# Circom Style Guide

Target: **circom 2.2.2**. This guide captures idioms and patterns learned through practice — things that go beyond basic syntax reference.

## 1. Anonymous Component Syntax

The defining pattern of modern circom. Four levels of usage, each with clear "when to use" guidance.

### Level 1 — Constraint-only (no output captured)

For templates with **no output signals** (pure constraint templates):

```circom
BabyCheck()(point[0], point[1]);
BabySuborderCheck()(blindingA);
```

Use when a template's purpose is to **constrain**, not to produce a value. The anonymous call is a standalone statement — no assignment needed.

**Important:** This only works for templates with zero outputs. For templates that have outputs but you only want the side-effect constraints (e.g., `Num2Bits` for range checking), assign to a discarded signal:

```circom
signal _bits[n] <== Num2Bits(n)(r);  // range check, outputs not used downstream
```

### Level 2 — Inline single-output assignment

```circom
signal output out <== Poseidon(1)([ address ]);
signal hash <== HashLeftRight()(left, right);
signal lt <== LessThan(252)([out, BABYJUB_SUB_ORDER()]);
```

Default for any single-output component. Array literals `[a, b]` pass multiple inputs.

### Level 3 — Tuple destructuring

```circom
signal (x, y) <== BabyAdd()(in[0][0], in[0][1], in[1][0], in[1][1]);
signal output (c1[2], c2[2]) <== ElGamalEncrypt()(...);
```

Use for multi-output components when all outputs are needed.

### Level 4 — Chained anonymous components (pipeline)

```circom
// Two stages — inner result feeds directly as positional input
signal a_G[2] <== EscalarMulFix(254, BASE_8())(Num2Bits(254)(blindingA));

// Three-stage pipeline from ascon (buses chain naturally)
intermediate[0] <== Ascon_LinearDiffusion()(
    Ascon_Sbox()(
        Ascon_ConstantAddition(rnd, 0)(in)
    )
);
```

Use for short pipelines (2–3 stages max). Beyond 3 stages, break into named intermediaries for readability.

**Limitation:** Anonymous components cannot be nested inside array literals. If a template takes its input as an array (like `Poseidon(n)([a, b, ...])`), you cannot chain another anonymous component inside those brackets:

```circom
// WON'T COMPILE — anonymous component inside array literal
signal out <== Poseidon(1)([Poseidon(1)([x])]);

// DO THIS INSTEAD — name the intermediate
signal inner <== Poseidon(1)([x]);
signal out <== Poseidon(1)([inner]);
```

Chaining works when the inner result passes directly as positional arguments, not wrapped in array syntax.

### When to fall back to traditional `component` syntax

- When the same component is referenced multiple times (e.g., `shared.out` used in two places)
- When complex wiring requires loops over component inputs:
  ```circom
  // Loop-based wiring — anonymous syntax would be awkward here
  component dot[m];
  for (var i = 0; i < m; i++) {
      dot[i] = FixedPointDotProduct(n, scale_bits);
      for (var j = 0; j < n; j++) {
          dot[i].a[j] <== M[i][j];
          dot[i].b[j] <== v[j];
      }
      out[i] <== dot[i].out;
  }
  ```
- When a component has many inputs that can't be passed positionally in a readable way

## 2. Template Design Patterns

### One-liner templates

For trivial domain wrappers — a single signal assignment with one anonymous component:

```circom
template AddressLeaf() { signal input address; signal output out <== Poseidon(1)([ address ]); }
```

Only use one-liners when the body fits on one line without sacrificing readability.

### Wrapper templates

Normalize external library interfaces to consistent `in`/`out` array patterns:

```circom
template BabyPointAdd() {
    signal input in[2][2];
    signal (x, y) <== BabyAdd()(in[0][0], in[0][1], in[1][0], in[1][1]);
    signal output out[2];
    out[0] <== x;
    out[1] <== y;
}
```

Wrapping circomlib components gives them consistent array interfaces instead of named fields like `x1, y1, x2, y2`.

### Constants as functions

```circom
function BASE_8() { return [...]; }
function BABYJUB_SUB_ORDER() { return ...; }
function ASCON_INITIAL_STATE_HASH_256() {
    return [
        word_2_bits(0x9b1e5494e934d681),
        word_2_bits(0x4bc3a01e333751d2),
        ...
    ];
}
```

Place in `constants.circom` within each module directory. Constants are SCREAMING_SNAKE_CASE functions because circom has no `const` keyword.

## 3. Bus Types and Signal Annotations

### Buses

Use when a group of signals represents a coherent domain concept appearing across multiple templates:

```circom
// ascon/types.circom
bus Ascon_State() {
    signal {binary} S0[64];
    signal {binary} S1[64];
    signal {binary} S2[64];
    signal {binary} S3[64];
    signal {binary} S4[64];
}

// Templates use bus types for inputs and outputs
template Ascon_Permutation(rnd) {
    input Ascon_State() in;
    output Ascon_State() out;
    ...
}
```

Do **NOT** use buses for ad-hoc groupings. A bus earns its existence by appearing in 3+ template signatures. Bus definitions go in a `types.circom` file within the module.

Note the syntax difference: bus-typed ports use `input`/`output` (no `signal` keyword), while regular signals use `signal input`/`signal output`.

### Signal annotations

`{binary}` marks signals known to be 0 or 1:

```circom
signal {binary} column_in[64][5];
signal input {binary} x[5];
signal {binary} layer_i[64] <== ShiftRight(shifts[0])(in);
```

Apply at declaration. Annotations propagate through anonymous component assignments, so downstream signals inherit the annotation.

## 4. Constraint Organization

### Var accumulators

For unconstrained linear accumulation leading to a constrained output:

```circom
signal products[n];
var sum = 0;
for (var i = 0; i < n; i++) {
    products[i] <== a[i] * b[i];  // quadratic constraint per element
    sum += products[i];            // linear accumulation (no constraint)
}
out <== sum;                       // one linear constraint tying it together
```

The `products[i]` signals are each constrained by a quadratic equation. The `var sum` accumulates linearly without adding constraints, then `out <== sum` creates a single linear constraint. This pattern avoids intermediate signal overhead for the accumulator.

**From the codebase:** `DotProduct`, `VectorNormSquared`, `MatrixVectorMul`, `MatrixMul`, and `FixedPointDotProduct` all use this pattern.

### Witness-then-constrain

For non-algebraic operations (division, modular reduction) that can't be expressed as R1CS constraints directly:

```circom
// Prover computes the witness (unconstrained)
signal q;
signal r;
q <-- rawDot >> scale_bits;
r <-- rawDot % (1 << scale_bits);

// Verifier checks the relationship (constrained)
rawDot === q * (1 << scale_bits) + r;

// Range check to ensure uniqueness of the decomposition
component rangeCheck = Num2Bits(scale_bits);
rangeCheck.in <== r;
```

Always pair `<--` witness assignments with `===` constraints and range checks. A witness without a constraint is a soundness bug.

### Range checks via Num2Bits

```circom
signal _bits[scale_bits] <== Num2Bits(scale_bits)(r);  // constrains 0 <= r < 2^scale_bits
```

The bit decomposition forces the value into range. Assign to a discarded signal prefixed with `_` when you don't need the bits downstream.

### Compile-time assertions

For parameter validation — these run at compile time, not during proving:

```circom
assert(n <= 252);
assert(ma + mb <= 253);
```

## 5. File Organization

```
circuits/
    circomlib/              # Git submodule (iden3/circomlib)
    STYLE.md                # This style guide

    bitwise.circom          # Root-level foundational circuits

    <module>/               # Each domain gets a directory
        types.circom        # Bus definitions (if the module uses buses)
        constants.circom    # Constant functions
        functions.circom    # Pure helper functions (witness computation, bit manipulation)
        <templates>.circom  # Template files organized by concern
        main.circom         # Compilation entry point (if applicable)
```

**Example — ascon module:**
```
ascon/
    types.circom            # Ascon_State bus
    constants.circom        # ASCON_INITIAL_STATE_HASH_256, ASCON_ROUND_CONSTANT, ...
    functions.circom        # word_2_bits, byte_2_bits, ShiftRight
    sbox.circom             # Ascon_Sbox_y0 through y4
    permutations.circom     # Ascon_Permutation, Ascon_Sbox, Ascon_LinearDiffusion, ...
    hash.circom             # Ascon_Hash_256
    main.circom             # component main = ...
```

Not every module needs every file. A simple module may have just a single `.circom` file at the module directory level. Create `types.circom`, `constants.circom`, etc. only when the module is complex enough to warrant separation.

### Include paths

All relative to `circuits/` (the compilation root, passed via `-l`):

```circom
pragma circom 2.2.2;

include "circomlib/circuits/bitify.circom";    // external lib (submodule)
include "circomlib/circuits/comparators.circom";

include "linalg/vector.circom";                // sibling module
include "bitwise.circom";                      // root-level circuit

include "ascon/types.circom";                  // within own module
include "ascon/functions.circom";
```

Every file starts with `pragma circom 2.2.2;` followed by includes.

## 6. Naming Conventions

| Element | Convention | Examples |
|---------|-----------|----------|
| Templates | PascalCase | `BabyPointAdd`, `FixedPointMul`, `VectorAdd` |
| Module-prefixed templates | `Module_Template` | `Ascon_Permutation`, `Ascon_Sbox_y0` |
| Buses | `Module_Name()` | `Ascon_State()` |
| Signals | camelCase | `blindingA`, `signerX`, `rawDot` |
| Signal arrays | camelCase or short names | `products[n]`, `acc[n]`, `out[m]` |
| Template parameters | camelCase or single letter | `n`, `k`, `scale_bits`, `nLevels` |
| Functions (constants) | SCREAMING_SNAKE_CASE | `BASE_8()`, `BABYJUB_SUB_ORDER()` |
| Functions (computation) | snake_case | `word_2_bits`, `long_div`, `mod_inv` |
| Files | snake_case | `bigint_func.circom`, `compress_point.circom` |
| Directories | snake_case | `linalg/`, `ascon/` |

**Module prefixing:** Use `Module_` prefix when templates could collide across modules or when the template name alone is ambiguous. Within a single-file module (like `bitwise.circom`), no prefix is needed.

## 7. Documentation

### Minimal comments — rely on clear naming

```circom
// Good: the formula is the documentation
// A + B - 2AB
out <== (in[0] + in[1]) - (2 * in[0] * in[1]);
```

### Mathematical formulas in comments

When the constraint implements a non-obvious equation:

```circom
// 𝑦0 = 𝑥4𝑥1 ⊕ 𝑥3 ⊕ 𝑥2𝑥1 ⊕ 𝑥2 ⊕ 𝑥1𝑥0 ⊕ 𝑥1 ⊕ 𝑥0
template Ascon_Sbox_y0() {
```

### Triple-slash `///` doc comments

Use above templates when the behavior isn't obvious from the signature. Focus on constraint counts and the "why":

```circom
/// Squared L2 norm of a vector: sum(v_i^2). n constraints.
template VectorNormSquared(n) {

/// Fixed-point multiplication with rescaling.
/// Given a, b representing real values a/S, b/S where S = 2^scale_bits,
/// computes out = floor(a * b / S).
/// 1 constraint for the division check + scale_bits for remainder range check.
template FixedPointMul(scale_bits) {
```

### Algorithm/paper references as URLs

```circom
// https://eprint.iacr.org/2022/1676.pdf
```

### Packing layout docs

When bit-packing is involved, show offsets explicitly:

```circom
// Layout: [address (160 bits)][nonce (64 bits)][flags (32 bits)]
// Offsets:  0                   160              224
```

## 8. Pragma and File Structure

Every `.circom` file follows this order:

```circom
pragma circom 2.2.2;

// External includes
include "circomlib/circuits/...";

// Internal includes
include "module/...";

// Functions (if any)

// Templates (if any)

// component main (only in main.circom entry points)
```

## 9. Constraint Efficiency Considerations

### Linear operations are free in R1CS

Addition and subtraction create no constraints — only multiplication does. Document this when it's relevant:

```circom
/// Element-wise vector addition. Zero constraints (addition is free in R1CS).
template VectorAdd(n) {
```

### Prefer inlined computation over sub-components for simple operations

When a sub-component would add overhead without improving readability, inline the computation:

```circom
// Inlined dot product — clearer than a sub-component for a simple pattern
signal products[m][n];
for (var i = 0; i < m; i++) {
    var sum = 0;
    for (var j = 0; j < n; j++) {
        products[i][j] <== M[i][j] * v[j];
        sum += products[i][j];
    }
    out[i] <== sum;
}
```

### Use sub-components for complex reusable logic

```circom
// FixedPointDotProduct encapsulates witness computation + range check
// Worth the sub-component overhead because the pattern is non-trivial
component dot[m];
for (var i = 0; i < m; i++) {
    dot[i] = FixedPointDotProduct(n, scale_bits);
    ...
}
```

The threshold: if a pattern involves only `<==` constraints and var accumulation, inline it. If it involves `<--` witness computation, `===` manual constraints, or range checks, extract to a template.
