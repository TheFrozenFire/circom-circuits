# Rocq Formal Verification

## Setup

### Native (macOS ARM)

```bash
brew install opam
opam init -y --bare
opam switch create rocq ocaml-base-compiler.4.14.2
eval $(opam env --switch=rocq)
opam install -y rocq-prover.9.0.0 coq-lsp.0.2.5+9.0 lwt logs
```

### MCP (rocq-mcp)

```bash
uv tool install git+https://github.com/llm4rocq/rocq-mcp.git
claude mcp add rocq-mcp -- env "PATH=$HOME/.opam/rocq/bin:$PATH" rocq-mcp
```

Provides `rocq_start_proof`, `rocq_run_tactic`, `rocq_get_goals`, `rocq_search`, `rocq_get_file_toc`, `rocq_get_premises`.

### Docker (alternative, amd64 only)

`rocq/Dockerfile` builds a Rocq 9.1 + pet-server image. No arm64 images exist for Rocq, so native opam is preferred on Apple Silicon.

### Compiling proofs

```bash
eval $(opam env --switch=rocq)
cd rocq/proofs
rocq compile Primitives.v && rocq compile Num2Bits.v && rocq compile Comparators.v
```

## Prior Art: Formal Land's Garden Framework

[Garden](https://github.com/formal-land/garden) is a framework for formally verifying zero-knowledge circuits. Their Circom backend is the most relevant reference for our work.

### Translation Pipeline

```
Circom source (.circom)
    → JSON AST (exported by modified Circom compiler)
    → rocq_of_circom.py (Python script)
    → Rocq .v files (free monad definitions)
    → Manual proofs
```

### Free Monad Design (`Garden/Circom/M.v`)

Circom templates become monadic programs in `M.t` with primitives:

| Primitive | Circom Concept |
|-----------|---------------|
| `DeclareVar` / `SubstituteVar` / `GetVarAccess` | Mutable variables |
| `DeclareSignal` | Signal declarations |
| `DeclareComponent` | Component instantiation |
| `EqualityConstraint` | `===` constraints |
| `OpenScope` / `CloseScope` | Variable scoping |
| `CallFunction` | Function calls |
| `GetPrime` | Field prime `p` |

Each template produces a signals record (mapping string names to `F.t` fields) and a `Definition` of type `M.t (BlockUnit.t Empty_set)`.

Example — Circom's XOR gate `out <== a + b - 2*a*b` becomes:

```coq
Definition XOR : M.t (BlockUnit.t Empty_set) :=
  M.template_body [] (
    do~ M.declare_signal "a" in
    do~ M.declare_signal "b" in
    do~ M.declare_signal "out" in
    do~ M.substitute_var "out" []
      [[ InfixOp.sub ~(| InfixOp.add ~(| M.var (| "a" |), M.var (| "b" |) |),
                         InfixOp.mul ~(| InfixOp.mul ~(| 2, M.var (| "a" |) |),
                                        M.var (| "b" |) |) |) ]]
    in M.pure BlockUnit.Tt
  ).
```

### The `Run` Relation

An 8-argument inductive relation extracts proof obligations:

```
{{ signals_naming, p, signals, scopes_in ⏩ e 🔽 output ⏩ scopes_out, P_prover, P_verifier }}
```

- `P_prover`: conditions from computation (witness generation)
- `P_verifier`: conditions from equality constraints (R1CS)

### Three Properties

1. **Determinism** — constraints uniquely determine the output (not underconstrained). Proved by showing `Run.t` yields a concrete output.
2. **Functional correctness** — output matches a reference specification.
3. **Completeness** — every valid input has a satisfying witness assignment.

### Current Maturity

- **Translated**: entire circomlib (~40 templates) including bitify, gates, comparators, babyjub, poseidon, sha256, SMT, etc.
- **Actually proved**: almost nothing on the Circom side. Only `nbits 6 = 3` (trivial function eval) and a partially admitted Xor3 proof. Their Plonky3 backend is far more mature (full Keccak round verification).
- **Takeaway**: the monad design and `Run` relation are well thought out, but the Circom proof infrastructure is too immature to reuse directly.

## Our Approach

We hand-model circuit semantics in Rocq rather than auto-translating from Circom. This is practical because:

1. We have a small number of templates to verify (PolyUHF, VectorCommit, HybridBridge)
2. The properties we care about are mathematical (Horner evaluation correctness, collision resistance bounds) rather than full circuit-level determinism proofs
3. Hand-modeling lets us work at the right abstraction level without the overhead of a full Circom-to-Rocq pipeline

### Proof Files

| File | Proves | Circuits |
|------|--------|----------|
| `Primitives.v` | Shared definitions (`is_binary`, `bits_to_num`, `all_binary`) and foundational lemmas (`binary_constraint`, `bits_to_num_bound`, `bits_to_num_unique`) | — |
| `Num2Bits.v` | Correctness and determinism of bit decomposition | `packing/bitify.circom` (Num2Bits) |
| `Comparators.v` | Soundness of IsZero, IsEqual, LessThan | `comparators.circom` |
| `Spike.v` | Horner evaluation properties (spike/demo) | — |

All proofs are complete — zero `Admitted` axioms.

### Compiling all proofs

```bash
eval $(opam env --switch=rocq)
cd rocq/proofs
rocq compile Primitives.v && rocq compile Num2Bits.v && rocq compile Comparators.v
```

`Num2Bits.v` and `Comparators.v` depend on `Primitives.v`, so compile order matters.

### Gotchas

- **`simpl` over-expands Z multiplication**: `simpl` on `2 * bits_to_num rest` produces a Z constructor match (`match bits_to_num rest with Z.pos y' => ... end`) that `lia` cannot solve. Fix: use `rewrite bits_to_num_cons` (or similar rewrite lemmas) instead of `simpl` when working with `bits_to_num`.
- **`nia` vs `Z.mul_eq_0`**: `nia` can fail on simple integral domain reasoning like `b * (b-1) = 0 → b = 0 ∨ b-1 = 0`. Use `apply Z.mul_eq_0 in H` followed by `lia` instead.
- **`at` is a keyword** in Rocq 9.0: avoid using `at` as a variable name in intro patterns (use `at_` or similar).
- **`From Coq` is deprecated**: use `From Stdlib` in Rocq 9.0+.
- `lia` requires `From Stdlib Require Import Lia.`.
