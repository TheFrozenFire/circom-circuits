# Rocq Proof Style Guide

Conventions for the formal verification proofs (`*.v` files) in this repository.

## 1. Theorem Naming

| Suffix | Meaning | When to use |
|---|---|---|
| `_spec` | Constraint specification | Restating circom constraints as a useful Z property |
| `_correct` | Soundness / correctness | Constraints imply the intended mathematical property |
| `_complete` | Witness completeness | Valid inputs produce a witness satisfying all constraints mod p |
| `_sound` | Soundness (no false positives) | Constraints prevent invalid states (used for comparators, search) |
| `_binary` | Binary output | Proving a signal is 0 or 1 |
| `_field_safe` | Field safety | Values stay in [0, p_field) so Z proofs lift to F_p |
| `_bound` | Range bound | Value bounded by an expression |
| `_welldefined` | Well-definedness | Preconditions ensure denominators are nonzero, etc. |

**Guidelines:**
- `_spec` is the primary suffix for per-template soundness theorems
- `_correct` is used for simpler gate-level proofs (AND, OR, XOR, Ch, Maj) and auxiliary lemmas
- Use `_complete` exclusively for witness computation proofs
- A single template typically has `Template_spec` + `Template_complete` + optionally `Template_field_safe`

## 2. Hypothesis Naming

Use descriptive names that indicate what the hypothesis asserts. Never rely on auto-generated names (H0, H1, ...) which break when goal structure changes.

| Pattern | Convention | Examples |
|---|---|---|
| Binary | `Ha`, `Hb`, `Hc` | `Ha : is_binary a` |
| Field membership | `Hx_field`, `Hu_field` | `Hx_field : in_field x` |
| Inverse spec | `Hinv_x`, `Hinv_den` | `Hinv_x : (x * fp_inv x) mod p = 1` |
| Raw inverse | `Hinv_raw` | `Hinv_1my : ((1-y) * fp_inv omy) mod p = 1` |
| Nonzero | `Hnx`, `Hv_nz` | `Hnx : x <> 0`, `Hdx_nz : dx mod p <> 0` |
| Constraint | `Hout`, `Hmid` | Named after the signal being constrained |
| Length | `Hlen` | `Hlen : length bits = n` |
| All binary | `Hall`, `Hbin` | `Hall : all_binary bits` |
| Bound | `Hbound`, `Hrange` | `Hbound : 0 <= x < 2^n` |

**Exception:** Parameter-indexed names like `H0..H4` for `is_binary x0..x4` are acceptable in brute-force case splits (e.g., Ascon S-box proofs) where the indices match the variable names.

## 3. Proof Structure

### Soundness proofs (`_spec`, `_correct`)
```rocq
Theorem Template_spec : forall (signals : Z), ...
  (* constraint hypotheses *)
  constraint1 -> constraint2 ->
  (* conclusion: useful property *)
  property.
Proof.
  intros ... . subst ... . (* eliminate intermediate signals *)
  (* algebraic reasoning: lia, ring, or binary_cases *)
Qed.
```

### Completeness proofs (`_complete`)
```rocq
Theorem Template_complete : forall (inputs : Z),
  in_field input1 -> in_field input2 ->
  (* preconditions for well-definedness *)
  denominator mod p_field <> 0 ->
  exists (witnesses : Z),
    in_field w1 /\ in_field w2 /\
    (constraint1) mod p_field = 0 /\
    (constraint2) mod p_field = 0.
Proof.
  intros ... .
  (* 1. Define wrapped field values *)
  set (v := expr mod p_field).
  (* 2. Prove field membership *)
  assert (Hv_field : in_field v) by (unfold v; solve_in_field_modp).
  (* 3. Establish inverse properties *)
  assert (Hinv_v : (v * fp_inv v) mod p_field = 1) by (apply fp_inv_spec; ...).
  (* 4. Exhibit witnesses and prove constraints *)
  exists ... . split; [exact ... |]. ...
Qed.
```

## 4. Custom Tactics

Use the project's custom tactics instead of repeating boilerplate:

| Tactic | Purpose |
|---|---|
| `binary_cases` | Exhaustive case split on `is_binary` hypotheses (1-3 vars) |
| `solve_in_field_modp` | Prove `in_field (x mod p_field)` |
| `solve_mod_zero` | Reduce `(a - b) mod p = 0` to `a mod p = b mod p` |
| `solve_mod_self_zero` | Prove `(x - x) mod p = 0` or `(x mod p - x) mod p = 0` |
| `fp_inv_cancel Hinv` | Cancel `fp_inv` in mod-p equality using inverse hypothesis |
| `derive_raw_fp_inv Hinv` | Derive `(raw * fp_inv w) mod p = 1` from `(w * fp_inv w) mod p = 1` |

## 5. File Organization

Each `.v` file mirrors a `.circom` file and follows this structure:

```rocq
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
(* other imports *)

Require Import Primitives.
(* domain-specific imports *)

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Template Name Circuit Verification
    Models constraints from circuits/path/to/template.circom. *)

(** ** TemplateName (file.circom:line-range)
    Constraints:
      constraint1
      constraint2 *)

Theorem TemplateName_spec : ...

(** ** TemplateName Completeness ... *)

Theorem TemplateName_complete : ...
```

- Every file must have `Set Default Proof Using "Type"` for `.vos` compilation
- Document the circom source file and line range in comments above each theorem
- List the constraints being modeled in the doc comment
