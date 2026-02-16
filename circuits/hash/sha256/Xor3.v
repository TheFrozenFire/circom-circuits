From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Xor3 Circuit Verification
    Models constraints from circuits/hash/sha256/xor3.circom. *)

(** ** Xor3 (xor3.circom:5-16)
    Constraints (per element k):
      mid[k] = b[k] * c[k]
      out[k] = a[k] * (1 - 2*b[k] - 2*c[k] + 4*mid[k]) + b[k] + c[k] - 2*mid[k]

    Substituting mid = b*c:
      out = a*(1 - 2b - 2c + 4bc) + b + c - 2bc *)

Theorem Xor3_correct : forall a b c mid out : Z,
  is_binary a -> is_binary b -> is_binary c ->
  mid = b * c ->
  out = a * (1 - 2 * b - 2 * c + 4 * mid) + b + c - 2 * mid ->
  out = xor3_bit a b c /\ is_binary out.
Proof.
  intros a b c mid out Ha Hb Hc Hmid Hout. unfold xor3_bit, xor_bit; binary_cases.
Qed.
