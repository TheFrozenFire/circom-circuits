From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.

Open Scope Z_scope.

(** * Maj Circuit Verification
    Models constraints from circuits/hash/sha256/maj.circom. *)

(** ** Maj_t (maj.circom:5-16)
    Constraints (per element k):
      mid[k] = b[k] * c[k]
      out[k] = a[k] * (b[k] + c[k] - 2 * mid[k]) + mid[k]

    Substituting mid = b*c:
      out = a*(b + c - 2bc) + bc *)

Theorem Maj_correct : forall a b c mid out : Z,
  is_binary a -> is_binary b -> is_binary c ->
  mid = b * c ->
  out = a * (b + c - 2 * mid) + mid ->
  out = maj_bit a b c /\ is_binary out.
Proof.
  intros a b c mid out Ha Hb Hc Hmid Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    destruct Hc as [Hc | Hc];
    subst; unfold maj_bit, is_binary; split; lia.
Qed.
