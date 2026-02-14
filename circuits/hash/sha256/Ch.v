From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.

Open Scope Z_scope.

(** * Ch Circuit Verification
    Models constraints from circuits/hash/sha256/ch.circom. *)

(** ** Ch_t (ch.circom:4-13)
    Constraints (per element k):
      out[k] = a[k] * (b[k] - c[k]) + c[k] *)

Theorem Ch_correct : forall a b c out : Z,
  is_binary a -> is_binary b -> is_binary c ->
  out = a * (b - c) + c ->
  out = ch_bit a b c /\ is_binary out.
Proof.
  intros a b c out Ha Hb Hc Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    destruct Hc as [Hc | Hc];
    subst; unfold ch_bit, is_binary; split; lia.
Qed.
