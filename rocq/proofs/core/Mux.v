From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.

Open Scope Z_scope.

(** * Multiplexer Circuit Verification
    Models constraints from circuits/core/mux.circom. *)

(** ** MultiMux1 (mux.circom:5-13)
    Constraints:
      out[i] = (c[i][1] - c[i][0]) * s + c[i][0]

    When s is binary, selects c[i][0] or c[i][1]. *)

Theorem MultiMux1_correct : forall c0 c1 s out : Z,
  is_binary s ->
  out = (c1 - c0) * s + c0 ->
  (s = 0 -> out = c0) /\ (s = 1 -> out = c1).
Proof.
  intros c0 c1 s out Hs Hout.
  destruct Hs as [Hs | Hs]; subst out; subst s; split; intro; lia.
Qed.
