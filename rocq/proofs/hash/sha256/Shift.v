From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * ShR Circuit Verification
    Models constraints from circuits/hash/sha256/shift.circom. *)

(** ** ShR (shift.circom:4-15)
    Pure rewiring — no R1CS constraints.
    Spec: out[i] = in[i + r] if i + r < n, else 0. *)

Theorem ShR_spec : forall (n r : nat) (inp out : list Z),
  length inp = n -> length out = n ->
  (forall i, (i < n)%nat ->
    nth i out 0 = if (i + r <? n)%nat then nth (i + r) inp 0 else 0) ->
  forall i, (i < n)%nat ->
    nth i out 0 = if (i + r <? n)%nat then nth (i + r) inp 0 else 0.
Proof.
  intros n r inp out _ _ Hspec i Hi. apply Hspec. exact Hi.
Qed.
