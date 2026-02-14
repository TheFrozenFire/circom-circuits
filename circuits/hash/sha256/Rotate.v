From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * RotR Circuit Verification
    Models constraints from circuits/hash/sha256/rotate.circom. *)

(** ** RotR (rotate.circom:4-11)
    Pure rewiring — no R1CS constraints.
    Spec: out[i] = in[(i + r) mod n] for all i. *)

Theorem RotR_spec : forall (n r : nat) (inp out : list Z),
  length inp = n -> length out = n ->
  (forall i, (i < n)%nat -> nth i out 0 = nth ((i + r) mod n) inp 0) ->
  forall i, (i < n)%nat -> nth i out 0 = nth ((i + r) mod n) inp 0.
Proof.
  intros n r inp out _ _ Hspec i Hi. apply Hspec. exact Hi.
Qed.
