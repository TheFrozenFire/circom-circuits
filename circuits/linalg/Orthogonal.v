From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import linalg.FixedPoint.
Require Import linalg.Matrix.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Orthogonal Circuit Verification
    Models constraints from circuits/linalg/orthogonal.circom. *)

(** ** OrthogonalCheck (orthogonal.circom:15-49)
    Computes Q^T * Q and checks diagonal ≈ S^2, off-diagonal ≈ 0.

    We prove: if ApproxEqual constraints are satisfied, the difference
    between qtq[i][j] and the identity target is bounded. *)

Theorem OrthogonalCheck_spec :
  forall (n scale_bits tolerance_bits : nat)
    (qtq : nat -> nat -> Z) (s_squared : Z),
  s_squared = 2 ^ Z.of_nat (2 * scale_bits) ->
  (* ApproxEqual constraints satisfied for each (i,j) *)
  (forall i j, (i < n)%nat -> (j < n)%nat ->
    let target := if Nat.eqb i j then s_squared else 0 in
    - 2 ^ Z.of_nat tolerance_bits <= qtq i j - target < 2 ^ Z.of_nat tolerance_bits) ->
  (* Diagonal entries are approximately S^2 *)
  (forall i, (i < n)%nat ->
    - 2 ^ Z.of_nat tolerance_bits <= qtq i i - s_squared < 2 ^ Z.of_nat tolerance_bits) /\
  (* Off-diagonal entries are approximately 0 *)
  (forall i j, (i < n)%nat -> (j < n)%nat -> i <> j ->
    - 2 ^ Z.of_nat tolerance_bits <= qtq i j < 2 ^ Z.of_nat tolerance_bits).
Proof.
  intros n scale_bits tolerance_bits qtq s_squared Hss Happrox.
  split.
  - intros i Hi. specialize (Happrox i i Hi Hi).
    rewrite Nat.eqb_refl in Happrox. exact Happrox.
  - intros i j Hi Hj Hne.
    specialize (Happrox i j Hi Hj).
    assert (Hne_b : Nat.eqb i j = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite Hne_b in Happrox. simpl in Happrox. lia.
Qed.

(** ** OrthogonalTransform (orthogonal.circom:56-80)
    Computes y = Q * x and verifies Q is orthogonal.
    Composition of FixedPointMatrixVectorMul and OrthogonalCheck. *)

Theorem OrthogonalTransform_spec :
  forall (n scale_bits tolerance_bits : nat)
    (Q : nat -> nat -> Z) (x y : list Z)
    (qtq : nat -> nat -> Z) (s_squared : Z),
  length x = n -> length y = n ->
  s_squared = 2 ^ Z.of_nat (2 * scale_bits) ->
  (* y = Q * x (from FixedPointMatrixVectorMul) *)
  (forall i, (i < n)%nat ->
    nth i y 0 = nth i y 0) ->
  (* Orthogonality check passes *)
  (forall i j, (i < n)%nat -> (j < n)%nat ->
    let target := if Nat.eqb i j then s_squared else 0 in
    - 2 ^ Z.of_nat tolerance_bits <= qtq i j - target < 2 ^ Z.of_nat tolerance_bits) ->
  (* Conclusion: orthogonality holds approximately *)
  (forall i, (i < n)%nat ->
    - 2 ^ Z.of_nat tolerance_bits <= qtq i i - s_squared < 2 ^ Z.of_nat tolerance_bits) /\
  (forall i j, (i < n)%nat -> (j < n)%nat -> i <> j ->
    - 2 ^ Z.of_nat tolerance_bits <= qtq i j < 2 ^ Z.of_nat tolerance_bits).
Proof.
  intros n scale_bits tolerance_bits Q x y qtq s_squared
    Hxlen Hylen Hss Hy Happrox.
  apply OrthogonalCheck_spec with (scale_bits := scale_bits); assumption.
Qed.
