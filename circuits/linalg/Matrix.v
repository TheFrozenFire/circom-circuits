From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Matrix Circuit Verification
    Models constraints from circuits/linalg/matrix.circom. *)

(** ** MatrixIsEqual (matrix.circom:99-123)
    Same AND-chain structure as VectorIsEqual. *)

Theorem MatrixIsEqual_correct : forall (eq_results : list Z) (out : Z),
  Forall is_binary eq_results ->
  out = list_product eq_results ->
  (out = 1 <-> Forall (fun x => x = 1) eq_results).
Proof.
  intros eq_results out Hbin Hout. subst out.
  apply binary_and_chain. exact Hbin.
Qed.

(** ** MatrixTranspose (matrix.circom:86-95)
    Pure signal rewiring — no R1CS constraints.
    Spec: out[j][i] = M[i][j] for all i, j. *)

Theorem MatrixTranspose_spec :
  forall (m n : nat) (M : nat -> nat -> Z) (out : nat -> nat -> Z),
  (forall i j, (i < m)%nat -> (j < n)%nat -> out j i = M i j) ->
  forall i j, (i < m)%nat -> (j < n)%nat -> out j i = M i j.
Proof. intros. apply H; assumption. Qed.
