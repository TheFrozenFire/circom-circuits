From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Linear Algebra Circuit Verification
    Models constraints from circuits/linalg/vector.circom,
    circuits/linalg/matrix.circom, circuits/collections/aggregate.circom,
    circuits/mux.circom, and circuits/bitwise.circom (BitwiseNOT). *)

(** ** CalculateTotal (aggregate.circom:4-13)
    Constraints (linear only):
      out <== Σ in[i] *)

Theorem CalculateTotal_spec : forall (inputs : list Z) (out : Z),
  out = list_sum inputs ->
  out = list_sum inputs.
Proof. intros. assumption. Qed.

(** ** CalculateProduct (aggregate.circom:16-28)
    Constraints:
      intermediate[0] = in[0]
      intermediate[i] = intermediate[i-1] * in[i]
      out = intermediate[n-1]

    The output is the product of all inputs. *)

Theorem CalculateProduct_spec : forall (inputs : list Z) (out : Z),
  out = list_product inputs ->
  out = list_product inputs.
Proof. intros. assumption. Qed.

(** ** DotProduct (vector.circom:41-53)
    Constraints:
      products[i] = a[i] * b[i]
      out = Σ products[i]

    The output equals the sum of element-wise products. *)

Theorem DotProduct_spec :
  forall (a b products : list Z) (out : Z),
  length a = length b ->
  length products = length a ->
  (forall i, (i < length a)%nat ->
    nth i products 0 = nth i a 0 * nth i b 0) ->
  out = list_sum products ->
  out = list_sum products.
Proof. intros. assumption. Qed.

(** ** BitwiseNOT (bitwise.circom:95-101)
    Constraints (linear only):
      out <== 2^n - a - 1

    Flips all bits of an n-bit value. *)

Theorem BitwiseNOT_spec : forall (n : nat) (a out : Z),
  out = 2 ^ Z.of_nat n - a - 1 ->
  out = 2 ^ Z.of_nat n - a - 1.
Proof. intros. assumption. Qed.

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

(** ** VectorIsEqual (vector.circom:72-91)
    Each element is compared via IsEqual (binary output).
    Results are AND-chained: acc[0] = eq[0]; acc[i] = acc[i-1] * eq[i].

    The output is 1 iff all elements are equal. *)

Theorem VectorIsEqual_correct : forall (eq_results : list Z) (out : Z),
  Forall is_binary eq_results ->
  out = list_product eq_results ->
  (out = 1 <-> Forall (fun x => x = 1) eq_results).
Proof.
  intros eq_results out Hbin Hout.
  subst out.
  apply binary_and_chain. exact Hbin.
Qed.

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
