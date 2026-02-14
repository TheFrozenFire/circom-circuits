From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Num2Bits Circuit Verification
    Models the constraints of Num2Bits(n) from circuits/packing/bitify.circom:33-44.

    Constraints:
      out[i] * (out[i] - 1) === 0    for each i in 0..n-1
      in === Σ out[i] * (1 << i)

    We prove: the constraints imply all outputs are binary, the input
    is in range [0, 2^n), and the decomposition is unique. *)

(** Num2Bits_correct: the constraints imply binary outputs and bounded input. *)
Theorem Num2Bits_correct : forall (out : list Z) (inp : Z),
  (forall i, (i < length out)%nat ->
    nth i out 0 * (nth i out 0 - 1) = 0) ->
  inp = bits_to_num out ->
  all_binary out /\ 0 <= inp < 2 ^ Z.of_nat (length out).
Proof.
  intros out inp Hbin Hsum.
  assert (Hall : all_binary out).
  {
    unfold all_binary. apply Forall_nth.
    intros i d Hi.
    rewrite nth_indep with (d' := 0) by exact Hi.
    apply binary_constraint. apply Hbin. exact Hi.
  }
  split.
  - exact Hall.
  - rewrite Hsum. apply bits_to_num_bound. exact Hall.
Qed.

(** Num2Bits_deterministic: the decomposition is unique — the circuit
    is not underconstrained. *)
Theorem Num2Bits_deterministic : forall (out1 out2 : list Z) (inp : Z),
  length out1 = length out2 ->
  (forall i, (i < length out1)%nat ->
    nth i out1 0 * (nth i out1 0 - 1) = 0) ->
  inp = bits_to_num out1 ->
  (forall i, (i < length out2)%nat ->
    nth i out2 0 * (nth i out2 0 - 1) = 0) ->
  inp = bits_to_num out2 ->
  out1 = out2.
Proof.
  intros out1 out2 inp Hlen Hbin1 Hsum1 Hbin2 Hsum2.
  assert (Hall1 : all_binary out1).
  {
    unfold all_binary. apply Forall_nth.
    intros i d Hi. rewrite nth_indep with (d' := 0) by exact Hi.
    apply binary_constraint. apply Hbin1. exact Hi.
  }
  assert (Hall2 : all_binary out2).
  {
    unfold all_binary. apply Forall_nth.
    intros i d Hi. rewrite nth_indep with (d' := 0) by exact Hi.
    apply binary_constraint. apply Hbin2. exact Hi.
  }
  apply bits_to_num_unique; try assumption.
  lia.
Qed.
