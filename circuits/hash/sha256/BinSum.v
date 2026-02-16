From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import WitnessLemmas.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * BinSum Circuit Verification
    Models constraints from circuits/hash/sha256/binsum.circom. *)

(** ** BinSum (binsum.circom:16-41)
    Constraints:
      out[k] * (out[k] - 1) = 0   for k = 0..nout-1
      Σ_j Σ_k in[j][k] * 2^k = Σ_k out[k] * 2^k

    This is structurally a Num2Bits decomposition of the sum of inputs.
    We model it as: given binary output bits whose value equals the sum
    of input values, the output represents the binary sum. *)

Theorem BinSum_correct : forall (out : list Z) (input_sum : Z),
  (forall i, (i < length out)%nat ->
    nth i out 0 * (nth i out 0 - 1) = 0) ->
  input_sum = bits_to_num out ->
  all_binary out /\ 0 <= input_sum < 2 ^ Z.of_nat (length out)
  /\ input_sum = bits_to_num out.
Proof.
  intros out input_sum Hbin Hsum.
  assert (Hall := binary_constraints_imply_all_binary out Hbin).
  split; [exact Hall |].
  split.
  - rewrite Hsum. apply bits_to_num_bound. exact Hall.
  - exact Hsum.
Qed.

(** ** BinSum Completeness
    The witness `out[k] <-- (lin >> k) & 1` where lin is the sum of inputs.
    Structurally identical to Num2BitsLE — uses num2bits_witness. *)

Theorem BinSum_complete : forall (nout : nat) (input_sum : Z),
  0 <= input_sum < 2 ^ Z.of_nat nout ->
  let out := num2bits_witness input_sum nout in
  (forall i, (i < nout)%nat -> nth i out 0 * (nth i out 0 - 1) = 0) /\
  input_sum = bits_to_num out /\
  length out = nout.
Proof.
  intros nout input_sum Hrange out. subst out.
  split; [| split].
  - intros i Hi. apply num2bits_witness_binary_constraint; lia.
  - symmetry. apply bits_to_num_testbit. exact Hrange.
  - apply num2bits_witness_length.
Qed.
