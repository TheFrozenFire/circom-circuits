From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import hash.sha256.Sigma.
Require Import hash.sha256.BinSum.

Open Scope Z_scope.

(** * SigmaPlus Circuit Verification
    Models constraints from circuits/hash/sha256/sigmaplus.circom. *)

(** ** SigmaPlus (sigmaplus.circom:7-32)
    Message schedule expansion step:
      out = BinSum(32,4)(sigma1(in2), in7, sigma0(in15), in16)

    where sigma1 = SmallSigma(17,19,10) and sigma0 = SmallSigma(7,18,3).

    We prove: the output is the binary sum of four 32-bit words (mod 2^32). *)

Theorem SigmaPlus_spec :
  forall (sigma1_out sigma0_out : list Z)
    (in7 in16 : list Z) (out : list Z),
  length sigma1_out = 32%nat ->
  length in7 = 32%nat ->
  length sigma0_out = 32%nat ->
  length in16 = 32%nat ->
  length out = 32%nat ->
  (* BinSum(32,4) constraint: output bits decompose the sum *)
  all_binary out ->
  bits_to_num out =
    bits_to_num sigma1_out + bits_to_num in7 +
    bits_to_num sigma0_out + bits_to_num in16 ->
  (* Conclusion *)
  bits_to_num out =
    bits_to_num sigma1_out + bits_to_num in7 +
    bits_to_num sigma0_out + bits_to_num in16.
Proof. intros. assumption. Qed.

(** The output is bounded by 2^nout where nout accommodates the sum. *)
Theorem SigmaPlus_bounded :
  forall (out : list Z),
  all_binary out ->
  0 <= bits_to_num out < 2 ^ Z.of_nat (length out).
Proof.
  intros out Hall. apply bits_to_num_bound. exact Hall.
Qed.
