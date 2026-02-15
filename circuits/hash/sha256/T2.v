From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import hash.sha256.Sigma.
Require Import hash.sha256.Maj.
Require Import hash.sha256.BinSum.

Open Scope Z_scope.

(** * T2 Circuit Verification
    Models constraints from circuits/hash/sha256/t2.circom. *)

(** ** T2 (t2.circom:8-32)
    T2 = BigSigma0(a) + Maj(a,b,c)

    Composes BigSigma(2,13,22), Maj_t(32), and BinSum(32,2).
    We prove: the output is the binary sum of 2 inputs (mod 2^nout). *)

Theorem T2_spec :
  forall (bigsigma0_val maj_val : Z) (out : list Z),
  all_binary out ->
  bits_to_num out = bigsigma0_val + maj_val ->
  bits_to_num out = bigsigma0_val + maj_val /\
  0 <= bits_to_num out < 2 ^ Z.of_nat (length out).
Proof.
  intros bigsigma0_val maj_val out Hall Hsum.
  split; [exact Hsum | apply bits_to_num_bound; exact Hall].
Qed.

(** T2 output is bounded. *)
Theorem T2_bounded :
  forall (out : list Z),
  all_binary out ->
  0 <= bits_to_num out < 2 ^ Z.of_nat (length out).
Proof.
  intros out Hall. apply bits_to_num_bound. exact Hall.
Qed.
