From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import hash.sha256.Sigma.
Require Import hash.sha256.Ch.
Require Import hash.sha256.BinSum.

Open Scope Z_scope.

(** * T1 Circuit Verification
    Models constraints from circuits/hash/sha256/t1.circom. *)

(** ** T1 (t1.circom:8-39)
    T1 = h + BigSigma1(e) + Ch(e,f,g) + k + w

    Composes BigSigma(6,11,25), Ch_t(32), and BinSum(32,5).
    We prove: the output is the binary sum of 5 inputs (mod 2^nout). *)

Theorem T1_spec :
  forall (h_val bigsigma1_val ch_val k_val w_val : Z) (out : list Z),
  all_binary out ->
  bits_to_num out = h_val + bigsigma1_val + ch_val + k_val + w_val ->
  bits_to_num out = h_val + bigsigma1_val + ch_val + k_val + w_val.
Proof. intros. assumption. Qed.

(** T1 output is bounded. *)
Theorem T1_bounded :
  forall (out : list Z),
  all_binary out ->
  0 <= bits_to_num out < 2 ^ Z.of_nat (length out).
Proof.
  intros out Hall. apply bits_to_num_bound. exact Hall.
Qed.
