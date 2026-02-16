From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import hash.sha256.Xor3.
Require Import hash.sha256.Rotate.
Require Import hash.sha256.Shift.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Sigma Circuit Verification
    Models constraints from circuits/hash/sha256/sigma.circom. *)

(** ** SmallSigma (sigma.circom:8-32)
    Composes RotR(ra), RotR(rb), ShR(rc), and Xor3.
    out[k] = xor3_bit(in[(k+ra)%32], in[(k+rb)%32], if k+rc<32 then in[k+rc] else 0)

    We prove: the output is the Xor3 of two rotations and one right shift. *)

Theorem SmallSigma_spec :
  forall (n ra rb rc : nat) (inp rota_out rotb_out shrc_out out : list Z),
  length inp = n -> length rota_out = n -> length rotb_out = n ->
  length shrc_out = n -> length out = n ->
  (* RotR wiring *)
  (forall k, (k < n)%nat -> nth k rota_out 0 = nth ((k + ra) mod n) inp 0) ->
  (forall k, (k < n)%nat -> nth k rotb_out 0 = nth ((k + rb) mod n) inp 0) ->
  (* ShR wiring *)
  (forall k, (k < n)%nat ->
    nth k shrc_out 0 = if (k + rc <? n)%nat then nth (k + rc) inp 0 else 0) ->
  (* Xor3 per-element correctness *)
  (forall k, (k < n)%nat ->
    is_binary (nth k rota_out 0) ->
    is_binary (nth k rotb_out 0) ->
    is_binary (nth k shrc_out 0) ->
    nth k out 0 = xor3_bit (nth k rota_out 0) (nth k rotb_out 0) (nth k shrc_out 0)) ->
  (* Conclusion: output matches composition *)
  forall k, (k < n)%nat ->
    is_binary (nth k rota_out 0) ->
    is_binary (nth k rotb_out 0) ->
    is_binary (nth k shrc_out 0) ->
    nth k out 0 = xor3_bit
      (nth ((k + ra) mod n) inp 0)
      (nth ((k + rb) mod n) inp 0)
      (if (k + rc <? n)%nat then nth (k + rc) inp 0 else 0).
Proof.
  intros n ra rb rc inp rota_out rotb_out shrc_out out
    Hinplen Hralen Hralen2 Hslen Holen
    Hrota Hrotb Hshrc Hxor3 k Hk HbinA HbinB HbinC.
  rewrite (Hxor3 k Hk HbinA HbinB HbinC).
  rewrite (Hrota k Hk). rewrite (Hrotb k Hk). rewrite (Hshrc k Hk).
  reflexivity.
Qed.

(** ** BigSigma (sigma.circom:35-58)
    Composes RotR(ra), RotR(rb), RotR(rc), and Xor3.
    out[k] = xor3_bit(in[(k+ra)%32], in[(k+rb)%32], in[(k+rc)%32]) *)

Theorem BigSigma_spec :
  forall (n ra rb rc : nat) (inp rota_out rotb_out rotc_out out : list Z),
  length inp = n -> length rota_out = n -> length rotb_out = n ->
  length rotc_out = n -> length out = n ->
  (forall k, (k < n)%nat -> nth k rota_out 0 = nth ((k + ra) mod n) inp 0) ->
  (forall k, (k < n)%nat -> nth k rotb_out 0 = nth ((k + rb) mod n) inp 0) ->
  (forall k, (k < n)%nat -> nth k rotc_out 0 = nth ((k + rc) mod n) inp 0) ->
  (forall k, (k < n)%nat ->
    is_binary (nth k rota_out 0) ->
    is_binary (nth k rotb_out 0) ->
    is_binary (nth k rotc_out 0) ->
    nth k out 0 = xor3_bit (nth k rota_out 0) (nth k rotb_out 0) (nth k rotc_out 0)) ->
  forall k, (k < n)%nat ->
    is_binary (nth k rota_out 0) ->
    is_binary (nth k rotb_out 0) ->
    is_binary (nth k rotc_out 0) ->
    nth k out 0 = xor3_bit
      (nth ((k + ra) mod n) inp 0)
      (nth ((k + rb) mod n) inp 0)
      (nth ((k + rc) mod n) inp 0).
Proof.
  intros n ra rb rc inp rota_out rotb_out rotc_out out
    Hinplen Hralen Hralen2 Hrclen Holen
    Hrota Hrotb Hrotc Hxor3 k Hk HbinA HbinB HbinC.
  rewrite (Hxor3 k Hk HbinA HbinB HbinC).
  rewrite (Hrota k Hk). rewrite (Hrotb k Hk). rewrite (Hrotc k Hk).
  reflexivity.
Qed.
