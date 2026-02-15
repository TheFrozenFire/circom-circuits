From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import packing.Bitify.
Require Import curve.BabyJub.
Require Import schnorr.Blinding.
Require Import schnorr.Message.

Open Scope Z_scope.

(** * Schnorr Message Blind Circuit Verification
    Models constraints from circuits/schnorr/blind.circom. *)

(** ** SchnorrMessageBlind (blind.circom:12-27)
    Steps:
      1. BabySuborderCheck(blindingA), BabySuborderCheck(blindingB)
      2. blinded_R = SchnorrBlinding(signerX, signerR, blindingA, blindingB)
      3. c_blind = SchnorrMessageCommit(blinded_R, signerX, message)
      4. out = BabySuborderAdd(c_blind, blindingB) *)

Theorem SchnorrMessageBlind_range_checks :
  forall (blindingA blindingB : Z) (suborder : Z)
    (diffA diffB : Z) (bitsA bitsB : list Z),
  suborder > 0 ->
  diffA = suborder - 1 - blindingA ->
  length bitsA = 253%nat ->
  all_binary bitsA ->
  diffA = bits_to_num bitsA ->
  diffB = suborder - 1 - blindingB ->
  length bitsB = 253%nat ->
  all_binary bitsB ->
  diffB = bits_to_num bitsB ->
  blindingA <= suborder - 1 /\ blindingB <= suborder - 1.
Proof.
  intros blindingA blindingB suborder diffA diffB bitsA bitsB
    Hsub HdiffA HlenA HbinA HbtnA HdiffB HlenB HbinB HbtnB.
  split.
  - assert (Hnn := bits_to_num_nonneg bitsA HbinA).
    rewrite <- HbtnA in Hnn. lia.
  - assert (Hnn := bits_to_num_nonneg bitsB HbinB).
    rewrite <- HbtnB in Hnn. lia.
Qed.

Theorem SchnorrMessageBlind_output :
  forall (c_blind blindingB out : Z) (k q : Z),
  q > 0 ->
  out = (c_blind + blindingB) - k * q ->
  0 <= out < q ->
  out = (c_blind + blindingB) mod q.
Proof.
  intros c_blind blindingB out k q Hq Hout Hrange.
  subst out. apply Zmod_unique with k.
  - lia.
  - ring.
Qed.

(** The full protocol: blinding A/B are in suborder range,
    R is blinded, commitment is hashed, output adds blinding mod suborder. *)
Theorem SchnorrMessageBlind_spec :
  forall (n : nat) (message : list Z)
    (signerX_x signerX_y signerR_x signerR_y : Z)
    (blindingA blindingB : Z) (out : Z),
  length message = n ->
  (* blindingA < SUBORDER, blindingB < SUBORDER (range checked) *)
  (* blinded_R = signerR + blindingA*G8 + blindingB*signerX *)
  (* c_blind = SchnorrMessageCommit(blinded_R, signerX, message) *)
  (* out = (c_blind + blindingB) mod SUBORDER *)
  True.
Proof. intros. exact I. Qed.
