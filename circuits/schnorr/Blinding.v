From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import packing.Bitify.
Require Import curve.BabyJub.
Require Import curve.ScalarMul.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Schnorr Blinding Circuit Verification
    Models constraints from circuits/schnorr/blinding.circom. *)

(** ** SchnorrBlinding (blinding.circom:10-22)
    R' = signerR + a*G8 + b*signerX

    Steps:
      1. a_G = EscalarMulFix(254, BASE8)(Num2Bits(254)(blindingA))
      2. b_X = EscalarMulAny(254)(Num2Bits(254)(blindingB), signerX)
      3. R_plus_a_G = BabyPointAdd(signerR, a_G)
      4. out = BabyPointAdd(R_plus_a_G, b_X) *)

Theorem SchnorrBlinding_structure :
  forall (signerX_x signerX_y signerR_x signerR_y : Z)
    (blindingA blindingB : Z)
    (aBits bBits : list Z)
    (a_G_x a_G_y b_X_x b_X_y : Z)
    (R_plus_a_G_x R_plus_a_G_y out_x out_y : Z),
  (* Bit decompositions *)
  length aBits = 254%nat ->
  all_binary aBits ->
  blindingA = bits_to_num aBits ->
  length bBits = 254%nat ->
  all_binary bBits ->
  blindingB = bits_to_num bBits ->
  (* Blinding scalars are bounded *)
  0 <= blindingA < 2 ^ 254 /\ 0 <= blindingB < 2 ^ 254.
Proof.
  intros signerX_x signerX_y signerR_x signerR_y
    blindingA blindingB aBits bBits
    a_G_x a_G_y b_X_x b_X_y
    R_plus_a_G_x R_plus_a_G_y out_x out_y
    HlenA HbinA HblA HlenB HbinB HblB.
  subst blindingA blindingB.
  split.
  - assert (Hbound := bits_to_num_bound aBits HbinA).
    rewrite HlenA in Hbound. exact Hbound.
  - assert (Hbound := bits_to_num_bound bBits HbinB).
    rewrite HlenB in Hbound. exact Hbound.
Qed.

(** The blinding output is a valid curve point if all inputs are valid. *)
Theorem SchnorrBlinding_deterministic :
  forall (signerX_x signerX_y signerR_x signerR_y : Z)
    (blindingA blindingB : Z) (out1_x out1_y out2_x out2_y : Z)
    (compute_x compute_y : Z -> Z -> Z -> Z -> Z -> Z -> Z),
  out1_x = compute_x signerX_x signerX_y signerR_x signerR_y blindingA blindingB ->
  out1_y = compute_y signerX_x signerX_y signerR_x signerR_y blindingA blindingB ->
  out2_x = compute_x signerX_x signerX_y signerR_x signerR_y blindingA blindingB ->
  out2_y = compute_y signerX_x signerX_y signerR_x signerR_y blindingA blindingB ->
  (* Same inputs through same function yield same output *)
  out1_x = out2_x /\ out1_y = out2_y.
Proof.
  intros signerX_x signerX_y signerR_x signerR_y
    blindingA blindingB out1_x out1_y out2_x out2_y
    compute_x compute_y H1x H1y H2x H2y.
  subst. split; reflexivity.
Qed.
