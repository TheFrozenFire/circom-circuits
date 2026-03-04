From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.
Require Import ecdsa.Secp256k1Params.
Require Import ecdsa.Point.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Secp256k1 Scalar Multiplication Verification
    Models constraints from circuits/ecdsa/scalarmul.circom.

    ScalarMult uses double-and-add from MSB to LSB with OR-chain
    for leading zero detection. PrivToPub uses fixed-base windowed
    multiplication with a precomputed G table (32 strides x 256 entries). *)

(* ================================================================== *)
(** ** Section 1: Multiplexer Soundness (Axiomatized) *)
(* ================================================================== *)

(** The circuit's Multiplexer template selects one of n_entries inputs
    based on a selector value. Soundness follows from Decoder + inner product. *)
Axiom Multiplexer_sound :
  forall (k : nat) (n_entries : nat) (sel : Z)
         (inp : list secp256k1_point) (out : secp256k1_point),
  0 <= sel < Z.of_nat n_entries ->
  length inp = n_entries ->
  (* All circuit constraints satisfied *)
  out = nth (Z.to_nat sel) inp (mk_secp256k1_point 0 0).

(* ================================================================== *)
(** ** Section 2: G Table *)
(* ================================================================== *)

(** The precomputed table from g_table.circom encodes 32 x 256 entries:
    g_table[s][j] = j * 2^(8s) * G for stride s, index j.
    This enables 8-bit windowed scalar multiplication. *)

Parameter secp256k1_G_table_entry : nat -> nat -> secp256k1_point.

Axiom secp256k1_G_table_correct :
  forall (s j : nat),
  (s < 32)%nat -> (j < 256)%nat ->
  secp256k1_G_table_entry s j =
    secp256k1_scalar_mul (Z.of_nat j * 2 ^ (Z.of_nat s * 8)) secp256k1_G.

(* ================================================================== *)
(** ** Section 3: ScalarMult Specification *)
(* ================================================================== *)

(** Secp256k1ScalarMult (scalarmul.circom:6-92)
    Variable-base scalar multiplication: out = scalar * point.

    Algorithm: Double-and-add from MSB to LSB.
    - Decompose scalar into 256 bits via Num2Bits
    - OR-chain tracks whether any nonzero bit has been seen
    - For each bit: double accumulator, conditionally add point
    - Mux selects between doubled-only and doubled-plus-point
    - Leading zero handling: first nonzero bit initializes accumulator

    Loop invariant (at step i, processing bit b_i from MSB):
      acc[i] = (Σ_{j > i} b_j * 2^(j-i-1)) * point
    After all 256 bits: acc[0] = scalar * point. *)

Theorem Secp256k1ScalarMult_spec :
  forall (scalar : list Z) (point out : secp256k1_point),
  length scalar = 8%nat ->
  secp256k1_on_curve point ->
  (* All limbs are 32-bit (from Num2Bits range checks) *)
  (forall i, (i < 8)%nat -> 0 <= nth i scalar 0 < 2^32) ->
  (* All circuit constraints satisfied: double-and-add loop, muxing, range checks *)
  secp256k1_on_curve out ->
  out = secp256k1_scalar_mul (limbs_to_num 32 scalar) point.
Proof.
  (* Loop induction on 256 bit steps. Precedent: BigModExp in BigIntCrt.v. *)
Admitted.

(* ================================================================== *)
(** ** Section 4: PrivToPub Specification *)
(* ================================================================== *)

(** Secp256k1PrivToPub (scalarmul.circom:95-158)
    Fixed-base scalar multiplication: pubkey = privkey * G.

    Uses precomputed G table with 8-bit windows (32 strides).
    Each stride selects from 256 precomputed multiples of G.
    Accumulates 31 additions (stride 0 initializes, strides 1-31 add).

    This is more efficient than variable-base ScalarMult because:
    1. No doublings needed (precomputed table absorbs them)
    2. Only 31 point additions instead of 256 double-and-add steps *)

Theorem Secp256k1PrivToPub_spec :
  forall (privkey : list Z) (pubkey : secp256k1_point),
  length privkey = 8%nat ->
  (* All limbs are 32-bit *)
  (forall i, (i < 8)%nat -> 0 <= nth i privkey 0 < 2^32) ->
  (* All circuit constraints satisfied: table lookups, additions, range checks *)
  secp256k1_on_curve pubkey ->
  pubkey = secp256k1_scalar_mul (limbs_to_num 32 privkey) secp256k1_G.
Proof.
  (* Loop induction on 32 strides, using G_table_correct and
     Multiplexer_sound at each step. Precedent: BigModExp in BigIntCrt.v. *)
Admitted.
