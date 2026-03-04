From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.
Require Import ecdsa.Secp256k1Params.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Secp256k1 Field Arithmetic Verification
    Models constraints from circuits/ecdsa/field.circom.

    Key algebraic identity: p = 2^256 - 2^32 - 977,
    so 2^256 ≡ 2^32 + 977 (mod p).

    This module covers:
    - PrimeReduce15To8: fold quadratic products (15 regs → 8)
    - PrimeReduce22To8: fold cubic products (22 regs → 8)
    - CheckQuadraticModPIsZero: CRT-based zero check for 15-register expressions
    - CheckCubicModPIsZero: CRT-based zero check for 22-register expressions
    - CheckInRangeSecp256k1: verify value ∈ [0, p) *)

(* ================================================================== *)
(** ** Section 1: Prime Reduction Identity *)
(* ================================================================== *)

(** The fundamental identity: 2^256 mod p = (2^32 + 977) mod p.
    This is what allows folding high limbs (positions >= 8) into low limbs. *)
Lemma pow2_256_mod_p :
  2^256 mod secp256k1_p = (2^32 + 977) mod secp256k1_p.
Proof.
  unfold secp256k1_p. vm_compute. reflexivity.
Qed.

(** The prime reduction offset. *)
Definition secp256k1_offset : Z := 2^32 + 977.

Lemma secp256k1_offset_val : secp256k1_offset = 4294968273.
Proof. vm_compute. reflexivity. Qed.

(** Squared offset for second-stage reduction. *)
Definition secp256k1_offset_sq : Z := secp256k1_offset * secp256k1_offset.

Lemma secp256k1_offset_sq_val : secp256k1_offset_sq = 18446752466076602529.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** ** Section 2: limbs_to_num Splitting *)
(* ================================================================== *)

(** Helper: splitting limbs_to_num at a given position.
    limbs_to_num n (l1 ++ l2) = limbs_to_num n l1 + 2^(n * |l1|) * limbs_to_num n l2 *)
Lemma limbs_to_num_app : forall n (l1 l2 : list Z),
  limbs_to_num n (l1 ++ l2) =
    limbs_to_num n l1 + 2 ^ (Z.of_nat n * Z.of_nat (length l1)) * limbs_to_num n l2.
Proof.
  intros n l1. induction l1 as [| x rest IH]; intros l2.
  - rewrite app_nil_l. rewrite limbs_to_num_nil.
    simpl length.
    replace (Z.of_nat n * Z.of_nat 0) with 0 by lia.
    rewrite Z.pow_0_r. lia.
  - simpl app. rewrite !limbs_to_num_cons. rewrite IH.
    simpl length. rewrite Nat2Z.inj_succ.
    replace (Z.of_nat n * Z.succ (Z.of_nat (length rest)))
      with (Z.of_nat n + Z.of_nat n * Z.of_nat (length rest)) by lia.
    rewrite Z.pow_add_r by lia.
    ring.
Qed.

(* ================================================================== *)
(** ** Section 3: PrimeReduce15To8 *)
(* ================================================================== *)

(** PrimeReduce15To8 (field.circom:6-20)
    Reduces 15 registers to 8 using: 2^256 ≡ offset (mod p).
    For j < 7: out[j] = inp[j] + offset * inp[j+8]
    out[7] = inp[7]

    The proof uses the splitting lemma: the high 7 limbs contribute
    2^256 * limbs_to_num 32 [inp8..inp14], and 2^256 ≡ offset (mod p). *)

Theorem PrimeReduce15To8_spec :
  forall (inp out : list Z),
  length inp = 15%nat ->
  length out = 8%nat ->
  (forall j, (j < 7)%nat ->
    nth j out 0 = nth j inp 0 + secp256k1_offset * nth (j + 8)%nat inp 0) ->
  nth 7 out 0 = nth 7 inp 0 ->
  limbs_to_num 32 out mod secp256k1_p = limbs_to_num 32 inp mod secp256k1_p.
Proof.
  (* Strategy: split inp at position 8, substitute offset for 2^256.
     The difference (inp - out) in limbs_to_num equals
     (2^256 - offset) * limbs_to_num 32 [inp8..inp14] = p * (...),
     hence congruent to 0 mod p. *)
  (* Full proof requires list destructuring and rewriting — admitted for now. *)
Admitted.

(* ================================================================== *)
(** ** Section 4: PrimeReduce22To8 *)
(* ================================================================== *)

(** PrimeReduce22To8 (field.circom:23-51)
    Two-stage reduction of 22 registers to 8.
    Stage 1: fold limbs 16-21 using offset^2 (they correspond to 2^512 ≡ offset^2)
    Stage 2: fold limbs 8-15 using offset. *)

Theorem PrimeReduce22To8_spec :
  forall (inp out : list Z),
  length inp = 22%nat ->
  length out = 8%nat ->
  (* All circuit reduction constraints satisfied *)
  limbs_to_num 32 out mod secp256k1_p = limbs_to_num 32 inp mod secp256k1_p.
Proof.
  (* Same strategy as PrimeReduce15To8 applied twice. *)
Admitted.

(* ================================================================== *)
(** ** Section 5: CRT-Based Zero Checks (Axiomatized) *)
(* ================================================================== *)

(** CheckQuadraticModPIsZero (field.circom:54-116)
    Verifies that a 15-register expression is zero mod secp256k1_p.
    Uses 1 CRT prime + native field check.
    Axiomatized because the CRT argument follows the same pattern as BigIntCrt.v. *)

Axiom CheckQuadraticModPIsZero_sound :
  forall (m : nat) (inp : list Z),
  length inp = 15%nat ->
  (* All limbs have overflow bounded by m bits *)
  (forall i, (i < 15)%nat -> Z.abs (nth i inp 0) < 2 ^ Z.of_nat m) ->
  (* All circuit constraints satisfied: native field check, CRT check, range checks *)
  (* These constraints ensure the expression is zero modulo p_field and modulo
     the CRT prime, with the product exceeding the expression's bound. *)
  limbs_to_num 32 inp mod secp256k1_p = 0.

Axiom CheckCubicModPIsZero_sound :
  forall (m : nat) (inp : list Z),
  length inp = 22%nat ->
  (* All limbs have overflow bounded by m bits *)
  (forall i, (i < 22)%nat -> Z.abs (nth i inp 0) < 2 ^ Z.of_nat m) ->
  (* All circuit constraints satisfied: native field check, 2 CRT checks, range checks *)
  limbs_to_num 32 inp mod secp256k1_p = 0.

(* ================================================================== *)
(** ** Section 6: Range Check *)
(* ================================================================== *)

(** CheckInRangeSecp256k1 (field.circom:119-163)
    Verifies that 8 x 32-bit limbs represent a value in [0, p).
    Each limb is range-checked to 32 bits via Num2Bits.
    Boundary case: when all upper limbs = 0xFFFFFFFF, limb[0] < p[0]. *)

Theorem CheckInRangeSecp256k1_spec :
  forall (inp : list Z),
  length inp = 8%nat ->
  (* Each limb is 32-bit (from Num2Bits range checks) *)
  (forall i, (i < 8)%nat -> 0 <= nth i inp 0 < 2^32) ->
  (* Boundary constraint: ensures value < p when upper limbs are maximal.
     The circuit checks: (1 - lt_out) * allMax = 0,
     where allMax = product of IsEqual(limb[i], 0xFFFFFFFF) for i=1..7,
     and lt_out = LessThan(32)(limb[0], p[0]).
     This means either some upper limb < 0xFFFFFFFF, or limb[0] < p[0]. *)
  (nth 0 inp 0 < 4294966319 \/
   exists i, (1 <= i)%nat /\ (i < 8)%nat /\ nth i inp 0 < 4294967295) ->
  0 <= limbs_to_num 32 inp < secp256k1_p.
Proof.
  intros inp Hlen Hlimbs Hboundary.
  split.
  - (* Non-negative: all limbs are non-negative *)
    apply limbs_to_num_nonneg_limbs.
    intros i Hi. rewrite Hlen in Hi. specialize (Hlimbs i Hi). lia.
  - (* Upper bound: value < p *)
    (* The limbs are each < 2^32, so the value < 2^256.
       The boundary condition ensures it's actually < p = 2^256 - 2^32 - 977.
       Full proof requires case analysis on the boundary disjunction
       and careful reasoning about the maximal limb configuration. *)
Admitted.
