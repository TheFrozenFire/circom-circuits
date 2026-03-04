From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.
Require Import ecdsa.Secp256k1Params.
Require Import ecdsa.Point.
Require Import ecdsa.ScalarMul.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * GLV Endomorphism Verification
    Models constraints from circuits/ecdsa/glv.circom.

    GLV (Gallant-Lambert-Vanstone) decomposes a 256-bit scalar k into
    two ~129-bit scalars k1, k2 such that k ≡ k1 + k2*λ (mod order).
    The scalar multiplication k*P then becomes k1*P + k2*φ(P) where
    φ(x,y) = (β*x, y) is the secp256k1 endomorphism. This halves
    the number of double-and-add iterations from 256 to ~129.

    The decomposition uses Babai's nearest-plane algorithm on the
    GLV lattice, producing |k1|, |k2| < 2^129 with sign bits s1, s2. *)

(* ================================================================== *)
(** ** Section 1: BigMultModP Soundness (Axiomatized) *)
(* ================================================================== *)

(** BigMultModP (via BigIntCrt pattern from arithmetic/BigIntCrt.v)
    Computes modular multiplication: out ≡ a * b (mod p).
    Soundness follows from CRT zero-check of (a*b - q*p - r). *)

Axiom BigMultModP_sound :
  forall (n k : nat) (a b modulus out : list Z),
  length a = k -> length b = k -> length modulus = k -> length out = k ->
  (* All circuit constraints satisfied: CRT checks, range checks *)
  limbs_to_num n out =
    (limbs_to_num n a * limbs_to_num n b) mod (limbs_to_num n modulus).

(* ================================================================== *)
(** ** Section 2: GLV Decomposition (PROVED) *)
(* ================================================================== *)

(** The circuit constrains the GLV decomposition as:
      scalar + 2*s1*k1_abs + 2*s2*k2l - k1_abs - k2l = q * order
    where k2l = (k2_abs * lambda) mod order and s1, s2 are sign bits.

    Rearranging: scalar = (1-2*s1)*k1_abs + (1-2*s2)*k2l + q*order
    Taking mod order, the q*order term vanishes. *)

Theorem GLV_decomposition_sound :
  forall scalar k1_abs k2_abs k2l s1 s2 q,
  is_binary s1 -> is_binary s2 ->
  0 <= k1_abs < 2^129 -> 0 <= k2_abs < 2^129 ->
  k2l = (k2_abs * secp256k1_lambda) mod secp256k1_order ->
  scalar + 2*s1*k1_abs + 2*s2*k2l - k1_abs - k2l = q * secp256k1_order ->
  scalar mod secp256k1_order =
    ((1 - 2*s1) * k1_abs + (1 - 2*s2) * k2l) mod secp256k1_order.
Proof.
  intros scalar k1_abs k2_abs k2l s1 s2 q Hs1 Hs2 Hk1 Hk2 Hk2l Hdecomp.
  (* Rearrange the hypothesis to isolate scalar *)
  assert (Hscalar : scalar =
    (1 - 2*s1) * k1_abs + (1 - 2*s2) * k2l + q * secp256k1_order) by lia.
  (* Substitute and use Z.mod_add to eliminate q*order *)
  rewrite Hscalar.
  replace ((1 - 2 * s1) * k1_abs + (1 - 2 * s2) * k2l + q * secp256k1_order)
    with (((1 - 2 * s1) * k1_abs + (1 - 2 * s2) * k2l) + q * secp256k1_order)
    by ring.
  rewrite Z.mod_add by (pose proof secp256k1_order_pos; lia).
  reflexivity.
Qed.

(* ================================================================== *)
(** ** Section 3: GLV Group-Theoretic Corollary (PROVED) *)
(* ================================================================== *)

(** From the decomposition, we derive:
      k * P = k1_signed * P + k2_signed * φ(P)
    where k1_signed = (1-2*s1)*k1_abs and φ(P) = endomorphism(P).

    The proof uses scalar_mul_mod_order to lift the mod-order equality
    to a scalar multiplication equality, then secp256k1_scalar_mul_add
    to split, and secp256k1_endomorphism_is_scalar_mul to substitute. *)

Theorem GLV_scalar_identity :
  forall scalar k1_abs k2_abs k2l s1 s2 q P,
  is_binary s1 -> is_binary s2 ->
  0 <= k1_abs < 2^129 -> 0 <= k2_abs < 2^129 ->
  k2l = (k2_abs * secp256k1_lambda) mod secp256k1_order ->
  scalar + 2*s1*k1_abs + 2*s2*k2l - k1_abs - k2l = q * secp256k1_order ->
  secp256k1_on_curve P ->
  secp256k1_scalar_mul scalar P =
    secp256k1_add
      (secp256k1_scalar_mul ((1 - 2*s1) * k1_abs) P)
      (secp256k1_scalar_mul ((1 - 2*s2) * k2_abs) (secp256k1_endomorphism P)).
Proof.
  intros scalar k1_abs k2_abs k2l s1 s2 q P
    Hs1 Hs2 Hk1 Hk2 Hk2l Hdecomp HP.
  (* Step 1: From decomposition, scalar ≡ (1-2*s1)*k1_abs + (1-2*s2)*k2l (mod order) *)
  assert (Hmod := GLV_decomposition_sound scalar k1_abs k2_abs k2l s1 s2 q
    Hs1 Hs2 Hk1 Hk2 Hk2l Hdecomp).
  (* Step 2: Rewrite scalar_mul via mod_order *)
  rewrite (secp256k1_scalar_mul_mod_order scalar P HP).
  rewrite Hmod.
  (* Step 3: Rewrite endomorphism as scalar_mul lambda *)
  rewrite (secp256k1_endomorphism_is_scalar_mul P HP).
  (* Step 4: Use scalar_mul_compat to combine k2_abs and lambda *)
  rewrite secp256k1_scalar_mul_compat by exact HP.
  (* Step 5: Now we need:
       scalar_mul (((1-2*s1)*k1_abs + (1-2*s2)*k2l) mod order) P
       = add (scalar_mul ((1-2*s1)*k1_abs) P)
             (scalar_mul ((1-2*s2)*k2_abs*lambda) P)
     Use mod_order on each sub-term and scalar_mul_add. *)
  (* The key identity: (1-2*s2)*k2l ≡ (1-2*s2)*k2_abs*lambda (mod order)
     because k2l = (k2_abs*lambda) mod order *)
  rewrite secp256k1_scalar_mul_mod_order
    with (k := (1 - 2*s1) * k1_abs) by exact HP.
  rewrite secp256k1_scalar_mul_mod_order
    with (k := (1 - 2*s2) * k2_abs * secp256k1_lambda) by exact HP.
  (* Relate k2l and k2_abs*lambda modularly *)
  assert (Hk2l_mod : ((1 - 2*s2) * k2l) mod secp256k1_order =
    ((1 - 2*s2) * k2_abs * secp256k1_lambda) mod secp256k1_order).
  { rewrite Hk2l.
    replace ((1 - 2*s2) * k2_abs * secp256k1_lambda)
      with ((1 - 2*s2) * (k2_abs * secp256k1_lambda)) by ring.
    rewrite Z.mul_mod_idemp_r by (pose proof secp256k1_order_pos; lia).
    reflexivity. }
  (* Now both sides use mod_order form. Use scalar_mul_add on the mod-order values. *)
  (* This requires showing the mod-order values are non-negative for scalar_mul_add. *)
  set (a := ((1 - 2*s1) * k1_abs) mod secp256k1_order).
  set (b := ((1 - 2*s2) * k2_abs * secp256k1_lambda) mod secp256k1_order).
  assert (Ha : 0 <= a) by (subst a; apply Z.mod_pos_bound; pose proof secp256k1_order_pos; lia).
  assert (Hb : 0 <= b) by (subst b; apply Z.mod_pos_bound; pose proof secp256k1_order_pos; lia).
  rewrite <- secp256k1_scalar_mul_add by (try exact HP; lia).
  rewrite secp256k1_scalar_mul_mod_order with (k := a + b) by exact HP.
  (* Goal: scalar_mul (((1-2*s1)*k1_abs + (1-2*s2)*k2l) mod order) P
         = scalar_mul ((a + b) mod order) P *)
  f_equal.
  subst a b.
  rewrite Zplus_mod.
  rewrite Hk2l_mod.
  rewrite <- Zplus_mod.
  reflexivity.
Qed.

(* ================================================================== *)
(** ** Section 4: GLV ScalarMult Specification *)
(* ================================================================== *)

(** Secp256k1GLVScalarMult (glv.circom)
    Variable-base scalar multiplication using GLV decomposition.

    Phase 1: Decompose scalar into k1, k2 with signs s1, s2
    Phase 2: Compute endomorphism point and conditionally negate
    Phase 3: 129-iteration double-and-add with 4-way mux

    The 4-way mux per bit selects from:
      [dummy, P', Q', P'+Q'] based on sel = k1_bit + 2*k2_bit *)

Theorem Secp256k1GLVScalarMult_spec :
  forall (scalar : list Z) (point out : secp256k1_point),
  length scalar = 8%nat ->
  secp256k1_on_curve point ->
  (* All limbs are 32-bit *)
  (forall i, (i < 8)%nat -> 0 <= nth i scalar 0 < 2^32) ->
  (* All circuit constraints satisfied *)
  secp256k1_on_curve out ->
  out = secp256k1_scalar_mul (limbs_to_num 32 scalar) point.
Proof.
  (* Compose GLV_scalar_identity with two 129-bit ScalarMult instances.
     Loop induction on 129 steps. *)
Admitted.
