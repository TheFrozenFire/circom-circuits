From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Secp256k1 Curve Parameters and Group Law Axioms

    This module provides:
    1. Concrete curve constants matching circuits/ecdsa/constants.circom
    2. A point type and on-curve predicate (Weierstrass: y^2 = x^3 + 7)
    3. Opaque group operations as Parameters
    4. 11 axioms characterizing secp256k1 as an abelian group
    5. Connecting axioms linking abstract operations to polynomial constraints
    6. GLV endomorphism axiom
    7. Derived lemmas

    Unlike BabyJubjub (twisted Edwards, division-free multiplicative form),
    secp256k1 uses Weierstrass form where addition involves division by (x2-x1).
    The connecting axioms therefore take polynomial identity forms as hypotheses,
    matching the circuit's constraint checking approach. *)

(* ================================================================== *)
(** ** Section 1: Curve Constants *)
(* ================================================================== *)

(** Field prime: p = 2^256 - 2^32 - 977 *)
Definition secp256k1_p : Z :=
  115792089237316195423570985008687907853269984665640564039457584007908834671663.

(** 8 x 32-bit little-endian limbs matching constants.circom SECP256K1_PRIME *)
Definition secp256k1_p_limbs : list Z :=
  [4294966319; 4294967294; 4294967295; 4294967295;
   4294967295; 4294967295; 4294967295; 4294967295].

(** Curve group order *)
Definition secp256k1_order : Z :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337.

Definition secp256k1_order_limbs : list Z :=
  [3493216577; 3218235020; 2940772411; 3132021990;
   4294967294; 4294967295; 4294967295; 4294967295].

(** GLV eigenvalue: lambda^3 = 1 mod order *)
Definition secp256k1_lambda : Z :=
  37718080363155996902926221483475020450927657555482586988616620542887997980402.

(** GLV endomorphism constant: beta^3 = 1 mod p *)
Definition secp256k1_beta : Z :=
  55594575648329892869085402983802832744385952214688224221778511981742606582254.

Definition secp256k1_beta_limbs : list Z :=
  [1905590766; 3241765928; 318081429; 2632993141;
   2889102569; 1852065694; 1702627088; 2062117419].

(** Generator x-coordinate *)
Definition secp256k1_Gx : Z :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240.

(** Generator y-coordinate *)
Definition secp256k1_Gy : Z :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424.

(* ================================================================== *)
(** ** Section 2: Basic Properties *)
(* ================================================================== *)

Lemma secp256k1_p_pos : 0 < secp256k1_p.
Proof. unfold secp256k1_p. lia. Qed.

Lemma secp256k1_p_identity :
  secp256k1_p = 2^256 - 2^32 - 977.
Proof. unfold secp256k1_p. vm_compute. reflexivity. Qed.

Lemma secp256k1_p_lt_pow256 : secp256k1_p < 2^256.
Proof. unfold secp256k1_p. vm_compute. reflexivity. Qed.

Lemma secp256k1_p_limbs_val :
  limbs_to_num 32 secp256k1_p_limbs = secp256k1_p.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256k1_order_pos : 0 < secp256k1_order.
Proof. unfold secp256k1_order. lia. Qed.

Lemma secp256k1_order_limbs_val :
  limbs_to_num 32 secp256k1_order_limbs = secp256k1_order.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256k1_order_lt_p : secp256k1_order < secp256k1_p.
Proof. unfold secp256k1_order, secp256k1_p. lia. Qed.

Lemma secp256k1_order_lt_pow256 : secp256k1_order < 2^256.
Proof. unfold secp256k1_order. vm_compute. reflexivity. Qed.

Lemma secp256k1_beta_limbs_val :
  limbs_to_num 32 secp256k1_beta_limbs = secp256k1_beta.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** ** Section 3: Point Type and On-Curve Predicate *)
(* ================================================================== *)

Record secp256k1_point := mk_secp256k1_point {
  spx : Z;
  spy : Z
}.

(** The Weierstrass curve equation over F_p: y^2 ≡ x^3 + 7 (mod p) *)
Definition secp256k1_on_curve (P : secp256k1_point) : Prop :=
  (spy P * spy P) mod secp256k1_p =
    (spx P * spx P * spx P + 7) mod secp256k1_p.

(** The generator point *)
Definition secp256k1_G : secp256k1_point :=
  mk_secp256k1_point secp256k1_Gx secp256k1_Gy.

(** The generator lies on the curve. *)
Lemma secp256k1_G_on_curve : secp256k1_on_curve secp256k1_G.
Proof.
  unfold secp256k1_on_curve, secp256k1_G, secp256k1_Gx, secp256k1_Gy, secp256k1_p.
  simpl spx. simpl spy. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(** ** Section 4: Opaque Group Operations *)
(* ================================================================== *)

(** The point at infinity, modeled abstractly. *)
Parameter secp256k1_identity : secp256k1_point.

Parameter secp256k1_add : secp256k1_point -> secp256k1_point -> secp256k1_point.
Parameter secp256k1_neg : secp256k1_point -> secp256k1_point.
Parameter secp256k1_scalar_mul : Z -> secp256k1_point -> secp256k1_point.

(* ================================================================== *)
(** ** Section 5: Group Law Axioms (11 axioms, mirroring CurveParams.v) *)
(* ================================================================== *)

(** 1. Closure under addition *)
Axiom secp256k1_add_on_curve : forall P Q,
  secp256k1_on_curve P -> secp256k1_on_curve Q ->
  secp256k1_on_curve (secp256k1_add P Q).

(** 2. Associativity *)
Axiom secp256k1_add_assoc : forall P Q R,
  secp256k1_on_curve P -> secp256k1_on_curve Q -> secp256k1_on_curve R ->
  secp256k1_add (secp256k1_add P Q) R = secp256k1_add P (secp256k1_add Q R).

(** 3. Commutativity *)
Axiom secp256k1_add_comm : forall P Q,
  secp256k1_on_curve P -> secp256k1_on_curve Q ->
  secp256k1_add P Q = secp256k1_add Q P.

(** 4. Right identity *)
Axiom secp256k1_add_identity_r : forall P,
  secp256k1_on_curve P -> secp256k1_add P secp256k1_identity = P.

(** 5. Right inverse *)
Axiom secp256k1_add_inverse_r : forall P,
  secp256k1_on_curve P -> secp256k1_add P (secp256k1_neg P) = secp256k1_identity.

(** 6. Scalar multiplication compatibility *)
Axiom secp256k1_scalar_mul_compat : forall a b G,
  secp256k1_on_curve G ->
  secp256k1_scalar_mul a (secp256k1_scalar_mul b G) = secp256k1_scalar_mul (a * b) G.

(** 7. Negation preserves on-curve *)
Axiom secp256k1_neg_on_curve : forall P,
  secp256k1_on_curve P -> secp256k1_on_curve (secp256k1_neg P).

(** 8. Scalar multiplication preserves on-curve *)
Axiom secp256k1_scalar_mul_on_curve : forall k G,
  secp256k1_on_curve G -> secp256k1_on_curve (secp256k1_scalar_mul k G).

(** 9. Scalar multiplication by zero *)
Axiom secp256k1_scalar_mul_zero : forall G,
  secp256k1_on_curve G -> secp256k1_scalar_mul 0 G = secp256k1_identity.

(** 10. Scalar multiplication by one *)
Axiom secp256k1_scalar_mul_one : forall G,
  secp256k1_on_curve G -> secp256k1_scalar_mul 1 G = G.

(** 11. Scalar multiplication successor *)
Axiom secp256k1_scalar_mul_succ : forall n G,
  secp256k1_on_curve G -> 0 <= n ->
  secp256k1_scalar_mul (n + 1) G = secp256k1_add G (secp256k1_scalar_mul n G).

(** Identity is on the curve. *)
Axiom secp256k1_identity_on_curve : secp256k1_on_curve secp256k1_identity.

(* ================================================================== *)
(** ** Section 6: Connecting Axioms *)
(* ================================================================== *)

(** Addition of distinct points: the circuit verifies via polynomial constraints
    that the output satisfies the cubic identity (slope elimination) and the
    collinearity condition. These polynomial forms avoid division by (x2-x1). *)
Axiom secp256k1_add_formula : forall x1 y1 x2 y2 x3 y3,
  secp256k1_on_curve (mk_secp256k1_point x1 y1) ->
  secp256k1_on_curve (mk_secp256k1_point x2 y2) ->
  x1 mod secp256k1_p <> x2 mod secp256k1_p ->
  (* CubicConstraint: slope elimination polynomial ≡ 0 (mod p) *)
  (x1*x1*x1 + x2*x2*x2 - x1*x1*x2 - x1*x2*x2
   + x2*x2*x3 + x1*x1*x3 - 2*x1*x2*x3
   - y1*y1 + 2*y1*y2 - y2*y2) mod secp256k1_p = 0 ->
  (* PointOnLine: (x1,y1), (x2,y2), (x3,-y3) collinear *)
  (x3*y2 + x2*y3 + x2*y1 - x3*y1 - x1*y2 - x1*y3) mod secp256k1_p = 0 ->
  (* Output on curve *)
  secp256k1_on_curve (mk_secp256k1_point x3 y3) ->
  mk_secp256k1_point x3 y3 =
    secp256k1_add (mk_secp256k1_point x1 y1) (mk_secp256k1_point x2 y2).

(** Point doubling: the circuit verifies via tangent line and on-curve checks. *)
Axiom secp256k1_double_formula : forall x1 y1 x3 y3,
  secp256k1_on_curve (mk_secp256k1_point x1 y1) ->
  y1 mod secp256k1_p <> 0 ->
  (* PointOnTangent: tangent at (x1,y1) passes through (x3,-y3) *)
  (2*y1*y1 + 2*y1*y3 - 3*x1*x1*x1 + 3*x1*x1*x3) mod secp256k1_p = 0 ->
  (* Output on curve *)
  secp256k1_on_curve (mk_secp256k1_point x3 y3) ->
  mk_secp256k1_point x3 y3 =
    secp256k1_add (mk_secp256k1_point x1 y1) (mk_secp256k1_point x1 y1).

(* ================================================================== *)
(** ** Section 7: GLV Endomorphism *)
(* ================================================================== *)

(** The endomorphism phi(x, y) = (beta*x mod p, y) satisfies phi(P) = lambda*P. *)
Definition secp256k1_endomorphism (P : secp256k1_point) : secp256k1_point :=
  mk_secp256k1_point ((secp256k1_beta * spx P) mod secp256k1_p) (spy P).

Axiom secp256k1_endomorphism_is_scalar_mul : forall P,
  secp256k1_on_curve P ->
  secp256k1_endomorphism P = secp256k1_scalar_mul secp256k1_lambda P.

(** Scalar multiplication respects the group order. *)
Axiom secp256k1_scalar_mul_mod_order : forall k P,
  secp256k1_on_curve P ->
  secp256k1_scalar_mul k P = secp256k1_scalar_mul (k mod secp256k1_order) P.

(* ================================================================== *)
(** ** Section 8: Derived Lemmas *)
(* ================================================================== *)

(** Left identity from commutativity + right identity. *)
Lemma secp256k1_add_identity_l : forall P,
  secp256k1_on_curve P -> secp256k1_add secp256k1_identity P = P.
Proof.
  intros P HP.
  rewrite secp256k1_add_comm.
  - apply secp256k1_add_identity_r. exact HP.
  - exact secp256k1_identity_on_curve.
  - exact HP.
Qed.

(** Scalar multiplication distributes over addition in the scalar.
    Proof by strong induction on a, same pattern as CurveParams.v. *)
Lemma secp256k1_scalar_mul_add : forall a b G,
  secp256k1_on_curve G -> 0 <= a -> 0 <= b ->
  secp256k1_scalar_mul (a + b) G =
    secp256k1_add (secp256k1_scalar_mul a G) (secp256k1_scalar_mul b G).
Proof.
  intros a b G HG Ha.
  revert b. pattern a. apply natlike_ind.
  - intros b Hb.
    replace (0 + b) with b by lia.
    rewrite secp256k1_scalar_mul_zero by exact HG.
    rewrite secp256k1_add_identity_l
      by (apply secp256k1_scalar_mul_on_curve; exact HG).
    reflexivity.
  - intros n Hn IH b Hb.
    replace (Z.succ n + b) with ((n + b) + 1) by lia.
    rewrite secp256k1_scalar_mul_succ by (try exact HG; lia).
    rewrite IH by lia.
    replace (Z.succ n) with (n + 1) by lia.
    rewrite secp256k1_scalar_mul_succ by (try exact HG; lia).
    rewrite secp256k1_add_assoc.
    + reflexivity.
    + exact HG.
    + apply secp256k1_scalar_mul_on_curve. exact HG.
    + apply secp256k1_scalar_mul_on_curve. exact HG.
  - exact Ha.
Qed.
