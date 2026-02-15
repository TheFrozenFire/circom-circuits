From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.

Open Scope Z_scope.

(** * BabyJubjub Curve Parameters and Group Law Axioms

    This module provides:
    1. Concrete curve constants matching circuits/curve/constants.circom
    2. A point type and on-curve predicate
    3. Opaque group operations (baby_add, baby_neg, scalar_mul) as Parameters
    4. 11 axioms characterizing BabyJubjub as an abelian group
    5. A connecting axiom linking the abstract baby_add to Edwards addition constraints
    6. Derived lemmas proved from the axioms

    The Edwards addition formula involves F_p division, which cannot be directly
    expressed in Z. Therefore the group operations are axiomatized rather than
    defined. These axioms are standard properties of twisted Edwards curves
    with the BabyJubjub parameters (a=168700, d=168696), verified in published
    literature but not machine-checked. *)

(** ** Curve Constants *)

Definition babyjub_a : Z := 168700.
Definition babyjub_d : Z := 168696.

Definition q_suborder : Z :=
  2736030358979909402780800718157159386076813972158567259200215660948447373041.

Definition base8_x : Z :=
  5299619240641551281634865583518297030282874472190772894086521144482721001553.

Definition base8_y : Z :=
  16950150798460657717958625567821834550301663161624707787222815936182638968203.

(** ** Suborder Properties *)

Lemma q_suborder_pos : 0 < q_suborder.
Proof. unfold q_suborder. lia. Qed.

Lemma q_suborder_lt_p : q_suborder < p_field.
Proof. unfold q_suborder, p_field. lia. Qed.

Lemma two_q_suborder_lt_p : 2 * q_suborder < p_field.
Proof. unfold q_suborder, p_field. lia. Qed.

Lemma q_suborder_gt_pow2_250 : 2 ^ 250 < q_suborder.
Proof. unfold q_suborder. vm_compute. reflexivity. Qed.

Lemma q_suborder_lt_pow2_251 : q_suborder < 2 ^ 251.
Proof. unfold q_suborder. vm_compute. reflexivity. Qed.

(** ** Suborder Bridging Lemmas *)

Definition in_suborder (x : Z) : Prop := 0 <= x < q_suborder.

Lemma Z_eq_iff_mod_q : forall a b,
  in_suborder a -> in_suborder b ->
  (a = b <-> a mod q_suborder = b mod q_suborder).
Proof.
  intros a b Ha Hb. split.
  - intro Heq. subst. reflexivity.
  - intro Hmod.
    assert (a mod q_suborder = a)
      by (apply Z.mod_small; unfold in_suborder in Ha; lia).
    assert (b mod q_suborder = b)
      by (apply Z.mod_small; unfold in_suborder in Hb; lia).
    lia.
Qed.

Lemma mod_q_add_exact : forall a b,
  in_suborder a -> in_suborder b -> a + b < q_suborder ->
  (a + b) mod q_suborder = a + b.
Proof.
  intros a b Ha Hb Hsum.
  apply Z.mod_small. unfold in_suborder in *. lia.
Qed.

Lemma pow2_lt_q_suborder : forall (n : nat),
  (n <= 250)%nat -> 2 ^ Z.of_nat n < q_suborder.
Proof.
  intros n Hn.
  assert (2 ^ Z.of_nat n <= 2 ^ 250).
  { apply Z.pow_le_mono_r; lia. }
  assert (2 ^ 250 < q_suborder) by exact q_suborder_gt_pow2_250.
  lia.
Qed.

Lemma in_suborder_of_bound : forall x (n : nat),
  0 <= x < 2 ^ Z.of_nat n -> (n <= 250)%nat -> in_suborder x.
Proof.
  intros x n Hx Hn. unfold in_suborder.
  assert (2 ^ Z.of_nat n < q_suborder) by (apply pow2_lt_q_suborder; exact Hn).
  lia.
Qed.

(** Suborder elements are also field elements. *)
Lemma in_suborder_in_field : forall x, in_suborder x -> in_field x.
Proof.
  intros x Hx. unfold in_field, in_suborder in *.
  assert (q_suborder < p_field) by exact q_suborder_lt_p. lia.
Qed.

(** ** Point Type and On-Curve Predicate *)

Record point := mkPoint { px : Z; py : Z }.

Definition identity : point := mkPoint 0 1.

(** The twisted Edwards curve equation over F_p: a*x^2 + y^2 ≡ 1 + d*x^2*y^2 (mod p) *)
Definition on_curve (P : point) : Prop :=
  (babyjub_a * (px P * px P) + (py P * py P)) mod p_field =
    (1 + babyjub_d * (px P * px P) * (py P * py P)) mod p_field.

(** ** Opaque Group Operations

    These are Parameters because the Edwards addition formula involves
    F_p division (by 1 +/- d*x1*y1*x2*y2), which cannot be expressed in Z.
    Their behavior is characterized by the axioms below. *)

Parameter baby_add : point -> point -> point.
Parameter baby_neg : point -> point.
Parameter scalar_mul : Z -> point -> point.

(** ** Group Law Axioms

    These 11 axioms state that (on_curve points, baby_add, identity)
    form an abelian group, with baby_neg as inversion and scalar_mul
    as repeated addition. *)

(** 1. Closure under addition *)
Axiom baby_add_on_curve : forall P Q : point,
  on_curve P -> on_curve Q -> on_curve (baby_add P Q).

(** 2. Associativity *)
Axiom baby_add_assoc : forall P Q R : point,
  on_curve P -> on_curve Q -> on_curve R ->
  baby_add (baby_add P Q) R = baby_add P (baby_add Q R).

(** 3. Commutativity *)
Axiom baby_add_comm : forall P Q : point,
  on_curve P -> on_curve Q ->
  baby_add P Q = baby_add Q P.

(** 4. Right identity *)
Axiom baby_add_identity_r : forall P : point,
  on_curve P -> baby_add P identity = P.

(** 5. Right inverse *)
Axiom baby_add_inverse_r : forall P : point,
  on_curve P -> baby_add P (baby_neg P) = identity.

(** 6. Scalar multiplication compatibility *)
Axiom scalar_mul_compat : forall (a b : Z) (G : point),
  on_curve G -> scalar_mul a (scalar_mul b G) = scalar_mul (a * b) G.

(** 7. Negation preserves on-curve *)
Axiom baby_neg_on_curve : forall P : point,
  on_curve P -> on_curve (baby_neg P).

(** 8. Scalar multiplication preserves on-curve *)
Axiom scalar_mul_on_curve : forall (k : Z) (G : point),
  on_curve G -> on_curve (scalar_mul k G).

(** 9. Scalar multiplication by zero *)
Axiom scalar_mul_zero : forall G : point,
  on_curve G -> scalar_mul 0 G = identity.

(** 10. Scalar multiplication by one *)
Axiom scalar_mul_one : forall G : point,
  on_curve G -> scalar_mul 1 G = G.

(** 11. Scalar multiplication successor *)
Axiom scalar_mul_succ : forall (n : Z) (G : point),
  on_curve G -> 0 <= n ->
  scalar_mul (n + 1) G = baby_add G (scalar_mul n G).

(** ** Connecting Axiom

    This links the abstract baby_add to the Edwards addition formula
    used in BabyAdd circuit constraints. Both sides of each equation
    are stated in multiplicative form (no division). *)

Axiom baby_add_formula : forall P Q : point,
  on_curve P -> on_curve Q ->
  let tau := px P * py Q * (py P * px Q) in
  (1 + babyjub_d * tau) * px (baby_add P Q) = px P * py Q + py P * px Q /\
  (1 - babyjub_d * tau) * py (baby_add P Q) =
    (-babyjub_a * px P + py P) * (px Q + py Q) +
      babyjub_a * (px P * py Q) - py P * px Q.

(** ** Derived Lemmas *)

(** The identity point is on the curve. *)
Lemma identity_on_curve : on_curve identity.
Proof. vm_compute. reflexivity. Qed.

(** Left identity from commutativity + right identity. *)
Lemma baby_add_identity_l : forall P : point,
  on_curve P -> baby_add identity P = P.
Proof.
  intros P HP.
  rewrite baby_add_comm.
  - apply baby_add_identity_r. exact HP.
  - exact identity_on_curve.
  - exact HP.
Qed.

(** Scalar multiplication distributes over addition in the scalar. *)
Lemma scalar_mul_add : forall (a b : Z) (G : point),
  on_curve G -> 0 <= a -> 0 <= b ->
  scalar_mul (a + b) G = baby_add (scalar_mul a G) (scalar_mul b G).
Proof.
  intros a b G HG Ha.
  revert b. pattern a. apply natlike_ind.
  - intros b Hb.
    replace (0 + b) with b by lia.
    rewrite scalar_mul_zero by exact HG.
    rewrite baby_add_identity_l by (apply scalar_mul_on_curve; exact HG).
    reflexivity.
  - intros n Hn IH b Hb.
    replace (Z.succ n + b) with ((n + b) + 1) by lia.
    rewrite scalar_mul_succ by (try exact HG; lia).
    rewrite IH by lia.
    replace (Z.succ n) with (n + 1) by lia.
    rewrite scalar_mul_succ by (try exact HG; lia).
    rewrite baby_add_assoc.
    + reflexivity.
    + exact HG.
    + apply scalar_mul_on_curve. exact HG.
    + apply scalar_mul_on_curve. exact HG.
  - exact Ha.
Qed.

(** The base point is on the curve. *)
Lemma base8_on_curve : on_curve (mkPoint base8_x base8_y).
Proof.
  vm_compute. reflexivity.
Qed.
