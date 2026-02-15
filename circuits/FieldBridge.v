From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** * Field Bridge: Connecting Z Proofs to Prime Field Arithmetic

    All proofs in this library reason over unbounded integers (Z).
    Circom operates in F_p where p is the BN128 scalar field prime (~2^254).
    A circom constraint [LHS === RHS] means [LHS ≡ RHS (mod p)], not [LHS = RHS] in Z.
    These are equivalent only when both sides are in [0, p).

    This module provides the prime constant, a field-membership predicate,
    and bridging lemmas that let per-template proofs show their Z results
    lift to F_p. *)

(** ** The BN128 scalar field prime *)

Definition p_field : Z :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617.

(** ** Field membership predicate *)

Definition in_field (x : Z) : Prop := 0 <= x < p_field.

(** ** Properties of p_field *)

Lemma p_field_pos : 0 < p_field.
Proof. unfold p_field. lia. Qed.

Lemma p_field_gt_pow2_253 : 2 ^ 253 < p_field.
Proof. unfold p_field. vm_compute. reflexivity. Qed.

Lemma p_field_lt_pow2_254 : p_field < 2 ^ 254.
Proof. unfold p_field. vm_compute. reflexivity. Qed.

(** ** Core bridging lemmas *)

(** Two field elements are equal in Z iff they are equal mod p. *)
Theorem Z_eq_iff_Fp_eq : forall a b,
  in_field a -> in_field b ->
  (a = b <-> a mod p_field = b mod p_field).
Proof.
  intros a b Ha Hb. split.
  - intro Heq. subst. reflexivity.
  - intro Hmod.
    assert (a mod p_field = a) by (apply Z.mod_small; unfold in_field in Ha; lia).
    assert (b mod p_field = b) by (apply Z.mod_small; unfold in_field in Hb; lia).
    lia.
Qed.

(** If both sides of a constraint are in [0, p), then mod-p equality implies Z equality. *)
Theorem Fp_constraint_to_Z : forall lhs rhs,
  in_field lhs -> in_field rhs ->
  lhs mod p_field = rhs mod p_field ->
  lhs = rhs.
Proof.
  intros lhs rhs Hlhs Hrhs Hmod.
  apply Z_eq_iff_Fp_eq; assumption.
Qed.

(** Z equality trivially implies mod-p equality. *)
Theorem Z_constraint_to_Fp : forall lhs rhs,
  lhs = rhs -> lhs mod p_field = rhs mod p_field.
Proof. intros. subst. reflexivity. Qed.

(** Addition doesn't wrap when the sum is below p. *)
Lemma fp_add_exact : forall a b,
  in_field a -> in_field b -> a + b < p_field ->
  (a + b) mod p_field = a + b.
Proof.
  intros a b Ha Hb Hsum.
  apply Z.mod_small. unfold in_field in *. lia.
Qed.

(** Multiplication doesn't wrap when the product is below p. *)
Lemma fp_mul_exact : forall a b,
  in_field a -> in_field b -> a * b < p_field ->
  (a * b) mod p_field = a * b.
Proof.
  intros a b Ha Hb Hprod.
  apply Z.mod_small. unfold in_field in *.
  split; [apply Z.mul_nonneg_nonneg; lia | lia].
Qed.

(** Subtraction doesn't wrap when b <= a. *)
Lemma fp_sub_exact : forall a b,
  in_field a -> in_field b -> b <= a ->
  (a - b) mod p_field = a - b.
Proof.
  intros a b Ha Hb Hle.
  apply Z.mod_small. unfold in_field in *. lia.
Qed.

(** ** Convenience lemmas for per-template proofs *)

(** 2^n < p_field when n <= 253. *)
Lemma pow2_lt_p_field : forall (n : nat),
  (n <= 253)%nat -> 2 ^ Z.of_nat n < p_field.
Proof.
  intros n Hn.
  assert (2 ^ Z.of_nat n <= 2 ^ 253).
  { apply Z.pow_le_mono_r; lia. }
  assert (2 ^ 253 < p_field) by exact p_field_gt_pow2_253.
  lia.
Qed.

(** A value in [0, 2^n) with n <= 253 is in the field. *)
Lemma in_field_of_bound : forall x (n : nat),
  0 <= x < 2 ^ Z.of_nat n -> (n <= 253)%nat -> in_field x.
Proof.
  intros x n Hx Hn. unfold in_field.
  assert (2 ^ Z.of_nat n < p_field) by (apply pow2_lt_p_field; exact Hn).
  lia.
Qed.

(** Zero is in the field. *)
Lemma in_field_0 : in_field 0.
Proof. unfold in_field. pose proof p_field_pos. lia. Qed.

(** One is in the field. *)
Lemma in_field_1 : in_field 1.
Proof. unfold in_field, p_field. lia. Qed.

(** A binary value is in the field. *)
Lemma in_field_binary : forall b, b = 0 \/ b = 1 -> in_field b.
Proof.
  intros b [H | H]; subst; [exact in_field_0 | exact in_field_1].
Qed.
