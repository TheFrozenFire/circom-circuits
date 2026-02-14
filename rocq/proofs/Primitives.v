From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(** * Shared Definitions for Circuit Verification *)

(** A value is binary if it is 0 or 1. *)
Definition is_binary (b : Z) : Prop := b = 0 \/ b = 1.

(** All elements of a list are binary. *)
Definition all_binary (bits : list Z) : Prop := Forall is_binary bits.

(** Little-endian binary to number: bits[0] + bits[1]*2 + bits[2]*4 + ... *)
Fixpoint bits_to_num (bits : list Z) : Z :=
  match bits with
  | [] => 0
  | b :: rest => b + 2 * bits_to_num rest
  end.

(** * Core Lemmas *)

(** The circom constraint b * (b - 1) = 0 is equivalent to b being binary. *)
Lemma binary_constraint : forall b : Z,
  b * (b - 1) = 0 <-> is_binary b.
Proof.
  intro b. unfold is_binary. split.
  - intro H.
    destruct (Z.eq_dec b 0) as [Hb0 | Hb0].
    + left. exact Hb0.
    + right. apply Z.mul_eq_0 in H. lia.
  - intros [H | H]; subst; ring.
Qed.

(** bits_to_num with cons — avoids simpl expanding Z multiplication. *)
Lemma bits_to_num_cons : forall b rest,
  bits_to_num (b :: rest) = b + 2 * bits_to_num rest.
Proof. intros. reflexivity. Qed.

(** bits_to_num of the nil list. *)
Lemma bits_to_num_nil : bits_to_num [] = 0.
Proof. reflexivity. Qed.

(** A binary value is non-negative. *)
Lemma binary_nonneg : forall b, is_binary b -> 0 <= b.
Proof. intros b [H | H]; subst; lia. Qed.

(** A binary value is at most 1. *)
Lemma binary_le_1 : forall b, is_binary b -> b <= 1.
Proof. intros b [H | H]; subst; lia. Qed.

(** bits_to_num of all-binary bits is non-negative. *)
Lemma bits_to_num_nonneg : forall bits,
  all_binary bits -> 0 <= bits_to_num bits.
Proof.
  induction bits as [| b rest IH].
  - intros _. simpl. lia.
  - intro Hall. inversion Hall; subst.
    rewrite bits_to_num_cons.
    assert (0 <= b) by (apply binary_nonneg; assumption).
    assert (0 <= bits_to_num rest) by (apply IH; assumption).
    lia.
Qed.

(** 2^n is positive for non-negative n. *)
Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

(** Key bound: if all bits are binary, bits_to_num bits < 2^(length bits). *)
Lemma bits_to_num_bound : forall bits,
  all_binary bits -> 0 <= bits_to_num bits < 2 ^ Z.of_nat (length bits).
Proof.
  induction bits as [| b rest IH].
  - intros _. simpl. lia.
  - intro Hall. inversion Hall; subst.
    specialize (IH H2).
    rewrite bits_to_num_cons. simpl length.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    assert (Hb : 0 <= b <= 1).
    { destruct H1 as [H1 | H1]; subst; lia. }
    lia.
Qed.

(** Uniqueness: two binary lists of the same length with the same value are equal. *)
Lemma bits_to_num_unique : forall a b,
  all_binary a -> all_binary b ->
  length a = length b ->
  bits_to_num a = bits_to_num b ->
  a = b.
Proof.
  induction a as [| ah at_ IH].
  - intros b _ _ Hlen Hval.
    destruct b; simpl in Hlen; [reflexivity | discriminate].
  - intros b Ha Hb Hlen Hval.
    destruct b as [| bh bt]; simpl in Hlen; [discriminate |].
    inversion Ha; subst. inversion Hb; subst.
    repeat rewrite bits_to_num_cons in Hval.
    assert (Hlen' : length at_ = length bt) by lia.
    assert (Hah : 0 <= ah <= 1) by (destruct H1 as [H1|H1]; subst; lia).
    assert (Hbh : 0 <= bh <= 1) by (destruct H3 as [H3|H3]; subst; lia).
    assert (Hbound_at := bits_to_num_bound at_ H2).
    assert (Hbound_bt := bits_to_num_bound bt H4).
    assert (ah = bh).
    {
      assert (Hdiff : ah - bh = 2 * (bits_to_num bt - bits_to_num at_)) by lia.
      rewrite Hlen' in Hbound_at.
      nia.
    }
    subst bh.
    assert (bits_to_num at_ = bits_to_num bt) by lia.
    f_equal. apply IH; assumption.
Qed.

(** Splitting bits_to_num over append. *)
Lemma bits_to_num_app : forall l1 l2,
  bits_to_num (l1 ++ l2) = bits_to_num l1 + 2 ^ Z.of_nat (length l1) * bits_to_num l2.
Proof.
  induction l1 as [| x rest IH].
  - intro l2. simpl bits_to_num. simpl length. rewrite Z.mul_1_l. lia.
  - intro l2. simpl app. rewrite bits_to_num_cons. rewrite IH.
    rewrite bits_to_num_cons. simpl length.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    lia.
Qed.

(** firstn preserves all_binary. *)
Lemma all_binary_firstn : forall bits k,
  all_binary bits -> all_binary (firstn k bits).
Proof.
  intros bits k Hall.
  unfold all_binary in *. apply Forall_nth.
  intros i d Hi.
  rewrite nth_firstn.
  assert (Hlt : (i <? k)%nat = true)
    by (rewrite length_firstn in Hi; apply Nat.ltb_lt; lia).
  rewrite Hlt.
  apply Forall_nth with (i := i) (d := d) in Hall; [exact Hall |].
  rewrite length_firstn in Hi. lia.
Qed.

(** bits_to_num of a firstn prefix is bounded by 2^k. *)
Lemma bits_to_num_firstn_bound : forall bits k,
  all_binary bits -> (k <= length bits)%nat ->
  0 <= bits_to_num (firstn k bits) < 2 ^ Z.of_nat k.
Proof.
  intros bits k Hall Hle.
  assert (Hfirst : all_binary (firstn k bits))
    by (apply all_binary_firstn; exact Hall).
  assert (Hbound := bits_to_num_bound (firstn k bits) Hfirst).
  rewrite length_firstn in Hbound. rewrite Nat.min_l in Hbound by lia.
  exact Hbound.
Qed.
