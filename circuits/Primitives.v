From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Set Default Proof Using "Type".

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

(** Solve goals by exhaustive case analysis on binary hypotheses.
    Handles 1-variable (2 cases), 2-variable (4 cases), and 3-variable (8 cases) splits. *)
Ltac binary_cases :=
  unfold is_binary in *;
  match goal with
  | [Ha : _ = 0 \/ _ = 1, Hb : _ = 0 \/ _ = 1, Hc : _ = 0 \/ _ = 1 |- _] =>
    destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    destruct Hc as [Hc | Hc]; subst; try lia
  | [Ha : _ = 0 \/ _ = 1, Hb : _ = 0 \/ _ = 1 |- _] =>
    destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb]; subst; try lia
  | [Ha : _ = 0 \/ _ = 1 |- _] =>
    destruct Ha as [Ha | Ha]; subst; try lia
  end.

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

(** Derive all_binary from pointwise binary constraints. *)
Lemma binary_constraints_imply_all_binary : forall bits,
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  all_binary bits.
Proof.
  intros bits Hbin. unfold all_binary. apply Forall_nth.
  intros i d Hi. rewrite nth_indep with (d' := 0) by exact Hi.
  apply binary_constraint. apply Hbin. exact Hi.
Qed.

(** Any index into an all-binary list is binary (handles out-of-bounds via nth_overflow → 0). *)
Lemma all_binary_nth_any : forall bits i,
  all_binary bits -> is_binary (nth i bits 0).
Proof.
  intros bits i Hall.
  destruct (Nat.lt_ge_cases i (length bits)) as [Hlt | Hge].
  - eapply Forall_nth; [exact Hall | exact Hlt].
  - rewrite nth_overflow by lia. left. reflexivity.
Qed.

(** skipn preserves all_binary. *)
Lemma all_binary_skipn : forall bits k,
  all_binary bits -> all_binary (skipn k bits).
Proof.
  intros bits k Hall. unfold all_binary in *.
  rewrite <- (firstn_skipn k bits) in Hall.
  apply Forall_app in Hall. destruct Hall as [_ Hall]. exact Hall.
Qed.

(** Decomposing bits_to_num at position n into low and high parts. *)
Lemma bits_to_num_split : forall bits (n : nat),
  (n <= length bits)%nat ->
  bits_to_num bits =
    bits_to_num (firstn n bits) + 2 ^ Z.of_nat n * bits_to_num (skipn n bits).
Proof.
  intros bits n Hle.
  assert (Heq : bits = firstn n bits ++ skipn n bits)
    by (symmetry; apply firstn_skipn).
  rewrite Heq at 1.
  rewrite bits_to_num_app.
  rewrite length_firstn. rewrite Nat.min_l by lia.
  reflexivity.
Qed.

(** The lower n bits of a binary number equal the number modulo 2^n. *)
Lemma bits_to_num_firstn_mod : forall bits (n : nat),
  all_binary bits -> (n <= length bits)%nat ->
  bits_to_num (firstn n bits) = (bits_to_num bits) mod (2 ^ Z.of_nat n).
Proof.
  intros bits n Hall Hle.
  symmetry.
  rewrite (bits_to_num_split bits n Hle).
  replace (2 ^ Z.of_nat n * bits_to_num (skipn n bits))
    with (bits_to_num (skipn n bits) * 2 ^ Z.of_nat n) by ring.
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
  apply Z.mod_small. apply bits_to_num_firstn_bound; assumption.
Qed.

(** * List Aggregation *)

(** Sum of all elements in a list. *)
Fixpoint list_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => x + list_sum rest
  end.

(** list_sum cons lemma. *)
Lemma list_sum_cons : forall x rest,
  list_sum (x :: rest) = x + list_sum rest.
Proof. intros. reflexivity. Qed.

(** list_sum of non-negative values is non-negative. *)
Lemma list_sum_nonneg : forall l,
  Forall (fun x => 0 <= x) l -> 0 <= list_sum l.
Proof.
  induction l as [| x rest IH].
  - intros _. simpl. lia.
  - intro Hall. inversion_clear Hall.
    rewrite list_sum_cons. assert (0 <= list_sum rest) by (apply IH; assumption). lia.
Qed.

(** list_sum of binary values is non-negative. *)
Lemma list_sum_nonneg_binary : forall l,
  Forall is_binary l -> 0 <= list_sum l.
Proof.
  induction l as [| x rest IH].
  - intros _. simpl. lia.
  - intro Hall. inversion_clear Hall.
    rewrite list_sum_cons.
    assert (0 <= x) by (destruct H; lia).
    assert (0 <= list_sum rest) by (apply IH; assumption).
    lia.
Qed.

(** If all indicators are binary and sum to 0, the weighted sum is 0. *)
Lemma binary_zero_weighted_sum : forall indicators values,
  Forall is_binary indicators ->
  list_sum indicators = 0 ->
  list_sum (map (fun p => fst p * snd p) (combine indicators values)) = 0.
Proof.
  induction indicators as [| ind rest IH]; intros values Hall Hsum.
  - simpl. lia.
  - destruct values as [| v vals].
    + simpl. lia.
    + inversion_clear Hall as [| ? ? Hind Hrest].
      rewrite list_sum_cons in Hsum.
      assert (Hind_nn : 0 <= ind) by (destruct Hind; lia).
      assert (Hrest_nn : 0 <= list_sum rest)
        by (apply list_sum_nonneg_binary; assumption).
      assert (Hind0 : ind = 0) by lia.
      subst ind. simpl.
      rewrite IH; [lia | assumption | lia].
Qed.

Fixpoint list_product (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: rest => x * list_product rest
  end.

(** list_product of non-negative values is non-negative. *)
Lemma list_product_nonneg : forall l,
  Forall (fun x => 0 <= x) l -> 0 <= list_product l.
Proof.
  induction l as [| x rest IH].
  - intros _. simpl. lia.
  - intro Hall. inversion_clear Hall. simpl.
    assert (0 <= list_product rest) by (apply IH; assumption).
    apply Z.mul_nonneg_nonneg; assumption.
Qed.

(** An AND-chain of binary values equals 1 iff all values are 1. *)
Lemma binary_and_chain : forall (eqs : list Z),
  Forall is_binary eqs ->
  (list_product eqs = 1 <-> Forall (fun x => x = 1) eqs).
Proof.
  induction eqs as [| e rest IH].
  - intros _. split; intro; constructor.
  - intro Hall. inversion Hall; subst.
    split.
    + intro Hprod. simpl in Hprod.
      destruct H1 as [He | He]; subst.
      * lia.
      * assert (list_product rest = 1) by lia.
        constructor; [reflexivity | apply IH; assumption].
    + intro Hfall. inversion Hfall; subst.
      unfold list_product. fold list_product.
      assert (Hrest : list_product rest = 1) by (apply IH; assumption).
      lia.
Qed.

(** * Big Integer Limb Representation *)

(** Convert a list of n-bit limbs to a number (little-endian).
    limbs_to_num n [l0; l1; ...; lk] = l0 + l1*2^n + l2*2^(2n) + ... *)
Fixpoint limbs_to_num (n : nat) (limbs : list Z) : Z :=
  match limbs with
  | [] => 0
  | l :: rest => l + 2 ^ Z.of_nat n * limbs_to_num n rest
  end.

Lemma limbs_to_num_cons : forall n l rest,
  limbs_to_num n (l :: rest) = l + 2 ^ Z.of_nat n * limbs_to_num n rest.
Proof. intros. reflexivity. Qed.

Lemma limbs_to_num_nil : forall n, limbs_to_num n [] = 0.
Proof. intros. reflexivity. Qed.

(** Pointwise addition of limbs adds their numeric values. *)
Lemma limbs_to_num_add : forall n a b,
  length a = length b ->
  limbs_to_num n a + limbs_to_num n b =
    limbs_to_num n (map (fun p => fst p + snd p) (combine a b)).
Proof.
  induction a as [| a0 arest IH]; intros b Hlen.
  - destruct b; [simpl; lia | simpl in Hlen; lia].
  - destruct b as [| b0 brest]; [simpl in Hlen; lia |].
    simpl combine. simpl map. rewrite !limbs_to_num_cons.
    simpl fst. simpl snd.
    assert (IHapp := IH brest ltac:(simpl in Hlen; lia)).
    lia.
Qed.

(** Carry propagation with incoming carry: generalized version.
    Proves: carry_in + limbs_to_num n inp = limbs_to_num n out + last_carry * 2^(n*k)
    where each limb satisfies in[i] + carry[i-1] = out[i] + carry[i] * 2^n. *)
Lemma carry_propagation_gen :
  forall (n : nat) (inp out carries : list Z) (carry_in : Z),
  length inp = length out ->
  length carries = length inp ->
  (length inp > 0)%nat ->
  (forall i, (i < length inp)%nat ->
    nth i inp 0 + (if (i =? 0)%nat then carry_in else nth (i - 1) carries 0) =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  carry_in + limbs_to_num n inp =
    limbs_to_num n out +
    nth (length inp - 1) carries 0 * 2 ^ (Z.of_nat n * Z.of_nat (length inp)).
Proof.
  induction inp as [| a rest IH]; intros out carries carry_in Hlen Hclen Hgt Hprop.
  - simpl in Hgt. lia.
  - destruct out as [| b outs]; [simpl in Hlen; lia |].
    destruct carries as [| c cs]; [simpl in Hclen; lia |].
    rewrite !limbs_to_num_cons.
    assert (H0 := Hprop 0%nat ltac:(simpl; lia)).
    simpl Nat.eqb in H0. simpl nth in H0.
    assert (Hlen' : length rest = length outs) by (simpl in Hlen; lia).
    assert (Hclen' : length cs = length rest) by (simpl in Hclen; lia).
    destruct rest as [| a2 rest'].
    + (* Single limb: rest is empty *)
      rewrite !limbs_to_num_nil. rewrite !Z.mul_0_r.
      simpl in Hlen'. destruct outs; [| simpl in Hlen'; lia].
      rewrite limbs_to_num_nil. rewrite Z.mul_0_r.
      simpl length. simpl nth. rewrite Z.mul_1_r. lia.
    + (* Multi-limb *)
      simpl in H0.
      assert (Hgt' : (length (a2 :: rest') > 0)%nat) by (simpl; lia).
      assert (Hprop' : forall i, (i < length (a2 :: rest'))%nat ->
        nth i (a2 :: rest') 0 +
          (if (i =? 0)%nat then c else nth (i - 1) cs 0) =
        nth i outs 0 + nth i cs 0 * 2 ^ Z.of_nat n).
      { intros i Hi. destruct i.
        - specialize (Hprop 1%nat ltac:(simpl in *; lia)).
          simpl Nat.eqb in Hprop |- *.
          change (nth 1 (a :: a2 :: rest') 0) with (nth 0 (a2 :: rest') 0) in Hprop.
          change (nth 0 (c :: cs) 0) with c in Hprop.
          change (nth 1 (b :: outs) 0) with (nth 0 outs 0) in Hprop.
          change (nth 1 (c :: cs) 0) with (nth 0 cs 0) in Hprop.
          exact Hprop.
        - specialize (Hprop (S (S i)) ltac:(simpl in *; lia)).
          simpl Nat.eqb in Hprop |- *.
          change (nth (S (S i)) (a :: a2 :: rest') 0)
            with (nth (S i) (a2 :: rest') 0) in Hprop.
          change (nth (S (S i)) (b :: outs) 0)
            with (nth (S i) outs 0) in Hprop.
          change (nth (S (S i)) (c :: cs) 0)
            with (nth (S i) cs 0) in Hprop.
          replace (S (S i) - 1)%nat with (S i) in Hprop by lia.
          change (nth (S i) (c :: cs) 0) with (nth i cs 0) in Hprop.
          replace (S i - 1)%nat with i by lia.
          exact Hprop. }
      assert (IHapp := IH outs cs c Hlen' Hclen' Hgt' Hprop').
      simpl length. simpl length in IHapp.
      replace (S (S (length rest')) - 1)%nat with (S (length rest'))%nat by lia.
      replace (S (length rest') - 1)%nat with (length rest')%nat in IHapp by lia.
      change (nth (S (length rest')) (c :: cs) 0) with (nth (length rest') cs 0).
      rewrite !Nat2Z.inj_succ. rewrite Z.mul_succ_r.
      rewrite Z.pow_add_r by lia. lia.
Qed.

(** Carry propagation: if each limb satisfies the carry equation
    and the final carry is zero, then the limb values are equal.
    This is the core lemma for BigAdd/BigSub/BigMult carry propagation. *)
Lemma carry_propagation_preserves_value :
  forall (n : nat) (inp out carries : list Z),
  length inp = length out ->
  length carries = length inp ->
  (length inp > 0)%nat ->
  (* First limb: in[0] = out[0] + carry[0] * 2^n *)
  nth 0 inp 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (* Middle limbs: in[i] + carry[i-1] = out[i] + carry[i] * 2^n *)
  (forall i, (0 < i < length inp)%nat ->
    nth i inp 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  (* Final carry is zero *)
  nth (length inp - 1) carries 0 = 0 ->
  limbs_to_num n inp = limbs_to_num n out.
Proof.
  intros n inp out carries Hlen Hclen Hgt H0 Hmid Hfinal.
  assert (Hgen := carry_propagation_gen n inp out carries 0 Hlen Hclen Hgt).
  assert (Hprop : forall i, (i < length inp)%nat ->
    nth i inp 0 + (if (i =? 0)%nat then 0 else nth (i - 1) carries 0) =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n).
  { intros i Hi. destruct (Nat.eqb_spec i 0) as [Heq | Hne].
    - subst i. lia.
    - apply Hmid. lia. }
  specialize (Hgen Hprop). rewrite Hfinal in Hgen. lia.
Qed.

(** * Bitwise Operation Definitions *)

(** Binary XOR: a + b - 2*a*b *)
Definition xor_bit (a b : Z) : Z := a + b - 2 * a * b.

(** SHA-256 choice function: a*(b-c) + c = a&b | (!a)&c *)
Definition ch_bit (a b c : Z) : Z := a * (b - c) + c.

(** SHA-256 majority function: a&b ^ a&c ^ b&c *)
Definition maj_bit (a b c : Z) : Z :=
  a * b + a * c + b * c - 2 * a * b * c.

(** Three-input XOR: a ^ b ^ c *)
Definition xor3_bit (a b c : Z) : Z := xor_bit a (xor_bit b c).

(** Fold XOR over a list of binary values (left fold). *)
Fixpoint fold_xor (bits : list Z) : Z :=
  match bits with
  | [] => 0
  | [x] => x
  | x :: rest => xor_bit x (fold_xor rest)
  end.

(** xor_bit preserves binary. *)
Lemma xor_bit_binary : forall a b,
  is_binary a -> is_binary b -> is_binary (xor_bit a b).
Proof.
  intros a b Ha Hb. unfold xor_bit; binary_cases.
Qed.

(** xor_bit matches the constraint a + b - 2*a*b. *)
Lemma xor_bit_correct : forall a b out,
  is_binary a -> is_binary b ->
  out = a + b - 2 * a * b ->
  out = xor_bit a b.
Proof.
  intros a b out Ha Hb Hout. unfold xor_bit; binary_cases.
Qed.

(** * Ordering Definitions *)

(** Helper: strict ordering of a list via adjacent comparisons. *)
Fixpoint strictly_ascending (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as rest) => x < y /\ strictly_ascending rest
  end.

Fixpoint strictly_descending (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as rest) => x > y /\ strictly_descending rest
  end.
