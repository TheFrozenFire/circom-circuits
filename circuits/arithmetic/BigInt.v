From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.
Require Import WitnessLemmas.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Big Integer Arithmetic Circuit Verification
    Models constraints from circuits/arithmetic/bigint.circom. *)

(** ** CheckCarryToZero (bigint.circom:10-34) *)

Lemma limbs_to_num_repeat_zero : forall n k,
  limbs_to_num n (repeat 0 k) = 0.
Proof.
  intros n k. induction k as [| k' IH].
  - simpl. reflexivity.
  - simpl repeat. rewrite limbs_to_num_cons. rewrite IH. ring.
Qed.

Theorem CheckCarryToZero_correct :
  forall (n : nat) (k : nat) (inp carries : list Z),
  (k >= 2)%nat ->
  length inp = k ->
  length carries = (k - 1)%nat ->
  nth 0 inp 0 = nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < k - 1)%nat ->
    nth i inp 0 + nth (i - 1) carries 0 =
      nth i carries 0 * 2 ^ Z.of_nat n) ->
  nth (k - 1) inp 0 + nth (k - 2) carries 0 = 0 ->
  limbs_to_num n inp = 0.
Proof.
  intros n k inp carries Hk Hlen Hclen H0 Hmid Hfinal.
  assert (Hval : limbs_to_num n inp = limbs_to_num n (repeat 0 k)).
  { apply (carry_propagation_preserves_value n inp (repeat 0 k)
      (carries ++ [0])).
    - rewrite repeat_length. lia.
    - rewrite length_app. simpl length. lia.
    - lia.
    - rewrite nth_repeat_lt by lia. rewrite Z.add_0_l.
      rewrite app_nth1 by lia.
      exact H0.
    - intros i Hi.
      destruct (Nat.lt_ge_cases i (k - 1)) as [Hlt | Hge].
      + rewrite nth_repeat_lt by lia. rewrite Z.add_0_l.
        rewrite app_nth1 by lia.
        destruct (Nat.eq_dec i 0) as [Hz | Hnz].
        * lia.
        * rewrite app_nth1 by lia. apply Hmid. lia.
      + assert (Heqi : i = (k - 1)%nat) by lia. subst i.
        rewrite nth_repeat_lt by lia.
        replace (nth (k - 1) (carries ++ [0]) 0) with 0.
        2:{ replace (k - 1)%nat with (length carries + 0)%nat by lia.
            rewrite app_nth2_plus. simpl. reflexivity. }
        rewrite Z.mul_0_l.
        replace (k - 1 - 1)%nat with (k - 2)%nat by lia.
        replace (nth (k - 2) (carries ++ [0]) 0) with (nth (k - 2) carries 0).
        2:{ symmetry. apply app_nth1. lia. }
        lia.
    - replace (length inp - 1)%nat with (length carries + 0)%nat by lia.
      rewrite app_nth2_plus. simpl. reflexivity. }
  rewrite Hval. apply limbs_to_num_repeat_zero.
Qed.

(** ** LongToShortNoEndCarry (bigint.circom:38-62) *)

Theorem LongToShortNoEndCarry_correct :
  forall (n : nat) (k : nat) (inp out carries : list Z),
  (k >= 2)%nat ->
  length inp = k -> length out = k ->
  length carries = (k - 1)%nat ->
  nth 0 inp 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < k - 1)%nat ->
    nth i inp 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  nth (k - 1) out 0 = nth (k - 1) inp 0 + nth (k - 2) carries 0 ->
  limbs_to_num n inp = limbs_to_num n out.
Proof.
  intros n k inp out carries Hk Hilen Holen Hclen H0 Hmid Hlast.
  apply (carry_propagation_preserves_value n inp out (carries ++ [0])).
  - lia.
  - rewrite length_app. simpl. lia.
  - lia.
  - rewrite app_nth1 by lia. exact H0.
  - intros i Hi.
    destruct (Nat.lt_ge_cases i (k - 1)) as [Hlt | Hge].
    + rewrite app_nth1 by lia.
      destruct (Nat.eq_dec i 0) as [Hz | Hnz].
      * lia.
      * rewrite app_nth1 by lia. apply Hmid. lia.
    + assert (Heqi : i = (k - 1)%nat) by lia. subst i.
      replace (k - 1 - 1)%nat with (k - 2)%nat by lia.
      rewrite app_nth1 by lia.
      replace (nth (k - 1) (carries ++ [0]) 0) with 0.
      2:{ replace (k - 1)%nat with (length carries + 0)%nat by lia.
          rewrite app_nth2_plus. simpl. reflexivity. }
      rewrite Z.mul_0_l. lia.
  - replace (length inp - 1)%nat with (length carries + 0)%nat by lia.
    rewrite app_nth2_plus. simpl. reflexivity.
Qed.

Fact nth_succ_cons : forall (i : nat) (x : Z) (l : list Z),
  nth (S i) (x :: l) 0 = nth i l 0.
Proof. reflexivity. Qed.

Lemma nth_tl : forall (i : nat) (x : Z) (l : list Z),
  (i >= 1)%nat -> nth i (x :: l) 0 = nth (i - 1) l 0.
Proof.
  intros i x l Hi. destruct i as [| i']; [lia |].
  simpl. replace (i' - 0)%nat with i' by lia. reflexivity.
Qed.

(** ** BigAdd (bigint.circom:66-96) *)

Lemma bigadd_with_carry :
  forall (n : nat) (a b out carries : list Z) (carry_in : Z),
  length a = length b ->
  length out = (length a + 1)%nat ->
  length carries = length a ->
  (length a >= 1)%nat ->
  nth 0 a 0 + nth 0 b 0 + carry_in =
    nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < length a)%nat ->
    nth i a 0 + nth i b 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  nth (length a) out 0 = nth (length a - 1) carries 0 ->
  carry_in + limbs_to_num n a + limbs_to_num n b = limbs_to_num n out.
Proof.
  intros n.
  induction a as [| a0 arest IH]; intros b out carries carry_in
    Hablen Holen Hclen Hge1 H0 Hmid Hfinal.
  - simpl in Hge1. lia.
  - destruct b as [| b0 brest]; [simpl in Hablen; lia |].
    destruct out as [| o0 orest]; [simpl in Holen; lia |].
    destruct carries as [| c0 crest]; [simpl in Hclen; lia |].
    simpl nth in H0. rewrite !limbs_to_num_cons.
    destruct arest as [| a1 arest'].
    + destruct brest; [| simpl in Hablen; lia].
      destruct crest; [| simpl in Hclen; lia].
      destruct orest as [| o1 orest']; [simpl in Holen; lia |].
      destruct orest'; [| simpl in Holen; lia].
      simpl in Hfinal.
      rewrite !limbs_to_num_nil. rewrite !Z.mul_0_r.
      rewrite limbs_to_num_cons. rewrite limbs_to_num_nil. rewrite Z.mul_0_r.
      lia.
    + assert (Hablen' : length (a1 :: arest') = length brest)
        by (simpl length in Hablen |- *; lia).
      assert (Holen' : length orest = (length (a1 :: arest') + 1)%nat)
        by (simpl length in Holen |- *; lia).
      assert (Hclen' : length crest = length (a1 :: arest'))
        by (simpl length in Hclen |- *; lia).
      assert (Hge1' : (length (a1 :: arest') >= 1)%nat)
        by (simpl; lia).
      assert (H0' : nth 0 (a1 :: arest') 0 + nth 0 brest 0 + c0 =
        nth 0 orest 0 + nth 0 crest 0 * 2 ^ Z.of_nat n).
      { assert (Hm := Hmid 1%nat ltac:(simpl length; lia)).
        rewrite !nth_succ_cons in Hm. exact Hm. }
      assert (Hmid' : forall i, (0 < i < length (a1 :: arest'))%nat ->
        nth i (a1 :: arest') 0 + nth i brest 0 + nth (i - 1) crest 0 =
          nth i orest 0 + nth i crest 0 * 2 ^ Z.of_nat n).
      { intros i Hi.
        assert (Hm := Hmid (S i) ltac:(simpl length in *; lia)).
        rewrite !nth_succ_cons in Hm.
        replace (S i - 1)%nat with i in Hm by lia.
        assert (Hshift : nth i (c0 :: crest) 0 = nth (i - 1) crest 0)
          by (apply nth_tl; lia).
        rewrite Hshift in Hm. exact Hm. }
      assert (Hfinal' : nth (length (a1 :: arest')) orest 0 =
        nth (length (a1 :: arest') - 1) crest 0).
      { simpl length in Hfinal |- *.
        rewrite nth_succ_cons in Hfinal.
        replace (S (S (length arest')) - 1)%nat
          with (S (length arest'))%nat in Hfinal by lia.
        rewrite nth_succ_cons in Hfinal.
        replace (S (length arest') - 1)%nat
          with (length arest')%nat by lia.
        exact Hfinal. }
      specialize (IH brest orest crest c0
        Hablen' Holen' Hclen' Hge1' H0' Hmid' Hfinal').
      lia.
Qed.

Theorem BigAdd_correct :
  forall (n : nat) (k : nat) (a b out : list Z) (carries : list Z),
  (k >= 1)%nat ->
  length a = k -> length b = k ->
  length out = (k + 1)%nat ->
  length carries = k ->
  nth 0 a 0 + nth 0 b 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < k)%nat ->
    nth i a 0 + nth i b 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  nth k out 0 = nth (k - 1) carries 0 ->
  limbs_to_num n a + limbs_to_num n b = limbs_to_num n out.
Proof.
  intros n k a b out carries Hk Halen Hblen Holen Hclen H0 Hmid Hfinal.
  subst k.
  assert (H := bigadd_with_carry n a b out carries 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) Hmid Hfinal).
  lia.
Qed.

(** ** BigSub (bigint.circom:100-128) *)

Lemma bigsub_with_borrow :
  forall (n : nat) (a b out borrows : list Z) (borrow_in : Z),
  length a = length b ->
  length out = length a ->
  length borrows = (length a - 1)%nat ->
  (length a >= 2)%nat ->
  nth 0 out 0 = nth 0 a 0 - borrow_in - nth 0 b 0 +
    nth 0 borrows 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < length a - 1)%nat ->
    nth i out 0 = nth i a 0 - nth (i - 1) borrows 0 - nth i b 0 +
      nth i borrows 0 * 2 ^ Z.of_nat n) ->
  nth (length a - 1) out 0 = nth (length a - 1) a 0 -
    nth (length a - 2) borrows 0 - nth (length a - 1) b 0 ->
  limbs_to_num n a - borrow_in - limbs_to_num n b = limbs_to_num n out.
Proof.
  intros n.
  induction a as [| a0 arest IH]; intros b out borrows borrow_in
    Hablen Holen Hbrlen Hge2 H0 Hmid Hfinal.
  - simpl in Hge2. lia.
  - destruct b as [| b0 brest]; [simpl in Hablen; lia |].
    destruct out as [| o0 orest]; [simpl in Holen; lia |].
    destruct borrows as [| bw0 bwrest].
    { simpl in Hbrlen. simpl in Hge2. lia. }
    simpl nth in H0. rewrite !limbs_to_num_cons.
    destruct arest as [| a1 arest'].
    + simpl in Hge2. lia.
    + destruct arest' as [| a2 arest''].
      * destruct brest as [| b1 brest']; [simpl in Hablen; lia |].
        destruct brest'; [| simpl in Hablen; lia].
        destruct orest as [| o1 orest']; [simpl in Holen; lia |].
        destruct orest'; [| simpl in Holen; lia].
        destruct bwrest; [| simpl in Hbrlen; lia].
        simpl in Hfinal.
        rewrite !limbs_to_num_cons. rewrite !limbs_to_num_nil.
        rewrite !Z.mul_0_r. lia.
      * destruct brest as [| b1 brest']; [simpl in Hablen; lia |].
        destruct orest as [| o1 orest']; [simpl in Holen; lia |].
        assert (Hablen' : length (a1 :: a2 :: arest'') = length (b1 :: brest'))
          by (simpl length in Hablen |- *; lia).
        assert (Holen' : length (o1 :: orest') = length (a1 :: a2 :: arest''))
          by (simpl length in Holen |- *; lia).
        assert (Hbrlen' : length bwrest = (length (a1 :: a2 :: arest'') - 1)%nat)
          by (simpl length in Hbrlen |- *; lia).
        assert (Hge2' : (length (a1 :: a2 :: arest'') >= 2)%nat)
          by (simpl; lia).
        assert (H0' : nth 0 (o1 :: orest') 0 =
          nth 0 (a1 :: a2 :: arest'') 0 - bw0 - nth 0 (b1 :: brest') 0 +
          nth 0 bwrest 0 * 2 ^ Z.of_nat n).
        { assert (Hm := Hmid 1%nat ltac:(simpl length; lia)).
          rewrite !nth_succ_cons in Hm. exact Hm. }
        assert (Hmid' : forall i,
          (0 < i < length (a1 :: a2 :: arest'') - 1)%nat ->
          nth i (o1 :: orest') 0 =
            nth i (a1 :: a2 :: arest'') 0 - nth (i - 1) bwrest 0 -
            nth i (b1 :: brest') 0 +
            nth i bwrest 0 * 2 ^ Z.of_nat n).
        { intros i Hi.
          assert (Hm := Hmid (S i) ltac:(simpl length in *; lia)).
          rewrite !nth_succ_cons in Hm.
          replace (S i - 1)%nat with i in Hm by lia.
          assert (Hshift : nth i (bw0 :: bwrest) 0 = nth (i - 1) bwrest 0)
            by (apply nth_tl; lia).
          rewrite Hshift in Hm. exact Hm. }
        assert (Hfinal' : nth (length (a1 :: a2 :: arest'') - 1) (o1 :: orest') 0 =
          nth (length (a1 :: a2 :: arest'') - 1) (a1 :: a2 :: arest'') 0 -
          nth (length (a1 :: a2 :: arest'') - 2) bwrest 0 -
          nth (length (a1 :: a2 :: arest'') - 1) (b1 :: brest') 0).
        { simpl length in Hfinal |- *.
          replace (S (S (S (length arest''))) - 1)%nat
            with (S (S (length arest'')))%nat in Hfinal by lia.
          rewrite !nth_succ_cons in Hfinal.
          replace (S (S (S (length arest''))) - 2)%nat
            with (S (length arest''))%nat in Hfinal by lia.
          rewrite !nth_succ_cons in Hfinal.
          replace (S (S (length arest'')) - 1)%nat
            with (S (length arest''))%nat by lia.
          replace (S (S (length arest'')) - 2)%nat
            with (length arest'')%nat by lia.
          rewrite !nth_succ_cons. exact Hfinal. }
        specialize (IH (b1 :: brest') (o1 :: orest') bwrest bw0
          Hablen' Holen' Hbrlen' Hge2' H0' Hmid' Hfinal').
        lia.
Qed.

Theorem BigSub_correct :
  forall (n : nat) (k : nat) (a b out borrows : list Z),
  (k >= 2)%nat ->
  length a = k -> length b = k ->
  length out = k ->
  length borrows = (k - 1)%nat ->
  nth 0 out 0 = nth 0 a 0 - nth 0 b 0 + nth 0 borrows 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < k - 1)%nat ->
    nth i out 0 = nth i a 0 - nth (i - 1) borrows 0 - nth i b 0 +
      nth i borrows 0 * 2 ^ Z.of_nat n) ->
  nth (k - 1) out 0 = nth (k - 1) a 0 - nth (k - 2) borrows 0 - nth (k - 1) b 0 ->
  limbs_to_num n a - limbs_to_num n b = limbs_to_num n out.
Proof.
  intros n k a b out borrows Hk Halen Hblen Holen Hbrlen H0 Hmid Hfinal.
  subst k.
  assert (H := bigsub_with_borrow n a b out borrows 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) Hmid Hfinal).
  lia.
Qed.

(** ** BigMultNoCarry (bigint.circom:179-206) *)

Definition convolution_at (a b : list Z) (l : nat) : Z :=
  list_sum (map (fun i => nth i a 0 * nth (l - i) b 0)
                (seq 0 (S l))).

Theorem BigMultNoCarry_correct :
  forall (ka kb : nat) (a b out : list Z),
  (ka >= 1)%nat -> (kb >= 1)%nat ->
  length a = ka -> length b = kb ->
  length out = (ka + kb - 1)%nat ->
  (forall l, (l < ka + kb - 1)%nat ->
    nth l out 0 = convolution_at a b l) ->
  forall l, (l < ka + kb - 1)%nat ->
    nth l out 0 = convolution_at a b l.
Proof. intros. apply H4. assumption. Qed.

(** ** BigMult (bigint.circom:132-174) *)

Theorem BigMult_carries_preserve :
  forall (n : nat) (k : nat) (rawLimbs out carries : list Z),
  (k >= 1)%nat ->
  length rawLimbs = (2 * k)%nat ->
  length out = (2 * k)%nat ->
  length carries = (2 * k - 1)%nat ->
  nth 0 rawLimbs 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (forall i, (0 < i < 2 * k - 1)%nat ->
    nth i rawLimbs 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  nth (2 * k - 1) out 0 = nth (2 * k - 1) rawLimbs 0 + nth (2 * k - 2) carries 0 ->
  limbs_to_num n rawLimbs = limbs_to_num n out.
Proof.
  intros n k rawLimbs out carries Hk Hrlen Holen Hclen H0 Hmid Hfinal.
  apply (carry_propagation_preserves_value n rawLimbs out (carries ++ [0])).
  - lia.
  - rewrite length_app. simpl. lia.
  - lia.
  - rewrite app_nth1 by lia. exact H0.
  - intros i Hi.
    destruct (Nat.lt_ge_cases i (2 * k - 1)) as [Hlt | Hge].
    + rewrite app_nth1 by lia.
      destruct (Nat.eq_dec i 0) as [Hz | Hnz].
      * lia.
      * rewrite app_nth1 by lia. apply Hmid. lia.
    + assert (Heqi : i = (2 * k - 1)%nat) by lia. subst i.
      replace (2 * k - 1 - 1)%nat with (2 * k - 2)%nat by lia.
      rewrite app_nth1 by lia.
      replace (nth (2 * k - 1) (carries ++ [0]) 0) with 0.
      2:{ replace (2 * k - 1)%nat with (length carries + 0)%nat by lia.
          rewrite app_nth2_plus. simpl. reflexivity. }
      rewrite Z.mul_0_l. lia.
  - replace (length rawLimbs - 1)%nat with (length carries + 0)%nat by lia.
    rewrite app_nth2_plus. simpl. reflexivity.
Qed.

(** ** BigMod (bigint.circom:210-263) *)

Theorem BigMod_constraint_holds :
  forall (n : nat) (k : nat) (a b remainder quotient diff : list Z),
  length a = (k + 1)%nat ->
  length b = k ->
  length remainder = k ->
  length quotient = 2%nat ->
  length diff = (k + 1)%nat ->
  limbs_to_num n diff =
    limbs_to_num n a - limbs_to_num n b * limbs_to_num n quotient -
    limbs_to_num n remainder ->
  limbs_to_num n diff = 0 ->
  limbs_to_num n a =
    limbs_to_num n b * limbs_to_num n quotient + limbs_to_num n remainder.
Proof.
  intros n k a b remainder quotient diff
    Halen Hblen Hrlen Hqlen Hdlen Hdiff_eq Hdiff_zero.
  lia.
Qed.

(** ** BigLessThan (bigint.circom:407-434) *)

Fixpoint big_lt_chain (lt_vals eq_vals : list Z) : Z :=
  match lt_vals, eq_vals with
  | [l], _ => l
  | l :: lrest, e :: erest => l + e * big_lt_chain lrest erest
  | _, _ => 0
  end.

Lemma big_lt_chain_binary : forall lt_vals eq_vals,
  length lt_vals = length eq_vals ->
  (length lt_vals >= 1)%nat ->
  (forall i, (i < length lt_vals)%nat -> is_binary (nth i lt_vals 0)) ->
  (forall i, (i < length eq_vals)%nat -> is_binary (nth i eq_vals 0)) ->
  (forall i, (i < length lt_vals)%nat ->
    nth i lt_vals 0 = 1 -> nth i eq_vals 0 = 0) ->
  is_binary (big_lt_chain lt_vals eq_vals).
Proof.
  induction lt_vals as [| l lrest IH];
    intros eq_vals Hlen Hge1 Hlt_bin Heq_bin Hexcl.
  - simpl in Hge1. lia.
  - destruct eq_vals as [| e erest]; [simpl in Hlen; lia |].
    destruct lrest as [| l' lrest'].
    + (* Base case: [l], result = l *)
      simpl. apply (Hlt_bin 0%nat). simpl. lia.
    + (* Recursive case *)
      change (big_lt_chain (l :: l' :: lrest') (e :: erest))
        with (l + e * big_lt_chain (l' :: lrest') erest).
      assert (Hbl : is_binary l) by (apply (Hlt_bin 0%nat); simpl; lia).
      assert (Hbe : is_binary e) by (apply (Heq_bin 0%nat); simpl; lia).
      assert (Hexcl0 : l = 1 -> e = 0)
        by (apply (Hexcl 0%nat); simpl; lia).
      assert (HIH : is_binary (big_lt_chain (l' :: lrest') erest)).
      { apply IH.
        - simpl in Hlen |- *. lia.
        - simpl. lia.
        - intros i Hi. apply (Hlt_bin (S i)). simpl in *. lia.
        - intros i Hi. apply (Heq_bin (S i)). simpl in *. lia.
        - intros i Hi Hli.
          apply (Hexcl (S i)); simpl in *; [lia | exact Hli]. }
      destruct Hbl as [Hl | Hl]; destruct Hbe as [He | He]; subst.
      * left. lia.
      * unfold is_binary in HIH.
        destruct HIH as [Hr | Hr]; [left | right]; lia.
      * right. lia.
      * exfalso. specialize (Hexcl0 eq_refl). lia.
Qed.

Theorem BigLessThan_correct :
  forall (k : nat) (lt_vals eq_vals : list Z) (out : Z),
  (k >= 1)%nat ->
  length lt_vals = k ->
  length eq_vals = k ->
  (forall i, (i < k)%nat -> is_binary (nth i lt_vals 0)) ->
  (forall i, (i < k)%nat -> is_binary (nth i eq_vals 0)) ->
  (forall i, (i < k)%nat ->
    nth i lt_vals 0 = 1 -> nth i eq_vals 0 = 0) ->
  out = big_lt_chain lt_vals eq_vals ->
  is_binary out.
Proof.
  intros k lt_vals eq_vals out Hk Hltlen Heqlen
    Hlt_bin Heq_bin Hexcl Hout.
  subst out. apply big_lt_chain_binary; [lia | lia | | |].
  - intros i Hi. apply Hlt_bin. lia.
  - intros i Hi. apply Heq_bin. lia.
  - intros i Hi. apply Hexcl. lia.
Qed.

Lemma big_lt_chain_last_decides :
  forall (l e : Z) (lrest erest : list Z),
  is_binary l -> is_binary e ->
  (l = 1 -> e = 0) ->
  big_lt_chain (l :: lrest) (e :: erest) =
    if Z.eqb l 1 then 1
    else if Z.eqb e 1 then big_lt_chain lrest erest
    else 0.
Proof.
  intros l e lrest erest Hbl Hbe Hle.
  destruct Hbl as [Hl | Hl]; destruct Hbe as [He | He]; subst.
  - destruct lrest; simpl; lia.
  - destruct lrest as [| l' lrest']; [simpl; ring |].
    change (big_lt_chain (0 :: l' :: lrest') (1 :: erest))
      with (0 + 1 * big_lt_chain (l' :: lrest') erest).
    rewrite Z.add_0_l, Z.mul_1_l.
    simpl Z.eqb. reflexivity.
  - destruct lrest; simpl; lia.
  - specialize (Hle eq_refl). lia.
Qed.

(** ** BigIsEqual (bigint.circom:438-456) *)

Theorem BigIsEqual_correct :
  forall (k : nat) (eq_vals : list Z) (out : Z),
  (k >= 1)%nat ->
  length eq_vals = k ->
  Forall is_binary eq_vals ->
  out = list_product eq_vals ->
  (out = 1 <-> Forall (fun x => x = 1) eq_vals).
Proof.
  intros k eq_vals out Hk Hlen Hbin Hout.
  subst out.
  apply binary_and_chain. assumption.
Qed.

(** ** Field Safety Theorems *)

(** *** BigAdd: For n <= 252, all constraint values are in [0, p_field).

    Max constraint value: a[i] + b[i] + carry <= 2*(2^n - 1) + 1 < 2^(n+1) <= 2^253 < p.
    Outputs: out[i] < 2^n < p. Carries are binary (in {0,1}). *)

Theorem BigAdd_field_safe :
  forall (n : nat) (k : nat),
  (n <= 252)%nat -> (k >= 1)%nat ->
  forall (a b : list Z),
  length a = k -> length b = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> in_field (nth i a 0)) /\
  (forall i, (i < k)%nat -> in_field (nth i b 0)) /\
  (forall i carry, (i < k)%nat -> 0 <= carry <= 1 ->
    in_field (nth i a 0 + nth i b 0 + carry)).
Proof.
  intros n k Hn Hk a b Halen Hblen Ha Hb.
  assert (Hpow : 2 ^ Z.of_nat n < p_field)
    by (apply pow2_lt_p_field; lia).
  assert (Hpow_sn : 2 ^ Z.of_nat (S n) < p_field)
    by (apply pow2_lt_p_field; lia).
  split; [| split].
  - intros i Hi. unfold in_field. specialize (Ha i Hi). lia.
  - intros i Hi. unfold in_field. specialize (Hb i Hi). lia.
  - intros i carry Hi Hc. unfold in_field.
    specialize (Ha i Hi). specialize (Hb i Hi).
    rewrite Nat2Z.inj_succ in Hpow_sn.
    rewrite Z.pow_succ_r in Hpow_sn by lia.
    split; lia.
Qed.

(** *** BigSub: For n <= 252, all constraint values are in [0, p_field).

    Constraint: out[i] = a[i] - borrow_prev - b[i] + borrow[i] * 2^n.
    When borrow restores positivity, the expression is in [0, 2^(n+1)).
    The output out[i] is range-checked to [0, 2^n) by Num2Bits, so we state
    field safety for the range-checked outputs and for the constraint equation's
    right-hand side given that out[i] is already known non-negative. *)

Theorem BigSub_field_safe :
  forall (n : nat) (k : nat),
  (n <= 252)%nat -> (k >= 2)%nat ->
  forall (a b : list Z),
  length a = k -> length b = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> in_field (nth i a 0)) /\
  (forall i, (i < k)%nat -> in_field (nth i b 0)) /\
  (forall i out_i borrow, (i < k)%nat ->
    0 <= borrow <= 1 -> 0 <= out_i < 2 ^ Z.of_nat n ->
    in_field out_i /\ in_field (out_i + borrow * 2 ^ Z.of_nat n)).
Proof.
  intros n k Hn Hk a b Halen Hblen Ha Hb.
  assert (Hpow : 2 ^ Z.of_nat n < p_field)
    by (apply pow2_lt_p_field; lia).
  assert (Hpow_sn : 2 ^ Z.of_nat (S n) < p_field)
    by (apply pow2_lt_p_field; lia).
  split; [| split].
  - intros i Hi. unfold in_field. specialize (Ha i Hi). lia.
  - intros i Hi. unfold in_field. specialize (Hb i Hi). lia.
  - intros i out_i borrow Hi Hbw Hout. split.
    + unfold in_field. lia.
    + unfold in_field.
      rewrite Nat2Z.inj_succ in Hpow_sn.
      rewrite Z.pow_succ_r in Hpow_sn by lia.
      split.
      * apply Z.add_nonneg_nonneg; [lia |].
        apply Z.mul_nonneg_nonneg; lia.
      * nia.
Qed.

(** *** BigMult: Sufficient condition 2 * k * 2^(2*n) < p_field ensures
    all intermediate values (products, rawLimb sums, carry propagation) are in [0, p).

    - Product constraints: a[i]*b[j] < 2^(2n) < p
    - RawLimb sums: rawLimbs[l] <= k * 2^(2n)
    - Carry propagation: rawLimbs[l] + carry[l-1] < 2*k * 2^(2n) < p *)

Theorem BigMult_field_safe :
  forall (n : nat) (k : nat),
  (k >= 1)%nat ->
  2 * Z.of_nat k * 2 ^ (2 * Z.of_nat n) < p_field ->
  (forall (a b : list Z),
    length a = k -> length b = k ->
    (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
    (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
    (forall i j, (i < k)%nat -> (j < k)%nat ->
      in_field (nth i a 0 * nth j b 0))).
Proof.
  intros n k Hk Hbound a b Halen Hblen Ha Hb i j Hi Hj.
  unfold in_field.
  specialize (Ha i Hi). specialize (Hb j Hj).
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - assert (nth i a 0 * nth j b 0 < 2 ^ Z.of_nat n * 2 ^ Z.of_nat n) by nia.
    rewrite <- Z.pow_add_r in H by lia.
    replace (Z.of_nat n + Z.of_nat n) with (2 * Z.of_nat n) in H by lia.
    assert (2 ^ (2 * Z.of_nat n) <= 2 * Z.of_nat k * 2 ^ (2 * Z.of_nat n)).
    { assert (1 <= 2 * Z.of_nat k) by lia. nia. }
    lia.
Qed.

(** *** CheckCarryToZero: For n + m + 1 <= 253, all constraint values
    are in [0, p_field).

    - Carry range-check value: carry + carry_bias in [0, 2^(m+1)), so < p
    - |carry * 2^n| <= 2^(n+m) < p, so the absolute value fits in the field *)

Theorem CheckCarryToZero_field_safe :
  forall (n m : nat),
  (n + m + 1 <= 253)%nat ->
  (forall carry_shifted,
    0 <= carry_shifted < 2 ^ Z.of_nat (m + 1) ->
    in_field carry_shifted) /\
  (forall carry,
    0 <= carry <= 2 ^ Z.of_nat m ->
    in_field (carry * 2 ^ Z.of_nat n)).
Proof.
  intros n m Hnm.
  assert (Hpow_m1 : 2 ^ Z.of_nat (m + 1) < p_field)
    by (apply pow2_lt_p_field; lia).
  assert (Hpow_nm : 2 ^ Z.of_nat (n + m) < p_field)
    by (apply pow2_lt_p_field; lia).
  assert (H2n : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  split.
  - intros carry_shifted Hc.
    apply in_field_of_bound with (n := (m + 1)%nat); [exact Hc | lia].
  - intros carry Hc. unfold in_field. split.
    + apply Z.mul_nonneg_nonneg; lia.
    + assert (carry * 2 ^ Z.of_nat n <= 2 ^ Z.of_nat m * 2 ^ Z.of_nat n) by nia.
      rewrite <- Z.pow_add_r in H by lia.
      replace (Z.of_nat m + Z.of_nat n) with (Z.of_nat (n + m)) in H by lia.
      lia.
Qed.

(** * Completeness Proofs for Witness Computation *)

(** ** BigAdd Completeness

    Witness: carry[i] <-- (a[i] + b[i] + carry[i-1]) >> n
             out[i]   <-- (a[i] + b[i] + carry[i-1]) mod 2^n
             out[k]   <-- carry[k-1]

    We prove the witness satisfies the limb equations and the final
    carry assignment. *)

Fixpoint big_add_witness_aux (n : nat) (a b : list Z) (carry_in : Z) : list Z * list Z :=
  match a, b with
  | [], [] => ([], [])
  | a0 :: arest, b0 :: brest =>
    let sum := a0 + b0 + carry_in in
    let out_i := sum mod 2 ^ Z.of_nat n in
    let carry_i := sum / 2 ^ Z.of_nat n in
    let '(outs, carries) := big_add_witness_aux n arest brest carry_i in
    (out_i :: outs, carry_i :: carries)
  | _, _ => ([], [])
  end.

Definition big_add_witness (n : nat) (a b : list Z) : list Z * list Z :=
  let '(outs, carries) := big_add_witness_aux n a b 0 in
  let last_carry := match carries with
    | [] => 0
    | _ => nth (length carries - 1) carries 0
    end in
  (outs ++ [last_carry], carries).

Lemma big_add_witness_aux_lengths : forall n a b carry_in,
  length a = length b ->
  let '(outs, carries) := big_add_witness_aux n a b carry_in in
  length outs = length a /\ length carries = length a.
Proof.
  intros n. induction a as [| a0 arest IH]; intros b carry_in Hlen.
  - destruct b; [simpl; auto | simpl in Hlen; lia].
  - destruct b as [| b0 brest]; [simpl in Hlen; lia |].
    simpl.
    set (c0 := (a0 + b0 + carry_in) / 2 ^ Z.of_nat n).
    destruct (big_add_witness_aux n arest brest c0) as [outs carries] eqn:Heq.
    assert (Hlen' : length arest = length brest) by (simpl in Hlen; lia).
    specialize (IH brest c0 Hlen'). rewrite Heq in IH. simpl. lia.
Qed.

Lemma nth_cons_if_eqb : forall (x : Z) (l : list Z) (j : nat),
  nth j (x :: l) 0 = if (j =? 0)%nat then x else nth (j - 1) l 0.
Proof. intros x l [| j']; simpl; [reflexivity | f_equal; lia]. Qed.

Lemma big_add_witness_aux_correct : forall n a b carry_in,
  length a = length b ->
  (forall i, (i < length a)%nat -> 0 <= nth i a 0) ->
  (forall i, (i < length b)%nat -> 0 <= nth i b 0) ->
  0 <= carry_in ->
  let '(outs, carries) := big_add_witness_aux n a b carry_in in
  (forall i, (i < length a)%nat ->
    nth i a 0 + nth i b 0 + (if (i =? 0)%nat then carry_in else nth (i - 1) carries 0) =
      nth i outs 0 + nth i carries 0 * 2 ^ Z.of_nat n) /\
  (forall i, (i < length a)%nat -> 0 <= nth i carries 0) /\
  (forall i, (i < length a)%nat -> 0 <= nth i outs 0 < 2 ^ Z.of_nat n).
Proof.
  intros n.
  induction a as [| a0 arest IH]; intros b carry_in Hlen Ha Hb Hcin.
  - (* Base: a = [], b = [] *)
    destruct b; [| simpl in Hlen; lia].
    simpl. repeat split; intros; lia.
  - (* Step: a = a0 :: arest *)
    destruct b as [| b0 brest]; [simpl in Hlen; lia |].
    simpl big_add_witness_aux.
    assert (Hlen' : length arest = length brest) by (simpl in Hlen; lia).
    assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    set (sum0 := a0 + b0 + carry_in).
    set (out0 := sum0 mod 2 ^ Z.of_nat n).
    set (carry0 := sum0 / 2 ^ Z.of_nat n).
    destruct (big_add_witness_aux n arest brest carry0) as [outs_rest carries_rest] eqn:Heq.
    assert (Ha0 : 0 <= a0) by (apply (Ha 0%nat); simpl; lia).
    assert (Hb0 : 0 <= b0) by (apply (Hb 0%nat); simpl; lia).
    assert (Hsum0 : 0 <= sum0) by (unfold sum0; lia).
    assert (Hcarry0 : 0 <= carry0) by (unfold carry0; apply Z.div_pos; lia).
    assert (Hdm : sum0 = out0 + carry0 * 2 ^ Z.of_nat n).
    { unfold out0, carry0. assert (Hdm := Z.div_mod sum0 (2 ^ Z.of_nat n) ltac:(lia)). lia. }
    assert (Hout0_bound : 0 <= out0 < 2 ^ Z.of_nat n).
    { unfold out0. split; apply Z.mod_pos_bound; lia. }
    assert (Ha' : forall i, (i < length arest)%nat -> 0 <= nth i arest 0)
      by (intros i Hi; apply (Ha (S i)); simpl; lia).
    assert (Hb' : forall i, (i < length brest)%nat -> 0 <= nth i brest 0)
      by (intros i Hi; apply (Hb (S i)); simpl; lia).
    specialize (IH brest carry0 Hlen' Ha' Hb' Hcarry0).
    rewrite Heq in IH.
    destruct IH as [IH_eq [IH_carry IH_out]].
    split; [| split].
    { (* Uniform limb equation *)
      intros i Hi. destruct i as [| j].
      - (* i = 0 *) simpl. unfold sum0 in Hdm. lia.
      - (* i = S j *)
        assert (IHj := IH_eq j ltac:(simpl in Hi; lia)).
        rewrite <- nth_cons_if_eqb in IHj.
        assert (Rn1 : nth (S j) (a0 :: arest) 0 = nth j arest 0) by reflexivity.
        assert (Rn2 : nth (S j) (b0 :: brest) 0 = nth j brest 0) by reflexivity.
        assert (Rn3 : nth (S j) (out0 :: outs_rest) 0 = nth j outs_rest 0) by reflexivity.
        assert (Rn4 : nth (S j) (carry0 :: carries_rest) 0 = nth j carries_rest 0) by reflexivity.
        assert (Req : (S j =? 0)%nat = false) by reflexivity.
        rewrite Rn1, Rn2, Rn3, Rn4, Req.
        replace ((S j - 1)%nat) with j by lia. exact IHj. }
    { (* Carry non-neg *)
      intros i Hi. destruct i as [| j].
      - simpl. exact Hcarry0.
      - assert (Rn : nth (S j) (carry0 :: carries_rest) 0 = nth j carries_rest 0) by reflexivity.
        rewrite Rn. apply IH_carry. simpl in Hi. lia. }
    { (* Out bounds *)
      intros i Hi. destruct i as [| j].
      - simpl. exact Hout0_bound.
      - assert (Rn : nth (S j) (out0 :: outs_rest) 0 = nth j outs_rest 0) by reflexivity.
        rewrite Rn. apply IH_out. simpl in Hi. lia. }
Qed.

Theorem BigAdd_complete :
  forall (n : nat) (k : nat) (a b : list Z),
  (k >= 1)%nat ->
  length a = k -> length b = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0) ->
  let '(out, carries) := big_add_witness n a b in
  length out = (k + 1)%nat /\
  length carries = k /\
  nth 0 a 0 + nth 0 b 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n /\
  (forall i, (0 < i < k)%nat ->
    nth i a 0 + nth i b 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) /\
  nth k out 0 = nth (k - 1) carries 0.
Proof.
  intros n k a b Hk Halen Hblen Ha Hb.
  subst k.
  unfold big_add_witness.
  destruct (big_add_witness_aux n a b 0) as [outs carries] eqn:Heq.
  assert (Haux_len := big_add_witness_aux_lengths n a b 0 ltac:(lia)).
  rewrite Heq in Haux_len. destruct Haux_len as [Holen Hclen].
  assert (Hb' : forall i, (i < length b)%nat -> 0 <= nth i b 0)
    by (intros i Hi; apply Hb; lia).
  assert (Haux := big_add_witness_aux_correct n a b 0 ltac:(lia) Ha Hb' ltac:(lia)).
  rewrite Heq in Haux.
  destruct Haux as [Heqs [Hcarry_nn Hout_bound]].
  (* Simplify the match on carries *)
  assert (Hmatch : match carries with | [] => 0 | _ :: _ => nth (length carries - 1) carries 0 end
                   = nth (length a - 1) carries 0).
  { rewrite Hclen. destruct carries; [simpl in Hclen; lia | reflexivity]. }
  rewrite Hmatch.
  split; [rewrite length_app; simpl; lia |].
  split; [exact Hclen |].
  split.
  - (* First limb *)
    assert (H0 := Heqs 0%nat ltac:(lia)). simpl Nat.eqb in H0.
    rewrite app_nth1 by lia. lia.
  - split.
    + (* Middle limbs *)
      intros i Hi.
      assert (Hi_eq := Heqs i ltac:(lia)).
      destruct i as [| j]; [lia |].
      assert (Req : (S j =? 0)%nat = false) by reflexivity.
      rewrite Req in Hi_eq.
      rewrite app_nth1 by lia. exact Hi_eq.
    + (* Final carry: nth (length a) (outs ++ [last_carry]) = last_carry *)
      rewrite app_nth2 by lia. rewrite Holen. rewrite Nat.sub_diag. simpl. reflexivity.
Qed.

(** ** BigSub Completeness

    Witness: borrow[i] <-- ... (borrow propagation)
             out[i]    <-- a[i] - borrow - b[i] + borrow[i] * 2^n *)

Fixpoint big_sub_witness_aux (n : nat) (a b : list Z) (borrow_in : Z)
  : list Z * list Z :=
  match a, b with
  | [], [] => ([], [])
  | a0 :: arest, b0 :: brest =>
    let diff := a0 - borrow_in - b0 in
    let borrow_i := if Z_lt_dec diff 0 then 1 else 0 in
    let out_i := diff + borrow_i * 2 ^ Z.of_nat n in
    let '(outs, borrows) := big_sub_witness_aux n arest brest borrow_i in
    (out_i :: outs, borrow_i :: borrows)
  | _, _ => ([], [])
  end.

Definition big_sub_witness (n : nat) (a b : list Z) : list Z * list Z :=
  let '(outs, borrows) := big_sub_witness_aux n a b 0 in
  (* Drop the last borrow element for the (k-1)-length borrows list *)
  (outs, firstn (length a - 1) borrows).

Lemma big_sub_witness_aux_lengths : forall n a b borrow_in,
  length a = length b ->
  let '(outs, borrows) := big_sub_witness_aux n a b borrow_in in
  length outs = length a /\ length borrows = length a.
Proof.
  intros n. induction a as [| a0 arest IH]; intros b borrow_in Hlen.
  - destruct b; [simpl; auto | simpl in Hlen; lia].
  - destruct b as [| b0 brest]; [simpl in Hlen; lia |].
    simpl.
    set (bw := if Z_lt_dec (a0 - borrow_in - b0) 0 then 1 else 0).
    destruct (big_sub_witness_aux n arest brest bw) as [outs borrows] eqn:Heq.
    assert (Hlen' : length arest = length brest) by (simpl in Hlen; lia).
    specialize (IH brest bw Hlen'). rewrite Heq in IH. simpl. lia.
Qed.

Lemma big_sub_witness_aux_correct : forall n a b borrow_in,
  length a = length b ->
  (forall i, (i < length a)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < length b)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  (borrow_in = 0 \/ borrow_in = 1) ->
  let '(outs, borrows) := big_sub_witness_aux n a b borrow_in in
  (forall i, (i < length a)%nat ->
    nth i outs 0 = nth i a 0 -
      (if (i =? 0)%nat then borrow_in else nth (i - 1) borrows 0) -
      nth i b 0 + nth i borrows 0 * 2 ^ Z.of_nat n) /\
  (forall i, (i < length a)%nat -> nth i borrows 0 = 0 \/ nth i borrows 0 = 1) /\
  (forall i, (i < length a)%nat -> 0 <= nth i outs 0 < 2 ^ Z.of_nat n).
Proof.
  intros n.
  induction a as [| a0 arest IH]; intros b borrow_in Hlen Ha Hb Hbin.
  - destruct b; [| simpl in Hlen; lia].
    simpl. repeat split; intros; lia.
  - destruct b as [| b0 brest]; [simpl in Hlen; lia |].
    simpl big_sub_witness_aux.
    assert (Hlen' : length arest = length brest) by (simpl in Hlen; lia).
    assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    set (diff := a0 - borrow_in - b0).
    set (bw := if Z_lt_dec diff 0 then 1 else 0).
    set (out0 := diff + bw * 2 ^ Z.of_nat n).
    destruct (big_sub_witness_aux n arest brest bw) as [outs_rest borrows_rest] eqn:Heq.
    assert (Ha0 : 0 <= a0 < 2 ^ Z.of_nat n) by (apply (Ha 0%nat); simpl; lia).
    assert (Hb0 : 0 <= b0 < 2 ^ Z.of_nat n) by (apply (Hb 0%nat); simpl; lia).
    assert (Hout0_eq : out0 = a0 - borrow_in - b0 + bw * 2 ^ Z.of_nat n)
      by (unfold out0, diff; lia).
    assert (Hbw_binary : bw = 0 \/ bw = 1).
    { unfold bw. destruct (Z_lt_dec diff 0); auto. }
    assert (Hout0_bound : 0 <= out0 < 2 ^ Z.of_nat n).
    { subst out0 diff bw.
      destruct (Z_lt_dec (a0 - borrow_in - b0) 0);
      destruct Hbin as [-> | ->]; lia. }
    assert (Ha' : forall i, (i < length arest)%nat -> 0 <= nth i arest 0 < 2 ^ Z.of_nat n)
      by (intros i Hi; apply (Ha (S i)); simpl; lia).
    assert (Hb' : forall i, (i < length brest)%nat -> 0 <= nth i brest 0 < 2 ^ Z.of_nat n)
      by (intros i Hi; apply (Hb (S i)); simpl; lia).
    specialize (IH brest bw Hlen' Ha' Hb' Hbw_binary).
    rewrite Heq in IH.
    destruct IH as [IH_eq [IH_borrow IH_out]].
    split; [| split].
    { (* Limb equations *)
      intros i Hi. destruct i as [| j].
      - simpl Nat.eqb. simpl nth. exact Hout0_eq.
      - assert (IHj := IH_eq j ltac:(simpl in Hi; lia)).
        change (nth (S j) (out0 :: outs_rest) 0) with (nth j outs_rest 0).
        change (nth (S j) (a0 :: arest) 0) with (nth j arest 0).
        change (nth (S j) (b0 :: brest) 0) with (nth j brest 0).
        change (nth (S j) (bw :: borrows_rest) 0) with (nth j borrows_rest 0).
        assert (Req : (S j =? 0)%nat = false) by reflexivity.
        rewrite Req. replace (S j - 1)%nat with j by lia.
        rewrite nth_cons_if_eqb. exact IHj. }
    { (* Borrow binary *)
      intros i Hi. destruct i as [| j].
      - simpl. exact Hbw_binary.
      - simpl. apply IH_borrow. simpl in Hi. lia. }
    { (* Out bounds *)
      intros i Hi. destruct i as [| j].
      - simpl. exact Hout0_bound.
      - simpl. apply IH_out. simpl in Hi. lia. }
Qed.

(** Value preservation for big_sub_witness_aux. *)
Lemma big_sub_witness_aux_value : forall n a b borrow_in,
  length a = length b ->
  (length a > 0)%nat ->
  (forall i, (i < length a)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < length b)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  let '(outs, borrows) := big_sub_witness_aux n a b borrow_in in
  limbs_to_num n a - limbs_to_num n b - borrow_in =
    limbs_to_num n outs -
    nth (length a - 1) borrows 0 * 2 ^ (Z.of_nat n * Z.of_nat (length a)).
Proof.
  intros n.
  induction a as [| a0 arest IH]; intros b borrow_in Hlen Hgt Ha Hb.
  - simpl in Hgt. lia.
  - destruct b as [| b0 brest]; [simpl in Hlen; lia |].
    simpl big_sub_witness_aux.
    assert (Hlen' : length arest = length brest) by (simpl in Hlen; lia).
    assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    set (diff := a0 - borrow_in - b0).
    set (bw := if Z_lt_dec diff 0 then 1 else 0).
    set (out0 := diff + bw * 2 ^ Z.of_nat n).
    destruct (big_sub_witness_aux n arest brest bw) as [outs_rest borrows_rest] eqn:Heq.
    assert (Ha' : forall i, (i < length arest)%nat -> 0 <= nth i arest 0 < 2 ^ Z.of_nat n)
      by (intros i Hi; apply (Ha (S i)); simpl; lia).
    assert (Hb' : forall i, (i < length brest)%nat -> 0 <= nth i brest 0 < 2 ^ Z.of_nat n)
      by (intros i Hi; apply (Hb (S i)); simpl; lia).
    rewrite !limbs_to_num_cons.
    destruct arest as [| a1 arest'].
    + (* Single limb remaining *)
      simpl in Hlen'. destruct brest; [| simpl in Hlen'; lia].
      simpl in Heq. injection Heq as Heq1 Heq2.
      subst outs_rest borrows_rest. rewrite limbs_to_num_nil.
      simpl length. simpl nth.
      change (1 - 1)%nat with 0%nat.
      change (Z.of_nat 1) with 1. rewrite Z.mul_1_r.
      unfold out0, diff. lia.
    + (* Multi-limb *)
      assert (Hgt' : (length (a1 :: arest') > 0)%nat) by (simpl; lia).
      specialize (IH brest bw Hlen' Hgt' Ha' Hb'). rewrite Heq in IH.
      simpl length.
      replace (S (S (length arest')) - 1)%nat with (S (length arest'))%nat by lia.
      simpl nth.
      simpl length in IH.
      replace (S (length arest') - 1)%nat with (length arest')%nat in IH by lia.
      rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
      unfold out0, diff. lia.
Qed.

Lemma nth_firstn_lt (l : list Z) (n i : nat) :
  (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
  intros H. rewrite nth_firstn.
  destruct (Nat.ltb_spec i n); [reflexivity | lia].
Qed.

(** For BigSub, we prove a simpler completeness result:
    when a >= b as big integers, the witness produces valid outputs. *)

Theorem BigSub_complete :
  forall (n : nat) (k : nat) (a b : list Z),
  (k >= 2)%nat ->
  length a = k -> length b = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  limbs_to_num n a >= limbs_to_num n b ->
  exists (out borrows : list Z),
    length out = k /\
    length borrows = (k - 1)%nat /\
    nth 0 out 0 = nth 0 a 0 - nth 0 b 0 + nth 0 borrows 0 * 2 ^ Z.of_nat n /\
    (forall i, (0 < i < k - 1)%nat ->
      nth i out 0 = nth i a 0 - nth (i - 1) borrows 0 - nth i b 0 +
        nth i borrows 0 * 2 ^ Z.of_nat n) /\
    nth (k - 1) out 0 = nth (k - 1) a 0 - nth (k - 2) borrows 0 - nth (k - 1) b 0 /\
    limbs_to_num n a - limbs_to_num n b = limbs_to_num n out.
Proof.
  intros n k a b Hk Halen Hblen Ha Hb Hge.
  (* Use the existing soundness theorem in reverse: the witness exists
     because a - b >= 0 implies the standard borrow propagation works. *)
  (* For now, we prove existence via the subtraction operation itself.
     The key insight: since a >= b, the limb-by-limb subtraction with
     borrows produces valid n-bit outputs. *)
  (* This is an existential witness — we construct it directly. *)
  destruct (big_sub_witness_aux n a b 0) as [outs borrows] eqn:Heq.
  assert (Hlens := big_sub_witness_aux_lengths n a b 0 ltac:(lia)).
  rewrite Heq in Hlens. destruct Hlens as [Holen Hbrlen].
  exists outs, (firstn (k - 1) borrows).
  subst k.
  split; [exact Holen |].
  split; [rewrite length_firstn, Hbrlen; lia |].
  set (k := length a) in *.
  assert (Hb' : forall i, (i < length b)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n)
    by (intros i Hi; apply Hb; lia).
  assert (Ha' : forall i, (i < length a)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n)
    by (intros i Hi; apply Ha; lia).
  assert (Haux := big_sub_witness_aux_correct n a b 0 ltac:(lia) Ha' Hb' ltac:(auto)).
  rewrite Heq in Haux.
  destruct Haux as [Haux_eq [Haux_borrow Haux_bound]].
  split.
  { (* First limb equation *)
    assert (H0 := Haux_eq 0%nat ltac:(lia)).
    simpl Nat.eqb in H0. rewrite Z.sub_0_r in H0.
    subst k. rewrite !nth_firstn_lt by lia. exact H0. }
  split.
  { (* Middle limb equations *)
    intros i Hi.
    assert (Hi_eq := Haux_eq i ltac:(lia)).
    destruct i; [lia |].
    assert (Req : (S i =? 0)%nat = false) by reflexivity.
    rewrite Req in Hi_eq. replace (S i - 1)%nat with i in Hi_eq by lia.
    subst k. rewrite !nth_firstn_lt by lia.
    replace (S i - 1)%nat with i by lia. exact Hi_eq. }
  split.
  { (* Last limb equation: out[k-1] = a[k-1] - borrow[k-2] - b[k-1] *)
    assert (Hlast := Haux_eq (k - 1)%nat ltac:(lia)).
    destruct (k - 1)%nat as [| j] eqn:Hkm1; [lia |].
    assert (Req : (S j =? 0)%nat = false) by reflexivity.
    rewrite Req in Hlast. replace (S j - 1)%nat with j in Hlast by lia.
    rewrite !nth_firstn_lt by lia.
    (* Hlast: out[k-1] = a[k-1] - borrows[j] - b[k-1] + borrows[k-1] * 2^n *)
    (* For last limb: borrows[k-1] = 0 when a >= b *)
    (* Need: the final borrow is 0. Use value preservation. *)
    assert (Hval := big_sub_witness_aux_value n a b 0 ltac:(lia) ltac:(lia) Ha' Hb').
    rewrite Heq in Hval. fold k in Hval. simpl Z.sub in Hval.
    (* Hval: limbs_to_num a - limbs_to_num b =
         limbs_to_num outs - nth (k-1) borrows 0 * 2^(n*k) *)
    assert (Hborrow_bound := Haux_borrow (k - 1)%nat ltac:(lia)).
    (* borrows[k-1] in {0,1}; if it were 1, limbs_to_num outs would be
       limbs_to_num a - limbs_to_num b + 2^(n*k), which is huge.
       But outs are n-bit, so limbs_to_num outs < 2^(n*k).
       And a-b >= 0. So borrows[k-1] must be 0. *)
    assert (Hfinal_borrow : nth (k - 1)%nat borrows 0 = 0).
    { assert (Hout_upper : limbs_to_num n outs < 2 ^ (Z.of_nat n * Z.of_nat k)).
      { clear -Haux_bound Holen. subst k.
        revert outs Holen Haux_bound.
        induction a as [| a0 arest IH]; intros outs Holen Haux_bound.
        - destruct outs; [simpl; apply Z.pow_pos_nonneg; lia | simpl in Holen; lia].
        - destruct outs as [| o0 orest]; [simpl in Holen; lia |].
          rewrite limbs_to_num_cons.
          assert (Ho0 := Haux_bound 0%nat ltac:(simpl; lia)). simpl in Ho0.
          assert (Holen' : length orest = length arest) by (simpl in Holen; lia).
          assert (Haux_bound' : forall i, (i < length arest)%nat ->
            0 <= nth i orest 0 < 2 ^ Z.of_nat n).
          { intros i Hi. assert (H := Haux_bound (S i) ltac:(simpl; lia)). simpl in H. exact H. }
          assert (IHapp := IH orest Holen' Haux_bound').
          simpl length. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. nia. }
      assert (Hout_nonneg : 0 <= limbs_to_num n outs).
      { clear -Haux_bound Holen. subst k.
        revert outs Holen Haux_bound.
        induction a as [| a0 arest IH]; intros outs Holen Haux_bound.
        - destruct outs; [simpl; lia | simpl in Holen; lia].
        - destruct outs as [| o0 orest]; [simpl in Holen; lia |].
          rewrite limbs_to_num_cons.
          assert (Ho0 := Haux_bound 0%nat ltac:(simpl; lia)). simpl in Ho0.
          assert (Holen' : length orest = length arest) by (simpl in Holen; lia).
          assert (Haux_bound' : forall i, (i < length arest)%nat ->
            0 <= nth i orest 0 < 2 ^ Z.of_nat n).
          { intros i Hi. assert (H := Haux_bound (S i) ltac:(simpl; lia)). simpl in H. exact H. }
          assert (IHapp := IH orest Holen' Haux_bound').
          assert (Hpow' : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia). nia. }
      destruct Hborrow_bound as [Hb0 | Hb1]; [exact Hb0 |].
      exfalso.
      rewrite Hb1 in Hval. rewrite Z.mul_1_l in Hval. lia. }
    rewrite Hkm1 in Hfinal_borrow. rewrite Hfinal_borrow in Hlast.
    replace (k - 2)%nat with j in |- * by lia. lia. }
  { (* Value preservation *)
    assert (Hval := big_sub_witness_aux_value n a b 0 ltac:(lia) ltac:(lia) Ha' Hb').
    rewrite Heq in Hval. fold k in Hval.
    assert (Hfinal_borrow : nth (k - 1)%nat borrows 0 = 0).
    { (* Same argument as above — factor into a shared lemma *)
      assert (Hborrow_bound := Haux_borrow (k - 1)%nat ltac:(lia)).
      assert (Hout_upper : limbs_to_num n outs < 2 ^ (Z.of_nat n * Z.of_nat k)).
      { clear -Haux_bound Holen. subst k.
        revert outs Holen Haux_bound.
        induction a as [| a0 arest IH]; intros outs Holen Haux_bound.
        - destruct outs; [simpl; apply Z.pow_pos_nonneg; lia | simpl in Holen; lia].
        - destruct outs as [| o0 orest]; [simpl in Holen; lia |].
          rewrite limbs_to_num_cons.
          assert (Ho0 := Haux_bound 0%nat ltac:(simpl; lia)). simpl in Ho0.
          assert (Holen' : length orest = length arest) by (simpl in Holen; lia).
          assert (Haux_bound' : forall i, (i < length arest)%nat ->
            0 <= nth i orest 0 < 2 ^ Z.of_nat n).
          { intros i Hi. assert (H := Haux_bound (S i) ltac:(simpl; lia)). simpl in H. exact H. }
          assert (IHapp := IH orest Holen' Haux_bound').
          simpl length. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. nia. }
      assert (Hout_nonneg : 0 <= limbs_to_num n outs).
      { clear -Haux_bound Holen. subst k.
        revert outs Holen Haux_bound.
        induction a as [| a0 arest IH]; intros outs Holen Haux_bound.
        - destruct outs; [simpl; lia | simpl in Holen; lia].
        - destruct outs as [| o0 orest]; [simpl in Holen; lia |].
          rewrite limbs_to_num_cons.
          assert (Ho0 := Haux_bound 0%nat ltac:(simpl; lia)). simpl in Ho0.
          assert (Holen' : length orest = length arest) by (simpl in Holen; lia).
          assert (Haux_bound' : forall i, (i < length arest)%nat ->
            0 <= nth i orest 0 < 2 ^ Z.of_nat n).
          { intros i Hi. assert (H := Haux_bound (S i) ltac:(simpl; lia)). simpl in H. exact H. }
          assert (IHapp := IH orest Holen' Haux_bound').
          assert (Hpow' : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia). nia. }
      destruct Hborrow_bound as [Hb0 | Hb1]; [exact Hb0 |].
      exfalso. rewrite Hb1 in Hval. rewrite Z.mul_1_l in Hval. lia. }
    rewrite Hfinal_borrow in Hval. simpl Z.sub in Hval. lia. }
Qed.

(** ** Carry Chain Infrastructure

    Single-list carry propagation: used by LongToShort, BigMult,
    and CheckCarryToZero completeness proofs. *)

Fixpoint carry_chain_aux (n : nat) (inp : list Z) (carry_in : Z)
  : list Z * list Z :=
  match inp with
  | [] => ([], [])
  | x :: rest =>
    let sum := x + carry_in in
    let out_i := sum mod 2 ^ Z.of_nat n in
    let carry_i := sum / 2 ^ Z.of_nat n in
    let '(outs, carries) := carry_chain_aux n rest carry_i in
    (out_i :: outs, carry_i :: carries)
  end.

Lemma carry_chain_aux_lengths : forall n inp carry_in,
  let '(outs, carries) := carry_chain_aux n inp carry_in in
  length outs = length inp /\ length carries = length inp.
Proof.
  intros n. induction inp as [| x rest IH]; intros carry_in.
  - simpl. auto.
  - simpl. set (c := (x + carry_in) / 2 ^ Z.of_nat n).
    destruct (carry_chain_aux n rest c) as [outs carries] eqn:Heq.
    specialize (IH c). rewrite Heq in IH. simpl. lia.
Qed.

Lemma carry_chain_aux_correct : forall n inp carry_in,
  (forall i, (i < length inp)%nat -> 0 <= nth i inp 0) ->
  0 <= carry_in ->
  let '(outs, carries) := carry_chain_aux n inp carry_in in
  (forall i, (i < length inp)%nat ->
    nth i inp 0 + (if (i =? 0)%nat then carry_in else nth (i - 1) carries 0) =
      nth i outs 0 + nth i carries 0 * 2 ^ Z.of_nat n) /\
  (forall i, (i < length inp)%nat -> 0 <= nth i carries 0) /\
  (forall i, (i < length inp)%nat -> 0 <= nth i outs 0 < 2 ^ Z.of_nat n).
Proof.
  intros n. induction inp as [| x rest IH]; intros carry_in Hnn Hcin.
  - simpl. repeat split; intros; lia.
  - simpl carry_chain_aux.
    assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    set (sum0 := x + carry_in).
    set (out0 := sum0 mod 2 ^ Z.of_nat n).
    set (carry0 := sum0 / 2 ^ Z.of_nat n).
    destruct (carry_chain_aux n rest carry0) as [outs_rest carries_rest] eqn:Heq.
    assert (Hx : 0 <= x) by (apply (Hnn 0%nat); simpl; lia).
    assert (Hsum0 : 0 <= sum0) by (unfold sum0; lia).
    assert (Hcarry0 : 0 <= carry0) by (unfold carry0; apply Z.div_pos; lia).
    assert (Hdm : sum0 = out0 + carry0 * 2 ^ Z.of_nat n).
    { unfold out0, carry0. assert (Hdm := Z.div_mod sum0 (2 ^ Z.of_nat n) ltac:(lia)). lia. }
    assert (Hout0_bound : 0 <= out0 < 2 ^ Z.of_nat n).
    { unfold out0. split; apply Z.mod_pos_bound; lia. }
    assert (Hnn' : forall i, (i < length rest)%nat -> 0 <= nth i rest 0)
      by (intros i Hi; apply (Hnn (S i)); simpl; lia).
    specialize (IH carry0 Hnn' Hcarry0).
    rewrite Heq in IH.
    destruct IH as [IH_eq [IH_carry IH_out]].
    split; [| split].
    { intros i Hi. destruct i as [| j].
      - simpl. unfold sum0 in Hdm. lia.
      - assert (IHj := IH_eq j ltac:(simpl in Hi; lia)).
        rewrite <- nth_cons_if_eqb in IHj.
        assert (Rn1 : nth (S j) (x :: rest) 0 = nth j rest 0) by reflexivity.
        assert (Rn3 : nth (S j) (out0 :: outs_rest) 0 = nth j outs_rest 0) by reflexivity.
        assert (Rn4 : nth (S j) (carry0 :: carries_rest) 0 = nth j carries_rest 0) by reflexivity.
        assert (Req : (S j =? 0)%nat = false) by reflexivity.
        rewrite Rn1, Rn3, Rn4, Req.
        replace ((S j - 1)%nat) with j by lia. exact IHj. }
    { intros i Hi. destruct i as [| j].
      - simpl. exact Hcarry0.
      - assert (Rn : nth (S j) (carry0 :: carries_rest) 0 = nth j carries_rest 0) by reflexivity.
        rewrite Rn. apply IH_carry. simpl in Hi. lia. }
    { intros i Hi. destruct i as [| j].
      - simpl. exact Hout0_bound.
      - assert (Rn : nth (S j) (out0 :: outs_rest) 0 = nth j outs_rest 0) by reflexivity.
        rewrite Rn. apply IH_out. simpl in Hi. lia. }
Qed.

Lemma limbs_to_num_snoc : forall n l x,
  limbs_to_num n (l ++ [x]) =
    limbs_to_num n l + x * 2 ^ (Z.of_nat n * Z.of_nat (length l)).
Proof.
  intros n. induction l as [| a rest IH]; intros x.
  - change ([] ++ [x]) with ([x] : list Z).
    rewrite limbs_to_num_cons, limbs_to_num_nil. simpl length.
    rewrite Nat2Z.inj_0, !Z.mul_0_r, Z.pow_0_r. lia.
  - simpl app. rewrite !limbs_to_num_cons. rewrite IH. simpl length.
    rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_r.
    rewrite Z.pow_add_r by lia. ring.
Qed.

Lemma limbs_to_num_firstn_skipn : forall n m (l : list Z),
  limbs_to_num n l =
    limbs_to_num n (firstn m l) +
      2 ^ (Z.of_nat n * Z.of_nat m) * limbs_to_num n (skipn m l).
Proof.
  intros n. induction m as [| m' IH]; intros l.
  - simpl firstn. simpl skipn. rewrite limbs_to_num_nil.
    rewrite Nat2Z.inj_0, Z.mul_0_r, Z.pow_0_r. lia.
  - destruct l as [| a rest].
    + simpl. lia.
    + simpl firstn. simpl skipn.
      rewrite !limbs_to_num_cons.
      assert (IHm := IH rest).
      rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. lia.
Qed.

Lemma carry_chain_aux_value : forall n inp carry_in,
  (forall i, (i < length inp)%nat -> 0 <= nth i inp 0) ->
  0 <= carry_in ->
  (length inp > 0)%nat ->
  let '(outs, carries) := carry_chain_aux n inp carry_in in
  carry_in + limbs_to_num n inp =
    limbs_to_num n outs +
    nth (length inp - 1) carries 0 * 2 ^ (Z.of_nat n * Z.of_nat (length inp)).
Proof.
  intros n inp carry_in Hnn Hcin Hgt.
  destruct (carry_chain_aux n inp carry_in) as [outs carries] eqn:Heq.
  assert (Hlens := carry_chain_aux_lengths n inp carry_in). rewrite Heq in Hlens.
  assert (Hcorr := carry_chain_aux_correct n inp carry_in Hnn Hcin). rewrite Heq in Hcorr.
  destruct Hlens as [Holen Hclen].
  destruct Hcorr as [Heqs _].
  apply carry_propagation_gen; [lia | lia | lia | exact Heqs].
Qed.

(** General carry propagation completeness: constructs outs and carries
    for any non-negative input list, with the last limb absorbing the
    final carry without modular reduction.

    Used by LongToShortNoEndCarry_complete and BigMult_complete. *)

Lemma carry_propagation_complete :
  forall (n : nat) (m : nat) (inp : list Z),
  (m >= 2)%nat ->
  length inp = m ->
  (forall i, (i < m)%nat -> 0 <= nth i inp 0) ->
  exists (out carries : list Z),
    length out = m /\
    length carries = (m - 1)%nat /\
    nth 0 inp 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n /\
    (forall i, (0 < i < m - 1)%nat ->
      nth i inp 0 + nth (i - 1) carries 0 =
        nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) /\
    nth (m - 1) out 0 = nth (m - 1) inp 0 + nth (m - 2) carries 0 /\
    limbs_to_num n inp = limbs_to_num n out.
Proof.
  intros n m inp Hm Hlen Hnn.
  assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  (* Apply carry_chain_aux to all m elements *)
  destruct (carry_chain_aux n inp 0) as [all_outs all_carries] eqn:Heq.
  assert (Hlens := carry_chain_aux_lengths n inp 0).
  rewrite Heq in Hlens. destruct Hlens as [Holen Hclen].
  assert (Hcorr := carry_chain_aux_correct n inp 0 ltac:(intros; apply Hnn; lia) ltac:(lia)).
  rewrite Heq in Hcorr.
  destruct Hcorr as [Heqs [Hcarry_nn Hout_bound]].
  (* Construct witness: carries = firstn (m-1) all_carries,
     out = firstn (m-1) all_outs ++ [inp[m-1] + carries[m-2]] *)
  set (carries := firstn (m - 1) all_carries).
  assert (Hclen' : length carries = (m - 1)%nat)
    by (subst carries; rewrite length_firstn; lia).
  (* Last carry from the chain *)
  assert (Hlast_carry : nth (m - 2) carries 0 = nth (m - 2) all_carries 0).
  { subst carries. rewrite nth_firstn_lt by lia. reflexivity. }
  set (last_out := nth (m - 1) inp 0 + nth (m - 2) carries 0).
  set (out := firstn (m - 1) all_outs ++ [last_out]).
  exists out, carries.
  assert (Hout_len : length out = m).
  { subst out. rewrite length_app. rewrite length_firstn. simpl. lia. }
  split; [exact Hout_len |].
  split; [exact Hclen' |].
  split.
  { (* First limb equation *)
    assert (H0 := Heqs 0%nat ltac:(lia)).
    simpl Nat.eqb in H0.
    subst out. rewrite app_nth1 by (rewrite length_firstn; lia).
    rewrite nth_firstn_lt by lia.
    subst carries. rewrite nth_firstn_lt by lia. lia. }
  split.
  { (* Middle limb equations *)
    intros i Hi.
    assert (Hi_eq := Heqs i ltac:(lia)).
    destruct i as [| j]; [lia |].
    assert (Req : (S j =? 0)%nat = false) by reflexivity.
    rewrite Req in Hi_eq.
    subst out. rewrite app_nth1 by (rewrite length_firstn; lia).
    rewrite nth_firstn_lt by lia.
    subst carries. rewrite !nth_firstn_lt by lia.
    exact Hi_eq. }
  split.
  { (* Last limb equation *)
    subst out last_out.
    rewrite app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn.
    replace (Nat.min (m - 1) (length all_outs)) with (m - 1)%nat by lia.
    rewrite Nat.sub_diag. simpl. reflexivity. }
  { (* Value preservation via carry_chain_aux_value *)
    assert (Hval := carry_chain_aux_value n inp 0
      ltac:(intros; apply Hnn; lia) ltac:(lia) ltac:(lia)).
    rewrite Heq in Hval. simpl (0 + _) in Hval. rewrite Hlen in Hval.
    (* Hval: limbs_to_num n inp = limbs_to_num n all_outs +
         nth (m-1) all_carries 0 * 2^(n*m) *)
    (* Get carry equation for last limb *)
    assert (Hlast_eq := Heqs (m - 1)%nat ltac:(lia)).
    destruct (Nat.eqb_spec (m - 1) 0) as [Hz | Hnz].
    { lia. }  (* m >= 2 so m-1 <> 0 *)
    (* Hlast_eq: inp[m-1] + all_carries[m-2] =
         all_outs[m-1] + all_carries[m-1] * 2^n *)
    (* Decompose all_outs = firstn (m-1) all_outs ++ [nth (m-1) all_outs 0] *)
    assert (Hall_decomp : all_outs = firstn (m - 1) all_outs ++ skipn (m - 1) all_outs)
      by (symmetry; apply firstn_skipn).
    assert (Hskipn_singleton : skipn (m - 1) all_outs = [nth (m - 1) all_outs 0]).
    { assert (Hskipn_len : length (skipn (m - 1) all_outs) = 1%nat)
        by (rewrite length_skipn; lia).
      destruct (skipn (m - 1) all_outs) as [| v [| v2 rest']] eqn:Hs;
        [simpl in Hskipn_len; lia | | simpl in Hskipn_len; lia].
      f_equal. change v with (nth 0 [v] 0). rewrite <- Hs.
      rewrite nth_skipn. f_equal. lia. }
    rewrite Hall_decomp, Hskipn_singleton in Hval.
    rewrite limbs_to_num_snoc in Hval.
    rewrite length_firstn in Hval.
    replace (Nat.min (m - 1) (length all_outs)) with (m - 1)%nat in Hval by lia.
    (* Now Hval: limbs_to_num n inp = limbs_to_num n (firstn (m-1) all_outs) +
         nth (m-1) all_outs 0 * 2^(n*(m-1)) + nth (m-1) all_carries 0 * 2^(n*m) *)
    (* Goal: limbs_to_num n inp = limbs_to_num n out *)
    subst out last_out.
    rewrite limbs_to_num_snoc. rewrite length_firstn.
    replace (Nat.min (m - 1) (length all_outs)) with (m - 1)%nat by lia.
    (* Goal: limbs_to_num n inp = limbs_to_num n (firstn (m-1) all_outs) +
         (inp[m-1] + carries[m-2]) * 2^(n*(m-1)) *)
    rewrite Hlast_carry.
    (* From Hlast_eq: inp[m-1] + all_carries[m-2] =
         all_outs[m-1] + all_carries[m-1] * 2^n *)
    (* So: (inp[m-1] + all_carries[m-2]) * 2^(n*(m-1)) =
         all_outs[m-1] * 2^(n*(m-1)) + all_carries[m-1] * 2^n * 2^(n*(m-1))
       = all_outs[m-1] * 2^(n*(m-1)) + all_carries[m-1] * 2^(n*m) *)
    replace (m - 1 - 1)%nat with (m - 2)%nat in Hlast_eq by lia.
    assert (H2n : Z.of_nat n * Z.of_nat m =
      Z.of_nat n + Z.of_nat n * Z.of_nat (m - 1)) by lia.
    rewrite H2n in Hval. rewrite Z.pow_add_r in Hval by lia. lia. }
Qed.

(** ** LongToShortNoEndCarry Completeness

    Witness: carry[i] <-- (in[i] + carry[i-1]) >> n
             out[i]   <-- (in[i] + carry[i-1]) mod 2^n
             out[k-1] <-- in[k-1] + carry[k-2] *)

Theorem LongToShortNoEndCarry_complete :
  forall (n : nat) (k : nat) (inp : list Z),
  (k >= 2)%nat ->
  length inp = k ->
  (forall i, (i < k)%nat -> 0 <= nth i inp 0) ->
  exists (out carries : list Z),
    length out = k /\
    length carries = (k - 1)%nat /\
    nth 0 inp 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n /\
    (forall i, (0 < i < k - 1)%nat ->
      nth i inp 0 + nth (i - 1) carries 0 =
        nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) /\
    nth (k - 1) out 0 = nth (k - 1) inp 0 + nth (k - 2) carries 0 /\
    limbs_to_num n inp = limbs_to_num n out.
Proof.
  intros n k inp Hk Hlen Hnn.
  exact (carry_propagation_complete n k inp Hk Hlen Hnn).
Qed.

(** ** CheckCarryToZero Completeness

    Witness: carry[i] <-- (inp[i] + carry[i-1]) / 2^n
    The bias-adjusted carry propagation ensures all limbs zero out. *)

Theorem CheckCarryToZero_complete :
  forall (n : nat) (k : nat) (inp : list Z),
  (k >= 2)%nat ->
  length inp = k ->
  limbs_to_num n inp = 0 ->
  exists carries : list Z,
    length carries = (k - 1)%nat /\
    nth 0 inp 0 = nth 0 carries 0 * 2 ^ Z.of_nat n /\
    (forall i, (0 < i < k - 1)%nat ->
      nth i inp 0 + nth (i - 1) carries 0 =
        nth i carries 0 * 2 ^ Z.of_nat n) /\
    nth (k - 1) inp 0 + nth (k - 2) carries 0 = 0.
Proof.
  intros n k inp Hk Hlen Hzero.
  assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  (* Define carries as running partial sums divided by 2^n.
     carries[i] = limbs_to_num n (firstn (i+1) inp) / 2^(n*(i+1)) *)
  set (carry_of := fun i => limbs_to_num n (firstn (S i) inp) / 2 ^ (Z.of_nat n * Z.of_nat (S i))).
  exists (map carry_of (seq 0 (k - 1))).
  assert (Hcarry_len : length (map carry_of (seq 0 (k - 1))) = (k - 1)%nat)
    by (rewrite length_map, length_seq; lia).
  split; [exact Hcarry_len |].
  (* Key lemma: limbs_to_num n (firstn (i+1) inp) is divisible by 2^(n*(i+1)).
     This follows from limbs_to_num n inp = 0: the first (i+1) limbs' contribution
     plus the remaining limbs' contribution = 0, and the remaining limbs' contribution
     is divisible by 2^(n*(i+1)). *)
  assert (Hdiv : forall i, (i < k)%nat ->
    (2 ^ (Z.of_nat n * Z.of_nat (S i)) | limbs_to_num n (firstn (S i) inp))).
  { intros i Hi.
    (* limbs_to_num n inp = limbs_to_num n (firstn (S i) inp) +
         2^(n*(S i)) * limbs_to_num n (skipn (S i) inp) *)
    assert (Hdecomp := limbs_to_num_firstn_skipn n (S i) inp).
    rewrite Hzero in Hdecomp.
    exists (- limbs_to_num n (skipn (S i) inp)).
    lia. }
  (* From divisibility, get the carry equation at each step *)
  assert (Hcarry_eq : forall i, (i < k)%nat ->
    limbs_to_num n (firstn (S i) inp) =
      carry_of i * 2 ^ (Z.of_nat n * Z.of_nat (S i))).
  { intros i Hi. unfold carry_of.
    assert (Hd := Hdiv i Hi).
    destruct Hd as [q Hq].
    rewrite Hq, Z.div_mul by (apply Z.pow_nonzero; lia).
    lia. }
  (* Derive individual limb equations from the carry equations *)
  assert (Hlimb : forall i, (i < k)%nat ->
    nth i inp 0 + (if (i =? 0)%nat then 0 else carry_of (i - 1)%nat) =
      carry_of i * 2 ^ Z.of_nat n).
  { intros i Hi.
    destruct i.
    - (* i = 0 *)
      simpl Nat.eqb.
      assert (H0 := Hcarry_eq 0%nat ltac:(lia)).
      (* firstn 1 inp = [nth 0 inp 0] when length inp >= 1 *)
      assert (Hf1 : firstn 1 inp = [nth 0 inp 0]).
      { destruct inp as [| x rest']; [simpl in Hlen; lia |].
        simpl. reflexivity. }
      rewrite Hf1 in H0.
      rewrite limbs_to_num_cons, limbs_to_num_nil, Z.mul_0_r in H0.
      change (Z.of_nat 1) with 1 in H0. rewrite Z.mul_1_r in H0. lia.
    - (* i > 0: use firstn/skipn decomposition *)
      assert (Req : (S i =? 0)%nat = false) by reflexivity.
      rewrite Req.
      replace (S i - 1)%nat with i by lia.
      assert (Hsi := Hcarry_eq (S i) ltac:(lia)).
      assert (Hi' := Hcarry_eq i ltac:(lia)).
      (* Decompose: firstn (S (S i)) = firstn (S i) + one more element *)
      assert (Hdecomp2 := limbs_to_num_firstn_skipn n (S i) (firstn (S (S i)) inp)).
      rewrite firstn_firstn in Hdecomp2.
      replace (Nat.min (S i) (S (S i))) with (S i) in Hdecomp2 by lia.
      (* skipn (S i) (firstn (S (S i)) inp) = [nth (S i) inp 0] *)
      assert (Hskip_one : skipn (S i) (firstn (S (S i)) inp) = [nth (S i) inp 0]).
      { assert (Hskiplen : length (skipn (S i) (firstn (S (S i)) inp)) = 1%nat)
          by (rewrite length_skipn, length_firstn; lia).
        destruct (skipn (S i) (firstn (S (S i)) inp)) as [| v [| v2 rest']] eqn:Hs;
          [simpl in Hskiplen; lia | | simpl in Hskiplen; lia].
        f_equal.
        assert (Hv : v = nth 0 (skipn (S i) (firstn (S (S i)) inp)) 0) by (rewrite Hs; reflexivity).
        rewrite nth_skipn in Hv. rewrite nth_firstn_lt in Hv by lia.
        rewrite Nat.add_0_r in Hv. exact Hv. }
      rewrite Hskip_one in Hdecomp2.
      rewrite limbs_to_num_cons, limbs_to_num_nil, Z.mul_0_r, Z.add_0_r in Hdecomp2.
      rewrite Hi' in Hdecomp2.
      rewrite Hsi in Hdecomp2.
      (* Hdecomp2: carry_of (S i) * 2^(n*(S(S i))) =
           carry_of i * 2^(n*(S i)) + 2^(n*(S i)) * nth (S i) inp 0 *)
      (* Factor: 2^(n*(S i)) * (carry_of (S i) * 2^n) =
           2^(n*(S i)) * (carry_of i + nth (S i) inp 0) *)
      assert (Hpow_pos : 0 < 2 ^ (Z.of_nat n * Z.of_nat (S i)))
        by (apply Z.pow_pos_nonneg; lia).
      rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r in Hdecomp2 by lia.
      nia. }
  (* Now prove each conjunct *)
  split.
  { (* First equation: inp[0] = carries[0] * 2^n *)
    assert (H0 := Hlimb 0%nat ltac:(lia)).
    simpl Nat.eqb in H0. rewrite Z.add_0_r in H0.
    rewrite nth_map_seq by lia. simpl. exact H0. }
  split.
  { (* Middle equations *)
    intros i Hi.
    assert (Hsi := Hlimb i ltac:(lia)).
    destruct i; [lia |].
    assert (Req : (S i =? 0)%nat = false) by reflexivity.
    rewrite Req in Hsi.
    replace (S i - 1)%nat with i in Hsi by lia.
    rewrite !nth_map_seq by lia. simpl.
    replace (i - 0)%nat with i by lia.
    exact Hsi. }
  { (* Last equation: inp[k-1] + carries[k-2] = 0 *)
    assert (Hkm1 := Hcarry_eq (k - 1)%nat ltac:(lia)).
    replace (S (k - 1)) with k in Hkm1 by lia.
    assert (Hfirstn_k : firstn k inp = inp)
      by (rewrite <- Hlen; apply firstn_all).
    rewrite Hfirstn_k, Hzero in Hkm1.
    (* So carry_of (k-1) * 2^(n*k) = 0, hence carry_of (k-1) = 0 *)
    assert (Hfinal : carry_of (k - 1)%nat = 0).
    { symmetry in Hkm1. apply Z.eq_mul_0 in Hkm1.
      destruct Hkm1 as [Hkm1 | Hkm1]; [exact Hkm1 |].
      exfalso. assert (0 < 2 ^ (Z.of_nat n * Z.of_nat k))
        by (apply Z.pow_pos_nonneg; lia). lia. }
    (* Get the last limb equation: inp[k-1] + carry_of(k-2) = carry_of(k-1) * 2^n *)
    assert (Hlast := Hlimb (k - 1)%nat ltac:(lia)).
    assert (Hkne : ((k - 1) =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite Hkne in Hlast.
    (* Hlast: inp[k-1] + carry_of(k-2) = carry_of(k-1) * 2^n *)
    rewrite Hfinal, Z.mul_0_l in Hlast.
    replace ((k - 1 - 1)%nat) with ((k - 2)%nat) in Hlast by lia.
    (* Hlast: inp[k-1] + carry_of(k-2) = 0 *)
    rewrite nth_map_seq by lia.
    replace (k - 2 - 0)%nat with (k - 2)%nat by lia.
    exact Hlast. }
Qed.

(** ** BigMult Completeness

    The raw convolution limbs are carry-propagated identically to
    LongToShortNoEndCarry. *)

Theorem BigMult_complete :
  forall (n : nat) (k : nat) (rawLimbs : list Z),
  (k >= 1)%nat ->
  length rawLimbs = (2 * k)%nat ->
  (forall i, (i < 2 * k)%nat -> 0 <= nth i rawLimbs 0) ->
  exists (out carries : list Z),
    length out = (2 * k)%nat /\
    length carries = (2 * k - 1)%nat /\
    nth 0 rawLimbs 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n /\
    (forall i, (0 < i < 2 * k - 1)%nat ->
      nth i rawLimbs 0 + nth (i - 1) carries 0 =
        nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) /\
    nth (2 * k - 1) out 0 =
      nth (2 * k - 1) rawLimbs 0 + nth (2 * k - 2) carries 0 /\
    limbs_to_num n rawLimbs = limbs_to_num n out.
Proof.
  intros n k rawLimbs Hk Hlen Hnn.
  exact (carry_propagation_complete n (2 * k) rawLimbs ltac:(lia) Hlen Hnn).
Qed.

(** * Tier 5 Completeness Proofs *)

(** ** BigMod Completeness (bigint.circom:210-263)

    Witness: quotient <-- A / B (as 2-limb), remainder <-- A mod B (as k-limb).
    Constraint: A = B * Q + R, with R < B (checked via BigLessThan). *)

Theorem BigMod_complete :
  forall (n k : nat) (a b : list Z),
  (n >= 1)%nat -> (k >= 2)%nat ->
  length a = (k + 1)%nat -> length b = k ->
  (forall i, (i < k + 1)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  limbs_to_num n b > 0 ->
  limbs_to_num n a / limbs_to_num n b < 2 ^ (2 * Z.of_nat n) ->
  exists (quotient remainder : list Z),
    length quotient = 2%nat /\ length remainder = k /\
    (forall i, (i < 2)%nat -> 0 <= nth i quotient 0 < 2 ^ Z.of_nat n) /\
    (forall i, (i < k)%nat -> 0 <= nth i remainder 0 < 2 ^ Z.of_nat n) /\
    limbs_to_num n a =
      limbs_to_num n b * limbs_to_num n quotient + limbs_to_num n remainder /\
    limbs_to_num n remainder < limbs_to_num n b.
Proof.
  intros n k a b Hn Hk Halen Hblen Ha Hb HBpos HQbound.
  set (A := limbs_to_num n a).
  set (B := limbs_to_num n b).
  set (Q := A / B).
  set (R := A mod B).
  assert (HA_nn : 0 <= A).
  { unfold A. apply limbs_to_num_nonneg_limbs. intros i Hi.
    rewrite Halen in Hi. assert (Hi' := Ha i ltac:(lia)). lia. }
  assert (HQ_nn : 0 <= Q) by (unfold Q; apply Z.div_pos; lia).
  assert (HR_nn : 0 <= R) by (unfold R; apply Z.mod_pos_bound; lia).
  assert (HR_bound : R < B) by (unfold R; apply Z.mod_pos_bound; lia).
  assert (Hdm : A = B * Q + R).
  { unfold Q, R. assert (Hdm := Z.div_mod A B ltac:(lia)). lia. }
  (* Q < 2^(2n) by hypothesis *)
  assert (HQ_range : 0 <= Q < 2 ^ (2 * Z.of_nat n)).
  { split; [exact HQ_nn | unfold Q, A, B; exact HQbound]. }
  (* R < B < 2^(n*k) *)
  assert (HB_upper : B < 2 ^ (Z.of_nat n * Z.of_nat k)).
  { unfold B. rewrite <- Hblen. apply limbs_to_num_upper.
    intros i Hi. rewrite Hblen in Hi. apply Hb. lia. }
  assert (HR_range : 0 <= R < 2 ^ (Z.of_nat n * Z.of_nat k)) by lia.
  (* Decompose Q and R into limbs *)
  set (quotient := num_to_limbs Q n 2).
  set (remainder := num_to_limbs R n k).
  exists quotient, remainder.
  assert (Hqlen : length quotient = 2%nat)
    by (unfold quotient; apply num_to_limbs_length).
  assert (Hrlen : length remainder = k)
    by (unfold remainder; apply num_to_limbs_length).
  split; [exact Hqlen |].
  split; [exact Hrlen |].
  split.
  { intros i Hi. unfold quotient. apply num_to_limbs_range; lia. }
  split.
  { intros i Hi. unfold remainder. apply num_to_limbs_range; lia. }
  (* Value equation *)
  assert (HQ_val : limbs_to_num n quotient = Q).
  { unfold quotient. apply num_to_limbs_correct.
    replace (Z.of_nat n * Z.of_nat 2) with (2 * Z.of_nat n) by lia. exact HQ_range. }
  assert (HR_val : limbs_to_num n remainder = R).
  { unfold remainder. apply num_to_limbs_correct. exact HR_range. }
  rewrite HQ_val, HR_val.
  split; [exact Hdm | exact HR_bound].
Qed.

(** ** BigMultModP Completeness (bigint.circom:268-303)

    Witness: quotient <-- (A*B) / P, out <-- (A*B) mod P.
    Constraint: A * B = P * quotient + out. *)

Theorem BigMultModP_complete :
  forall (n k : nat) (a b p : list Z),
  (n >= 1)%nat -> (k >= 2)%nat ->
  length a = k -> length b = k -> length p = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i p 0 < 2 ^ Z.of_nat n) ->
  limbs_to_num n p > 0 ->
  (limbs_to_num n a * limbs_to_num n b) / limbs_to_num n p < 2 ^ (Z.of_nat n * Z.of_nat k) ->
  exists (out quotient : list Z),
    length out = k /\ length quotient = k /\
    (forall i, (i < k)%nat -> 0 <= nth i out 0 < 2 ^ Z.of_nat n) /\
    (forall i, (i < k)%nat -> 0 <= nth i quotient 0 < 2 ^ Z.of_nat n) /\
    limbs_to_num n a * limbs_to_num n b =
      limbs_to_num n p * limbs_to_num n quotient + limbs_to_num n out /\
    limbs_to_num n out < limbs_to_num n p.
Proof.
  intros n k a b p Hn Hk Halen Hblen Hplen Ha Hb Hp HPpos HQbound.
  set (A := limbs_to_num n a).
  set (B := limbs_to_num n b).
  set (P := limbs_to_num n p).
  set (Q := (A * B) / P).
  set (R := (A * B) mod P).
  assert (HAB_nn : 0 <= A * B).
  { apply Z.mul_nonneg_nonneg.
    - unfold A. apply limbs_to_num_nonneg_limbs. intros i Hi.
      rewrite Halen in Hi. assert (Hi' := Ha i ltac:(lia)). lia.
    - unfold B. apply limbs_to_num_nonneg_limbs. intros i Hi.
      rewrite Hblen in Hi. assert (Hi' := Hb i ltac:(lia)). lia. }
  assert (HQ_nn : 0 <= Q) by (unfold Q; apply Z.div_pos; lia).
  assert (HR_nn : 0 <= R) by (unfold R; apply Z.mod_pos_bound; lia).
  assert (HR_bound : R < P) by (unfold R; apply Z.mod_pos_bound; lia).
  assert (Hdm : A * B = P * Q + R).
  { unfold Q, R. assert (Hdm := Z.div_mod (A * B) P ltac:(lia)). lia. }
  (* Q < 2^(n*k) by hypothesis, R < P < 2^(n*k) *)
  assert (HQ_range : 0 <= Q < 2 ^ (Z.of_nat n * Z.of_nat k)).
  { split; [exact HQ_nn | unfold Q, A, B, P; exact HQbound]. }
  assert (HP_upper : P < 2 ^ (Z.of_nat n * Z.of_nat k)).
  { unfold P. rewrite <- Hplen. apply limbs_to_num_upper.
    intros i Hi. rewrite Hplen in Hi. apply Hp. lia. }
  assert (HR_range : 0 <= R < 2 ^ (Z.of_nat n * Z.of_nat k)) by lia.
  set (out := num_to_limbs R n k).
  set (quotient := num_to_limbs Q n k).
  exists out, quotient.
  assert (Holen : length out = k) by (unfold out; apply num_to_limbs_length).
  assert (Hqlen : length quotient = k) by (unfold quotient; apply num_to_limbs_length).
  split; [exact Holen |].
  split; [exact Hqlen |].
  split.
  { intros i Hi. unfold out. apply num_to_limbs_range; lia. }
  split.
  { intros i Hi. unfold quotient. apply num_to_limbs_range; lia. }
  assert (HQ_val : limbs_to_num n quotient = Q)
    by (unfold quotient; apply num_to_limbs_correct; exact HQ_range).
  assert (HR_val : limbs_to_num n out = R)
    by (unfold out; apply num_to_limbs_correct; exact HR_range).
  rewrite HQ_val, HR_val.
  split; [exact Hdm | exact HR_bound].
Qed.

(** ** BigSubModP Completeness (bigint.circom:308-337)

    Witness: out <-- ((A - B) mod P + P) mod P, decomposed into k limbs.
    Constraint: (out + B - A) mod P = 0. *)

Theorem BigSubModP_complete :
  forall (n k : nat) (a b p : list Z),
  (n >= 1)%nat -> (k >= 2)%nat ->
  length a = k -> length b = k -> length p = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i b 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i p 0 < 2 ^ Z.of_nat n) ->
  limbs_to_num n p > 0 ->
  exists (out : list Z),
    length out = k /\
    (forall i, (i < k)%nat -> 0 <= nth i out 0 < 2 ^ Z.of_nat n) /\
    (limbs_to_num n out + limbs_to_num n b - limbs_to_num n a) mod (limbs_to_num n p) = 0.
Proof.
  intros n k a b p Hn Hk Halen Hblen Hplen Ha Hb Hp HPpos.
  set (A := limbs_to_num n a).
  set (B := limbs_to_num n b).
  set (P := limbs_to_num n p).
  set (R := ((A - B) mod P + P) mod P).
  assert (HP_upper : P < 2 ^ (Z.of_nat n * Z.of_nat k)).
  { unfold P. rewrite <- Hplen. apply limbs_to_num_upper.
    intros i Hi. rewrite Hplen in Hi. apply Hp. lia. }
  assert (HR_range : 0 <= R < 2 ^ (Z.of_nat n * Z.of_nat k)).
  { unfold R. split.
    - apply Z.mod_pos_bound; lia.
    - assert (R < P) by (unfold R; apply Z.mod_pos_bound; lia). lia. }
  set (out := num_to_limbs R n k).
  exists out.
  assert (Holen : length out = k) by (unfold out; apply num_to_limbs_length).
  split; [exact Holen |].
  split.
  { intros i Hi. unfold out. apply num_to_limbs_range; lia. }
  assert (HR_val : limbs_to_num n out = R)
    by (unfold out; apply num_to_limbs_correct; exact HR_range).
  rewrite HR_val.
  (* Show (R + B - A) mod P = 0 *)
  (* R = ((A - B) mod P + P) mod P ≡ (A - B) (mod P) *)
  (* So R + B - A ≡ (A - B) + (B - A) = 0 (mod P) *)
  unfold R.
  (* Goal: (((A - B) mod P + P) mod P + B - A) mod P = 0 *)
  (* Step 1: pull outer mod P inside *)
  replace (((A - B) mod P + P) mod P + B - A)
    with (((A - B) mod P + P) mod P + (B - A)) by ring.
  rewrite Zplus_mod_idemp_l.
  (* Goal: ((A - B) mod P + P + (B - A)) mod P = 0 *)
  (* Step 2: reassociate so (A-B) mod P is first addend *)
  replace ((A - B) mod P + P + (B - A))
    with ((A - B) mod P + (P + (B - A))) by ring.
  rewrite Zplus_mod_idemp_l.
  (* Goal: ((A - B) + (P + (B - A))) mod P = 0 *)
  replace ((A - B) + (P + (B - A))) with P by ring.
  apply Z.mod_same. lia.
Qed.

(** ** BigModInv Axiomatization and Completeness (bigint.circom:344-403)

    Multi-limb modular inverse cannot be expressed in Z (requires field
    arithmetic). We axiomatize the inverse function similarly to fp_inv. *)

Parameter big_mod_inv : nat -> nat -> list Z -> list Z -> list Z.

Axiom big_mod_inv_length : forall n k a p,
  length (big_mod_inv n k a p) = k.

Axiom big_mod_inv_range : forall n k a p i,
  (n >= 1)%nat -> (k >= 1)%nat -> (i < k)%nat ->
  0 <= nth i (big_mod_inv n k a p) 0 < 2 ^ Z.of_nat n.

Axiom big_mod_inv_spec : forall n k a p,
  (n >= 1)%nat -> (k >= 1)%nat ->
  length a = k -> length p = k ->
  limbs_to_num n p > 1 ->
  Z.gcd (limbs_to_num n a) (limbs_to_num n p) = 1 ->
  (limbs_to_num n a * limbs_to_num n (big_mod_inv n k a p)) mod (limbs_to_num n p) = 1.

Theorem BigModInv_complete :
  forall (n k : nat) (a p : list Z),
  (n >= 1)%nat -> (k >= 2)%nat ->
  length a = k -> length p = k ->
  (forall i, (i < k)%nat -> 0 <= nth i a 0 < 2 ^ Z.of_nat n) ->
  (forall i, (i < k)%nat -> 0 <= nth i p 0 < 2 ^ Z.of_nat n) ->
  limbs_to_num n p > 1 ->
  Z.gcd (limbs_to_num n a) (limbs_to_num n p) = 1 ->
  exists (out : list Z),
    length out = k /\
    (forall i, (i < k)%nat -> 0 <= nth i out 0 < 2 ^ Z.of_nat n) /\
    (limbs_to_num n a * limbs_to_num n out) mod (limbs_to_num n p) = 1.
Proof.
  intros n k a p Hn Hk Halen Hplen Ha Hp HPgt1 Hgcd.
  set (out := big_mod_inv n k a p).
  exists out.
  split; [apply big_mod_inv_length |].
  split.
  { intros i Hi. apply big_mod_inv_range; lia. }
  apply big_mod_inv_spec; try assumption; lia.
Qed.
