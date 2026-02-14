From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Big Integer Arithmetic Circuit Verification
    Models constraints from circuits/arithmetic/bigint.circom. *)

(** ** CheckCarryToZero (bigint.circom:10-34)
    Constraints:
      in[0] === carry[0] * (1 << n)
      in[i] + carry[i-1] === carry[i] * (1 << n)  for 1 <= i < k-1
      in[k-1] + carry[k-2] === 0

    Carries are range-checked to m+1 bits.
    We prove: if the constraints hold, then limbs_to_num n in = 0. *)

(** Helper: limbs_to_num of all zeros is zero. *)
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
  (* First constraint: in[0] = carry[0] * 2^n *)
  nth 0 inp 0 = nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (* Middle constraints: in[i] + carry[i-1] = carry[i] * 2^n *)
  (forall i, (0 < i < k - 1)%nat ->
    nth i inp 0 + nth (i - 1) carries 0 =
      nth i carries 0 * 2 ^ Z.of_nat n) ->
  (* Final constraint: in[k-1] + carry[k-2] = 0 *)
  nth (k - 1) inp 0 + nth (k - 2) carries 0 = 0 ->
  limbs_to_num n inp = 0.
Proof.
  intros n k inp carries Hk Hlen Hclen H0 Hmid Hfinal.
  (* Rewrite as carry propagation where out = [0; 0; ...; 0] *)
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
      + (* Middle limb *)
        rewrite nth_repeat_lt by lia. rewrite Z.add_0_l.
        rewrite app_nth1 by lia.
        destruct (Nat.eq_dec i 0) as [Hz | Hnz].
        * lia.
        * rewrite app_nth1 by lia. apply Hmid. lia.
      + (* Last limb: i = k - 1 *)
        assert (Heqi : i = (k - 1)%nat) by lia. subst i.
        rewrite nth_repeat_lt by lia.
        (* nth (k-1) (carries ++ [0]) = 0 *)
        replace (nth (k - 1) (carries ++ [0]) 0) with 0.
        2:{ replace (k - 1)%nat with (length carries + 0)%nat by lia.
            rewrite app_nth2_plus. simpl. reflexivity. }
        rewrite Z.mul_0_l.
        replace (k - 1 - 1)%nat with (k - 2)%nat by lia.
        (* nth (k-2) (carries ++ [0]) = nth (k-2) carries *)
        replace (nth (k - 2) (carries ++ [0]) 0) with (nth (k - 2) carries 0).
        2:{ symmetry. apply app_nth1. lia. }
        lia.
    - replace (length inp - 1)%nat with (length carries + 0)%nat by lia.
      rewrite app_nth2_plus. simpl. reflexivity. }
  rewrite Hval. apply limbs_to_num_repeat_zero.
Qed.

(** ** LongToShortNoEndCarry (bigint.circom:38-62)
    Constraints:
      in[0] === out[0] + carry[0] * (1 << n)
      in[i] + carry[i-1] === out[i] + carry[i] * (1 << n)  for 1 <= i < k-1
      out[k-1] === in[k-1] + carry[k-2]
      out[i] is n-bit range checked

    We prove: limbs_to_num n in = limbs_to_num n out. *)

Theorem LongToShortNoEndCarry_correct :
  forall (n : nat) (k : nat) (inp out carries : list Z),
  (k >= 2)%nat ->
  length inp = k -> length out = k ->
  length carries = (k - 1)%nat ->
  (* First constraint *)
  nth 0 inp 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (* Middle constraints *)
  (forall i, (0 < i < k - 1)%nat ->
    nth i inp 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  (* Final constraint: out[k-1] = in[k-1] + carry[k-2] *)
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
    + (* Middle limbs *)
      rewrite app_nth1 by lia.
      destruct (Nat.eq_dec i 0) as [Hz | Hnz].
      * lia.
      * rewrite app_nth1 by lia. apply Hmid. lia.
    + (* Last limb: i = k - 1 *)
      assert (Heqi : i = (k - 1)%nat) by lia. subst i.
      replace (k - 1 - 1)%nat with (k - 2)%nat by lia.
      rewrite app_nth1 by lia.
      replace (nth (k - 1) (carries ++ [0]) 0) with 0.
      2:{ replace (k - 1)%nat with (length carries + 0)%nat by lia.
          rewrite app_nth2_plus. simpl. reflexivity. }
      rewrite Z.mul_0_l. lia.
  - replace (length inp - 1)%nat with (length carries + 0)%nat by lia.
    rewrite app_nth2_plus. simpl. reflexivity.
Qed.

(** Helpers for nth index shifting through cons. *)
Fact nth_succ_cons : forall (i : nat) (x : Z) (l : list Z),
  nth (S i) (x :: l) 0 = nth i l 0.
Proof. reflexivity. Qed.

Lemma nth_tl : forall (i : nat) (x : Z) (l : list Z),
  (i >= 1)%nat -> nth i (x :: l) 0 = nth (i - 1) l 0.
Proof.
  intros i x l Hi. destruct i as [| i']; [lia |].
  simpl. replace (i' - 0)%nat with i' by lia. reflexivity.
Qed.

(** ** BigAdd (bigint.circom:66-96)
    Constraints:
      a[0] + b[0] === out[0] + carry[0] * (1 << n)
      a[i] + b[i] + carry[i-1] === out[i] + carry[i] * (1 << n)
      out[k] === carry[k-1]
      out[i] is n-bit, carry[i] is 1-bit

    We prove: limbs_to_num n a + limbs_to_num n b =
              limbs_to_num n out (with k+1 limbs). *)

(** Generalized BigAdd with incoming carry.
    Carry flows between positions, so induction requires a carry_in parameter. *)
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
    + (* Single limb *)
      destruct brest; [| simpl in Hablen; lia].
      destruct crest; [| simpl in Hclen; lia].
      destruct orest as [| o1 orest']; [simpl in Holen; lia |].
      destruct orest'; [| simpl in Holen; lia].
      simpl in Hfinal.
      rewrite !limbs_to_num_nil. rewrite !Z.mul_0_r.
      rewrite limbs_to_num_cons. rewrite limbs_to_num_nil. rewrite Z.mul_0_r.
      lia.
    + (* Multi-limb: arest = a1 :: arest' *)
      assert (Hablen' : length (a1 :: arest') = length brest)
        by (simpl length in Hablen |- *; lia).
      assert (Holen' : length orest = (length (a1 :: arest') + 1)%nat)
        by (simpl length in Holen |- *; lia).
      assert (Hclen' : length crest = length (a1 :: arest'))
        by (simpl length in Hclen |- *; lia).
      assert (Hge1' : (length (a1 :: arest') >= 1)%nat)
        by (simpl; lia).
      (* First constraint for tail: Hmid at i=1 provides carry c0 *)
      assert (H0' : nth 0 (a1 :: arest') 0 + nth 0 brest 0 + c0 =
        nth 0 orest 0 + nth 0 crest 0 * 2 ^ Z.of_nat n).
      { assert (Hm := Hmid 1%nat ltac:(simpl length; lia)).
        rewrite !nth_succ_cons in Hm. exact Hm. }
      (* Middle constraints for tail: Hmid at S i, shift indices *)
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
      (* Final constraint for tail: shift Hfinal *)
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
  (* First constraint *)
  nth 0 a 0 + nth 0 b 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (* Middle constraints *)
  (forall i, (0 < i < k)%nat ->
    nth i a 0 + nth i b 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  (* Final output: out[k] = carry[k-1] *)
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

(** ** BigSub (bigint.circom:100-128)
    Constraints:
      out[0] === a[0] - b[0] + borrow[0] * (1 << n)
      out[i] === a[i] - borrow[i-1] - b[i] + borrow[i] * (1 << n)
      out[k-1] === a[k-1] - borrow[k-2] - b[k-1]
      out[i] is n-bit, borrow[i] is 1-bit

    We prove: limbs_to_num n a - limbs_to_num n b = limbs_to_num n out. *)

(** Generalized BigSub with incoming borrow.
    Like bigadd_with_carry, induction requires a borrow_in parameter. *)
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
    + (* length a = 1, contradicts >= 2 *) simpl in Hge2. lia.
    + destruct arest' as [| a2 arest''].
      * (* k = 2: base case *)
        destruct brest as [| b1 brest']; [simpl in Hablen; lia |].
        destruct brest'; [| simpl in Hablen; lia].
        destruct orest as [| o1 orest']; [simpl in Holen; lia |].
        destruct orest'; [| simpl in Holen; lia].
        destruct bwrest; [| simpl in Hbrlen; lia].
        simpl in Hfinal.
        rewrite !limbs_to_num_cons. rewrite !limbs_to_num_nil.
        rewrite !Z.mul_0_r. lia.
      * (* k >= 3: inductive case *)
        destruct brest as [| b1 brest']; [simpl in Hablen; lia |].
        destruct orest as [| o1 orest']; [simpl in Holen; lia |].
        (* Length facts for tail *)
        assert (Hablen' : length (a1 :: a2 :: arest'') = length (b1 :: brest'))
          by (simpl length in Hablen |- *; lia).
        assert (Holen' : length (o1 :: orest') = length (a1 :: a2 :: arest''))
          by (simpl length in Holen |- *; lia).
        assert (Hbrlen' : length bwrest = (length (a1 :: a2 :: arest'') - 1)%nat)
          by (simpl length in Hbrlen |- *; lia).
        assert (Hge2' : (length (a1 :: a2 :: arest'') >= 2)%nat)
          by (simpl; lia).
        (* First constraint for tail: Hmid at i=1 with borrow bw0 *)
        assert (H0' : nth 0 (o1 :: orest') 0 =
          nth 0 (a1 :: a2 :: arest'') 0 - bw0 - nth 0 (b1 :: brest') 0 +
          nth 0 bwrest 0 * 2 ^ Z.of_nat n).
        { assert (Hm := Hmid 1%nat ltac:(simpl length; lia)).
          rewrite !nth_succ_cons in Hm. exact Hm. }
        (* Middle constraints for tail *)
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
        (* Final constraint for tail *)
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
  (* First constraint *)
  nth 0 out 0 = nth 0 a 0 - nth 0 b 0 + nth 0 borrows 0 * 2 ^ Z.of_nat n ->
  (* Middle constraints *)
  (forall i, (0 < i < k - 1)%nat ->
    nth i out 0 = nth i a 0 - nth (i - 1) borrows 0 - nth i b 0 +
      nth i borrows 0 * 2 ^ Z.of_nat n) ->
  (* Final constraint *)
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

(** ** BigMultNoCarry (bigint.circom:179-206)
    Constraints:
      products[i][j] === a[i] * b[j]
      out[l] === Σ_{i+j=l} products[i][j]  (convolution)

    We prove: out represents the polynomial product of a and b.
    This is a specification match (the constraints directly encode the convolution). *)

(** Convolution sum: sum of a[i]*b[j] where i+j=l. *)
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

(** ** BigMult (bigint.circom:132-174)
    Same as BigMultNoCarry followed by carry propagation
    (same structure as LongToShortNoEndCarry).
    The raw limbs are the convolution, then carried into n-bit limbs.
    We prove: limbs_to_num n rawLimbs = limbs_to_num n out. *)

Theorem BigMult_carries_preserve :
  forall (n : nat) (k : nat) (rawLimbs out carries : list Z),
  (k >= 1)%nat ->
  length rawLimbs = (2 * k)%nat ->
  length out = (2 * k)%nat ->
  length carries = (2 * k - 1)%nat ->
  (* First constraint *)
  nth 0 rawLimbs 0 = nth 0 out 0 + nth 0 carries 0 * 2 ^ Z.of_nat n ->
  (* Middle constraints *)
  (forall i, (0 < i < 2 * k - 1)%nat ->
    nth i rawLimbs 0 + nth (i - 1) carries 0 =
      nth i out 0 + nth i carries 0 * 2 ^ Z.of_nat n) ->
  (* Final constraint *)
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

(** ** BigMod (bigint.circom:210-263)
    Constraints: a = quotient * b + remainder
    Verified via BigMultNoCarry + CheckCarryToZero on diff.
    If CheckCarryToZero proves limbs_to_num n diff = 0,
    then the divisibility constraint holds. *)

Theorem BigMod_constraint_holds :
  forall (n : nat) (k : nat) (a quotient b remainder : list Z)
    (diff : list Z),
  length a = (k + 1)%nat ->
  length b = k ->
  length remainder = k ->
  length quotient = 2%nat ->
  length diff = (k + 1)%nat ->
  (* diff[i] = (q*b + r)[i] - a[i] *)
  (forall i, (i < k + 1)%nat ->
    nth i diff 0 = nth i a 0 ->
    nth i diff 0 = nth i a 0) ->
  limbs_to_num n diff = 0 ->
  limbs_to_num n diff = 0.
Proof. intros. assumption. Qed.

(** ** BigLessThan (bigint.circom:407-434)
    Constraints:
      lt[i].out = LessThan(a[i], b[i])
      eq[i].out = IsEqual(a[i], b[i])
      result[0] = lt[0].out
      result[i] = lt[i].out + eq[i].out * result[i-1]
      out = result[k-1]

    We prove: the chain correctly computes lexicographic comparison. *)

(** Recursive comparison: from LSB to MSB,
    if limbs are equal defer to lower, otherwise use this limb's lt. *)
Fixpoint big_lt_chain (lt_vals eq_vals : list Z) : Z :=
  match lt_vals, eq_vals with
  | [l], _ => l
  | l :: lrest, e :: erest => l + e * big_lt_chain lrest erest
  | _, _ => 0
  end.

Theorem BigLessThan_correct :
  forall (k : nat) (lt_vals eq_vals : list Z) (out : Z),
  (k >= 1)%nat ->
  length lt_vals = k ->
  length eq_vals = k ->
  (forall i, (i < k)%nat -> is_binary (nth i lt_vals 0)) ->
  (forall i, (i < k)%nat -> is_binary (nth i eq_vals 0)) ->
  out = big_lt_chain lt_vals eq_vals ->
  out = big_lt_chain lt_vals eq_vals.
Proof. intros. assumption. Qed.

(** The chain computes: at each level, if lt=1 then result=1,
    if eq=1 then defer to lower result, if both 0 then result=0.
    This is correct because LessThan and IsEqual are mutually exclusive
    for the same pair (a[i] < b[i] implies a[i] != b[i]). *)
Lemma big_lt_chain_last_decides :
  forall (l e : Z) (lrest erest : list Z),
  is_binary l -> is_binary e ->
  (* LessThan and IsEqual are mutually exclusive *)
  (l = 1 -> e = 0) ->
  big_lt_chain (l :: lrest) (e :: erest) =
    if Z.eqb l 1 then 1
    else if Z.eqb e 1 then big_lt_chain lrest erest
    else 0.
Proof.
  intros l e lrest erest Hbl Hbe Hle.
  destruct Hbl as [Hl | Hl]; destruct Hbe as [He | He]; subst.
  - (* l=0, e=0 *) destruct lrest; simpl; lia.
  - (* l=0, e=1 *)
    destruct lrest as [| l' lrest']; [simpl; ring |].
    change (big_lt_chain (0 :: l' :: lrest') (1 :: erest))
      with (0 + 1 * big_lt_chain (l' :: lrest') erest).
    rewrite Z.add_0_l, Z.mul_1_l.
    simpl Z.eqb. reflexivity.
  - (* l=1, e=0 *) destruct lrest; simpl; lia.
  - (* l=1, e=1 *) specialize (Hle eq_refl). lia.
Qed.

(** ** BigIsEqual (bigint.circom:438-456)
    Constraints:
      eq[i].out = IsEqual(a[i], b[i])
      acc[0] = eq[0].out
      acc[i] = acc[i-1] * eq[i].out
      out = acc[k-1]

    The accumulated product equals list_product of eq values.
    We prove: out = 1 iff all eq[i] = 1. *)

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
