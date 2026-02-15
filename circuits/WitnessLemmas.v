From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Shared Lemmas for Witness Completeness Proofs

    These lemmas support proving that `<--` witness computations
    produce values satisfying the `===` constraints. *)

(** ** Bit Extraction Lemmas *)

(** Z.testbit produces a binary value. *)
Lemma Z_testbit_binary : forall z i,
  0 <= i -> is_binary (Z.b2z (Z.testbit z i)).
Proof.
  intros z i Hi.
  destruct (Z.testbit z i); unfold is_binary; auto.
Qed.

(** Circom's `(in >> i) & 1` equals `Z.b2z (Z.testbit in i)`. *)
Lemma shiftr_land_1_testbit : forall inp i,
  0 <= inp -> 0 <= i ->
  Z.land (Z.shiftr inp i) 1 = Z.b2z (Z.testbit inp i).
Proof.
  intros inp i Hinp Hi.
  rewrite Z.shiftr_div_pow2 by exact Hi.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.pow_1_r.
  rewrite <- Z.testbit_spec' by exact Hi.
  reflexivity.
Qed.

(** The witness function for Num2BitsLE: map Z.testbit over [0..n). *)
Definition num2bits_witness (inp : Z) (n : nat) : list Z :=
  map (fun i => Z.b2z (Z.testbit inp (Z.of_nat i))) (seq 0 n).

Lemma num2bits_witness_length : forall inp n,
  length (num2bits_witness inp n) = n.
Proof.
  intros. unfold num2bits_witness. rewrite length_map, length_seq. reflexivity.
Qed.

(** Helper: nth into a map over seq. *)
Lemma nth_map_seq : forall (f : nat -> Z) (start len i : nat) (d : Z),
  (i < len)%nat ->
  nth i (map f (seq start len)) d = f (start + i)%nat.
Proof.
  intros f start len. revert start.
  induction len as [| len' IH]; intros start i d Hi.
  - lia.
  - simpl seq. rewrite map_cons.
    destruct i as [| i'].
    + simpl. f_equal. lia.
    + simpl nth. rewrite IH by lia. f_equal. lia.
Qed.

Lemma num2bits_witness_nth : forall inp n i,
  (i < n)%nat ->
  nth i (num2bits_witness inp n) 0 = Z.b2z (Z.testbit inp (Z.of_nat i)).
Proof.
  intros inp n i Hi.
  unfold num2bits_witness.
  rewrite nth_map_seq by lia. simpl. reflexivity.
Qed.

Lemma num2bits_witness_all_binary : forall inp n,
  0 <= inp ->
  all_binary (num2bits_witness inp n).
Proof.
  intros inp n Hinp.
  unfold all_binary. apply Forall_nth.
  intros i d Hi.
  rewrite num2bits_witness_length in Hi.
  rewrite nth_indep with (d' := 0) by (rewrite num2bits_witness_length; lia).
  rewrite num2bits_witness_nth by lia.
  apply Z_testbit_binary. lia.
Qed.

(** The tail of num2bits_witness is num2bits_witness of inp/2. *)
Lemma num2bits_witness_cons : forall inp n,
  num2bits_witness inp (S n) =
    Z.b2z (Z.testbit inp 0) :: num2bits_witness (inp / 2) n.
Proof.
  intros inp n.
  unfold num2bits_witness. simpl seq. rewrite map_cons.
  f_equal.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite !length_map, !length_seq. reflexivity.
  - intros i Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !nth_map_seq by lia.
    rewrite Z.div2_bits by lia.
    f_equal. f_equal. lia.
Qed.

(** Core lemma: bits_to_num of the testbit witness reconstructs the input. *)
Lemma bits_to_num_testbit : forall (n : nat) (inp : Z),
  0 <= inp < 2 ^ Z.of_nat n ->
  bits_to_num (num2bits_witness inp n) = inp.
Proof.
  induction n as [| n' IH]; intros inp Hrange.
  - simpl in Hrange. assert (inp = 0) by lia. subst. reflexivity.
  - rewrite num2bits_witness_cons. rewrite bits_to_num_cons.
    rewrite IH.
    + (* Z.b2z (Z.testbit inp 0) + 2 * (inp / 2) = inp *)
      assert (Hmod : Z.b2z (Z.testbit inp 0) = inp mod 2).
      { rewrite Z.testbit_spec' by lia. rewrite Z.pow_0_r. rewrite Z.div_1_r.
        reflexivity. }
      rewrite Hmod.
      assert (Hdm := Z.div_mod inp 2 ltac:(lia)). lia.
    + split.
      * apply Z.div_pos; lia.
      * apply Z.div_lt_upper_bound; [lia |].
        rewrite Nat2Z.inj_succ in Hrange.
        rewrite Z.pow_succ_r in Hrange by lia. lia.
Qed.

(** ** Division / Modulo Lemmas *)

(** Package of properties for division witness: q = a/b, r = a mod b. *)
Lemma div_mod_witness_valid : forall a b,
  0 <= a -> 0 < b ->
  let q := a / b in
  let r := a mod b in
  0 <= r < b /\ 0 <= q /\ a = q * b + r.
Proof.
  intros a b Ha Hb q r.
  subst q r.
  split; [apply Z.mod_pos_bound; lia |].
  split; [apply Z.div_pos; lia |].
  assert (Hdm := Z.div_mod a b ltac:(lia)). lia.
Qed.

(** Witness satisfies the constraint a = q * b + r with 0 <= r < b. *)
Lemma div_mod_constraint : forall a b,
  0 <= a -> 0 < b ->
  a = (a / b) * b + a mod b /\ 0 <= a mod b < b.
Proof.
  intros a b Ha Hb.
  split.
  - assert (Hdm := Z.div_mod a b ltac:(lia)). lia.
  - apply Z.mod_pos_bound. lia.
Qed.

(** ** Carry Propagation Lemmas *)

(** A single carry propagation step: split sum into (low bits, carry). *)
Definition carry_witness_step (sum : Z) (n : nat) : Z * Z :=
  (sum mod 2 ^ Z.of_nat n, sum / 2 ^ Z.of_nat n).

Lemma carry_witness_step_valid : forall sum n,
  0 <= sum ->
  let '(out, carry) := carry_witness_step sum n in
  sum = out + carry * 2 ^ Z.of_nat n /\
  0 <= out < 2 ^ Z.of_nat n /\
  0 <= carry.
Proof.
  intros sum n Hsum.
  unfold carry_witness_step.
  assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  split.
  - assert (Hdm := Z.div_mod sum (2 ^ Z.of_nat n) ltac:(lia)). lia.
  - split; [apply Z.mod_pos_bound; lia |].
    apply Z.div_pos; lia.
Qed.

(** When sum < 2^(n+1), the carry is binary (0 or 1). *)
Lemma carry_witness_binary : forall sum n,
  0 <= sum < 2 ^ Z.of_nat (n + 1) ->
  is_binary (snd (carry_witness_step sum n)).
Proof.
  intros sum n Hrange.
  unfold carry_witness_step. simpl snd.
  assert (Hpow : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 <= sum / 2 ^ Z.of_nat n) by (apply Z.div_pos; lia).
  assert (Hq_bound : sum / 2 ^ Z.of_nat n < 2).
  { apply Z.div_lt_upper_bound; [lia |].
    rewrite Nat2Z.inj_add in Hrange.
    replace (Z.of_nat n + Z.of_nat 1) with (Z.of_nat n + 1) in Hrange by lia.
    rewrite Z.pow_add_r in Hrange by lia.
    simpl Z.pow at 2 in Hrange. lia. }
  unfold is_binary. lia.
Qed.

(** ** Num2Bits Binary Constraint from Witness *)

(** Each bit from num2bits_witness satisfies b * (b - 1) = 0. *)
Lemma num2bits_witness_binary_constraint : forall inp n i,
  0 <= inp ->
  (i < n)%nat ->
  let out := num2bits_witness inp n in
  nth i out 0 * (nth i out 0 - 1) = 0.
Proof.
  intros inp n i Hinp Hi out.
  subst out.
  rewrite num2bits_witness_nth by lia.
  apply binary_constraint.
  apply Z_testbit_binary. lia.
Qed.
