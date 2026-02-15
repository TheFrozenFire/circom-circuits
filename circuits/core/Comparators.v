From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.

Open Scope Z_scope.

(** * Comparator Circuit Verification
    Models constraints from circuits/core/comparators.circom. *)

(** ** IsZero (comparators.circom:6-15)
    Constraints:
      out === -in * inv + 1     (i.e., out = 1 - in * inv)
      in * out === 0 *)

Theorem IsZero_sound : forall inp out inv : Z,
  out = 1 - inp * inv ->
  inp * out = 0 ->
  (inp = 0 <-> out = 1).
Proof.
  intros inp out inv Hout Hprod.
  split.
  - intro Hinp. subst inp. rewrite Hout. ring.
  - intro Hone. subst out.
    rewrite Hone in Hprod. lia.
Qed.

Theorem IsZero_binary : forall inp out inv : Z,
  out = 1 - inp * inv ->
  inp * out = 0 ->
  is_binary out.
Proof.
  intros inp out inv Hout Hprod.
  unfold is_binary.
  rewrite Hout in Hprod.
  destruct (Z.eq_dec inp 0) as [Hinp | Hinp].
  - right. subst inp. rewrite Hout. ring.
  - left.
    assert (inp * (1 - inp * inv) = 0) as H by exact Hprod.
    apply Z.mul_eq_0 in H.
    destruct H as [H | H]; [contradiction | lia].
Qed.

(** ** IsEqual (comparators.circom:18-23)
    Delegates to IsZero(in[1] - in[0]).
    Constraints:
      out = 1 - (b - a) * inv
      (b - a) * out = 0 *)

Theorem IsEqual_sound : forall a b out inv : Z,
  out = 1 - (b - a) * inv ->
  (b - a) * out = 0 ->
  (a = b <-> out = 1).
Proof.
  intros a b out inv Hout Hprod.
  assert (Hiso := IsZero_sound (b - a) out inv Hout Hprod).
  lia.
Qed.

(** ** IsZero Completeness
    Witness: inv <-- (inp != 0) ? 1/inp : 0
             out <-- 1 - inp * inv

    Two cases:
    - inp = 0: inv = 0, out = 1. Both constraints hold trivially.
    - inp != 0: inv = fp_inv inp, out = (1 - inp * fp_inv inp) mod p = 0.
      By fp_inv_spec, inp * fp_inv inp ≡ 1, so out ≡ 0 and inp * out ≡ 0. *)

Theorem IsZero_complete : forall inp : Z,
  in_field inp ->
  exists out inv : Z,
    in_field out /\ in_field inv /\
    (out - (1 - inp * inv)) mod p_field = 0 /\
    (inp * out) mod p_field = 0.
Proof.
  intros inp Hinp.
  destruct (Z.eq_dec inp 0) as [Hzero | Hnz].
  - (* Case inp = 0 *)
    exists 1, 0. split; [exact in_field_1 |]. split; [exact in_field_0 |].
    subst inp. simpl. split.
    + rewrite Z.mod_small; [lia | pose proof p_field_pos; lia].
    + rewrite Z.mod_small; [lia | pose proof p_field_pos; lia].
  - (* Case inp != 0 *)
    set (inv := fp_inv inp).
    set (out := (1 - inp * inv) mod p_field).
    exists out, inv.
    assert (Hp_pos : 0 < p_field) by exact p_field_pos.
    assert (Hinv_field : in_field inv) by (apply fp_inv_in_field; assumption).
    assert (Hinv_spec : (inp * inv) mod p_field = 1) by (apply fp_inv_spec; assumption).
    (* Key: out = 0 because inp * inv ≡ 1 (mod p), so 1 - inp*inv ≡ 0 *)
    assert (Hout_zero : out = 0).
    { unfold out. rewrite <- Hinv_spec.
      rewrite Zminus_mod_idemp_l.
      replace (inp * inv - inp * inv) with 0 by ring.
      rewrite Z.mod_0_l by lia. reflexivity. }
    split.
    + (* in_field out *)
      rewrite Hout_zero. exact in_field_0.
    + split; [exact Hinv_field |].
      split.
      * (* (out - (1 - inp * inv)) mod p = 0 *)
        unfold out.
        rewrite Zminus_mod_idemp_l.
        replace ((1 - inp * inv) - (1 - inp * inv)) with 0 by ring.
        rewrite Z.mod_0_l by lia. reflexivity.
      * (* (inp * out) mod p = 0 *)
        rewrite Hout_zero. rewrite Z.mul_0_r.
        rewrite Z.mod_0_l by lia. reflexivity.
Qed.

(** ** IsEqual Completeness
    Delegates to IsZero(b - a). *)

Theorem IsEqual_complete : forall a b : Z,
  in_field a -> in_field b ->
  exists out inv : Z,
    in_field out /\ in_field inv /\
    (out - (1 - (b - a) * inv)) mod p_field = 0 /\
    ((b - a) * out) mod p_field = 0.
Proof.
  intros a b Ha Hb.
  assert (Hp_pos : 0 < p_field) by exact p_field_pos.
  (* b - a may not be in [0, p), so we reduce it mod p first *)
  set (diff := (b - a) mod p_field).
  assert (Hdiff_field : in_field diff).
  { unfold diff, in_field. split; apply Z.mod_pos_bound; lia. }
  destruct (IsZero_complete diff Hdiff_field)
    as [out [inv [Hout_field [Hinv_field [Hc1 Hc2]]]]].
  exists out, inv.
  split; [exact Hout_field |]. split; [exact Hinv_field |].
  assert (Hba_cong : ((b - a) - diff) mod p_field = 0).
  { unfold diff. rewrite Zminus_mod_idemp_r.
    replace ((b - a) - (b - a)) with 0 by ring.
    apply Z.mod_0_l. lia. }
  split.
  - (* (out - (1 - (b-a)*inv)) mod p = 0 *)
    replace (out - (1 - (b - a) * inv))
      with ((out - (1 - diff * inv)) + ((b - a) - diff) * inv) by ring.
    rewrite Zplus_mod.
    rewrite (Z.mul_mod ((b - a) - diff) inv) by lia.
    rewrite Hba_cong. simpl (0 * (inv mod p_field)%Z).
    rewrite Z.mod_0_l by lia. rewrite Z.add_0_r.
    rewrite Z.mod_mod by lia. exact Hc1.
  - (* ((b-a) * out) mod p = 0 *)
    rewrite <- Z.mul_mod_idemp_l by lia. fold diff. exact Hc2.
Qed.

(** ** LessThan (comparators.circom:27-34)
    Constraints:
      bits = Num2Bits(n+1)(a + 2^n - b)
      out = 1 - bits[n]

    Key idea: a + 2^n - b is computed. If a < b, this value is in
    [0, 2^n), so the (n+1)-th bit (index n) is 0, giving out = 1.
    If a >= b, the value is in [2^n, 2^(n+1)), so bit n is 1, giving out = 0. *)

Theorem LessThan_sound : forall n : nat, (0 < n)%nat ->
  forall a b : Z, 0 <= a < 2 ^ Z.of_nat n -> 0 <= b < 2 ^ Z.of_nat n ->
  forall bits : list Z, forall out : Z,
  length bits = S n ->
  all_binary bits ->
  bits_to_num bits = a + 2 ^ Z.of_nat n - b ->
  out = 1 - nth n bits 0 ->
  (a < b <-> out = 1).
Proof.
  intros n Hn a b Ha Hb bits out Hlen Hbin Hbtn Hout.
  assert (Hbound := bits_to_num_bound bits Hbin).
  rewrite Hlen in Hbound. rewrite Nat2Z.inj_succ in Hbound.
  rewrite Z.pow_succ_r in Hbound by lia.
  (* The value v = a + 2^n - b satisfies 0 < v < 2^(n+1) *)
  assert (Hv_lower : 0 < a + 2 ^ Z.of_nat n - b) by lia.
  assert (Hv_upper : a + 2 ^ Z.of_nat n - b < 2 * 2 ^ Z.of_nat n) by lia.
  (* Split bits into lower n bits and the top bit *)
  assert (Htop_bin : is_binary (nth n bits 0)).
  {
    unfold all_binary in Hbin.
    apply Forall_nth with (i := n) (d := 0) in Hbin; [exact Hbin |].
    lia.
  }
  (* Express bits_to_num in terms of lower bits and top bit using list split *)
  assert (Hnth_err : nth_error bits n = Some (nth n bits 0))
    by (apply nth_error_nth'; lia).
  assert (Hsplit := firstn_skipn_middle n bits Hnth_err).
  assert (Hdecomp : bits_to_num bits =
    bits_to_num (firstn n bits) + 2 ^ Z.of_nat n * nth n bits 0).
  {
    rewrite <- Hsplit at 1.
    rewrite bits_to_num_app.
    rewrite firstn_length_le by lia.
    f_equal.
    rewrite bits_to_num_cons.
    assert (Hskip_len : length (skipn (S n) bits) = 0%nat)
      by (rewrite length_skipn; lia).
    destruct (skipn (S n) bits) eqn:E; [| simpl in Hskip_len; lia].
    simpl. lia.
  }
  (* Lower bits are all binary *)
  assert (Hfirst_bin : all_binary (firstn n bits)).
  {
    unfold all_binary.
    rewrite <- Hsplit in Hbin. apply Forall_app in Hbin.
    destruct Hbin as [Hbin_first _]. exact Hbin_first.
  }
  assert (Hfirst_bound := bits_to_num_bound (firstn n bits) Hfirst_bin).
  rewrite firstn_length_le in Hfirst_bound by lia.
  (* Now reason about the top bit *)
  rewrite Hdecomp in Hbtn.
  destruct Htop_bin as [Htop0 | Htop1].
  + (* Top bit = 0: a + 2^n - b < 2^n, so a < b *)
    rewrite Htop0 in *. split; lia.
  + (* Top bit = 1: a + 2^n - b >= 2^n, so a >= b *)
    rewrite Htop1 in *. split; [intro; exfalso |]; lia.
Qed.

(** ** ForceEqualIfEnabled (comparators.circom:37-43)
    Constraints:
      isEq = 1 - (b - a) * inv     (from IsZero)
      (b - a) * isEq = 0            (from IsZero)
      (1 - isEq) * enabled = 0

    We prove: when enabled = 1, a must equal b. *)

Theorem ForceEqualIfEnabled_sound : forall a b enabled isEq inv : Z,
  isEq = 1 - (b - a) * inv ->
  (b - a) * isEq = 0 ->
  (1 - isEq) * enabled = 0 ->
  enabled = 1 -> a = b.
Proof.
  intros a b enabled isEq inv HisEq Hprod Hforce Hen.
  rewrite Hen in Hforce.
  assert (isEq = 1) by lia.
  assert (Hiso := IsZero_sound (b - a) isEq inv HisEq Hprod).
  lia.
Qed.

(** ** Field Safety for LessThan

    When n <= 252, inputs a, b in [0, 2^n), the intermediate value
    a + 2^n - b is in [1, 2^(n+1) - 1], which is a subset of [0, p_field)
    since 2^(n+1) <= 2^253 < p. The Z proof applies in F_p. *)

Theorem LessThan_field_safe : forall n : nat, (0 < n)%nat -> (n <= 252)%nat ->
  forall a b : Z, 0 <= a < 2 ^ Z.of_nat n -> 0 <= b < 2 ^ Z.of_nat n ->
  in_field a /\ in_field b /\ in_field (a + 2 ^ Z.of_nat n - b).
Proof.
  intros n Hn Hn252 a b Ha Hb.
  assert (Hpow_n : 2 ^ Z.of_nat n < p_field)
    by (apply pow2_lt_p_field; lia).
  assert (Hpow_sn : 2 ^ Z.of_nat (S n) < p_field)
    by (apply pow2_lt_p_field; lia).
  split; [| split].
  - apply in_field_of_bound with (n := n); [exact Ha | lia].
  - apply in_field_of_bound with (n := n); [exact Hb | lia].
  - unfold in_field.
    rewrite Nat2Z.inj_succ in Hpow_sn.
    rewrite Z.pow_succ_r in Hpow_sn by lia.
    lia.
Qed.
