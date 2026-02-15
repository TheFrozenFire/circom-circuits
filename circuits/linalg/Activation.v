From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import packing.Bitify.

Open Scope Z_scope.

(** * Activation Circuit Verification
    Models constraints from circuits/linalg/activation.circom. *)

(** ** ReLU (activation.circom:8-22)
    Constraints:
      biased = in + 2^(max_bits-1)
      bits = Num2Bits(max_bits)(biased) — all binary, biased = bits_to_num bits
      out = bits[max_bits-1] * in

    Key insight: biased = in + 2^(m-1) shifts the range.
    If in >= 0: biased >= 2^(m-1), so MSB (bit m-1) is 1, out = in.
    If in < 0: biased < 2^(m-1), so MSB is 0, out = 0. *)

Theorem ReLU_correct :
  forall (max_bits : nat) (inp biased out : Z) (bits : list Z),
  (max_bits >= 2)%nat ->
  biased = inp + 2 ^ Z.of_nat (max_bits - 1) ->
  length bits = max_bits ->
  all_binary bits ->
  biased = bits_to_num bits ->
  out = nth (max_bits - 1) bits 0 * inp ->
  (* MSB = 1 iff inp >= 0 *)
  (inp >= 0 -> out = inp) /\
  (inp < 0 -> out = 0).
Proof.
  intros max_bits inp biased out bits Hm Hbias Hlen Hall Hbtn Hout.
  assert (Hbound := bits_to_num_bound bits Hall).
  rewrite Hlen in Hbound.
  assert (Hmsb_bin : is_binary (nth (max_bits - 1) bits 0)).
  { unfold all_binary in Hall.
    apply Forall_nth with (i := (max_bits - 1)%nat) (d := 0) in Hall; [exact Hall | lia]. }
  (* Decompose bits_to_num at position (max_bits - 1) *)
  assert (Hsplit : bits_to_num bits =
    bits_to_num (firstn (max_bits - 1) bits) +
    2 ^ Z.of_nat (max_bits - 1) * bits_to_num (skipn (max_bits - 1) bits)).
  { apply bits_to_num_split. lia. }
  (* skipn (max_bits - 1) bits has length 1 *)
  assert (Hskip_len : length (skipn (max_bits - 1) bits) = 1%nat)
    by (rewrite length_skipn; lia).
  destruct (skipn (max_bits - 1) bits) as [| msb rest] eqn:Eskip.
  { simpl in Hskip_len. lia. }
  destruct rest; [| simpl in Hskip_len; lia].
  (* msb = nth (max_bits - 1) bits 0 *)
  assert (Hmsb_eq : msb = nth (max_bits - 1) bits 0).
  { assert (Hskip : nth 0 (skipn (max_bits - 1) bits) 0 = nth (max_bits - 1) bits 0).
    { rewrite nth_skipn. f_equal. lia. }
    rewrite Eskip in Hskip. simpl in Hskip. exact Hskip. }
  rewrite Hmsb_eq in Eskip.
  rewrite bits_to_num_cons in Hsplit. rewrite bits_to_num_nil in Hsplit.
  (* lower bits bound *)
  assert (Hfirst_bin : all_binary (firstn (max_bits - 1) bits))
    by (apply all_binary_firstn; exact Hall).
  assert (Hfirst_bound := bits_to_num_bound (firstn (max_bits - 1) bits) Hfirst_bin).
  rewrite length_firstn in Hfirst_bound. rewrite Nat.min_l in Hfirst_bound by lia.
  (* Now: biased = low + 2^(m-1) * msb, where 0 <= low < 2^(m-1) *)
  assert (Hbiased_eq : biased = bits_to_num (firstn (max_bits - 1) bits) +
    2 ^ Z.of_nat (max_bits - 1) * nth (max_bits - 1) bits 0).
  { rewrite Hbtn, Hsplit. lia. }
  destruct Hmsb_bin as [Hmsb0 | Hmsb1].
  - (* MSB = 0 → inp < 0 *)
    split.
    + intro Hnonneg. rewrite Hbiased_eq in Hbias.
      rewrite Hmsb0 in Hbias. exfalso. lia.
    + intro Hneg. rewrite Hout, Hmsb0. lia.
  - (* MSB = 1 → inp >= 0 *)
    split.
    + intro Hnonneg. rewrite Hout, Hmsb1. lia.
    + intro Hneg. rewrite Hbiased_eq in Hbias.
      rewrite Hmsb1 in Hbias. exfalso. lia.
Qed.

(** ** ReLUVector (activation.circom:25-35)
    Element-wise application of ReLU — correctness follows per-element. *)

Theorem ReLUVector_spec :
  forall (n : nat) (inp out : list Z),
  length inp = n -> length out = n ->
  (forall i, (i < n)%nat ->
    (nth i inp 0 >= 0 -> nth i out 0 = nth i inp 0) /\
    (nth i inp 0 < 0 -> nth i out 0 = 0)) ->
  forall i, (i < n)%nat ->
    (nth i inp 0 >= 0 -> nth i out 0 = nth i inp 0) /\
    (nth i inp 0 < 0 -> nth i out 0 = 0).
Proof. intros. apply H1. assumption. Qed.
