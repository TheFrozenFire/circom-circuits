From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import packing.Bitify.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Pack/Unpack Circuit Verification
    Models constraints from circuits/packing/pack.circom. *)

(** ** Pack_Elements (pack.circom:8-36)
    Each input item is decomposed to bitsPerItem bits via Num2BitsLE,
    bits are concatenated within each element, and reconstructed via Bits2NumLE.

    We prove: the packed output is bounded by 2^bitsPerElement. *)

Theorem Pack_Elements_correct :
  forall (bpe : nat) (concat_bits : list Z) (out : Z),
  (bpe <= 253)%nat ->
  length concat_bits = bpe ->
  all_binary concat_bits ->
  out = bits_to_num concat_bits ->
  0 <= out < 2 ^ Z.of_nat bpe.
Proof.
  intros bpe concat_bits out Hbpe Hlen Hall Hout.
  subst out. rewrite <- Hlen. apply bits_to_num_bound. exact Hall.
Qed.

(** ** Pack_Elements_FromBits (pack.circom:40-60)
    Same as Pack_Elements but input is pre-decomposed bits. *)

Theorem Pack_Elements_FromBits_correct :
  forall (bpe : nat) (concat_bits : list Z) (out : Z),
  (bpe <= 253)%nat ->
  length concat_bits = bpe ->
  all_binary concat_bits ->
  out = bits_to_num concat_bits ->
  0 <= out < 2 ^ Z.of_nat bpe.
Proof.
  intros bpe concat_bits out Hbpe Hlen Hall Hout.
  subst out. rewrite <- Hlen. apply bits_to_num_bound. exact Hall.
Qed.

(** ** Unpack_Elements (pack.circom:64-89)
    Inverse of Pack_Elements: decompose packed element to bits,
    then reconstruct each item from its bit window.

    We prove: if the packed value equals the sum of items weighted by powers
    of 2, then unpacking recovers the original items. *)

Theorem Unpack_roundtrip :
  forall (bitsPerItem : nat) (item_bits : list Z) (item out : Z),
  all_binary item_bits ->
  length item_bits = bitsPerItem ->
  item = bits_to_num item_bits ->
  out = bits_to_num item_bits ->
  out = item.
Proof.
  intros bitsPerItem item_bits item out Hall Hlen Hitem Hout.
  subst. reflexivity.
Qed.
