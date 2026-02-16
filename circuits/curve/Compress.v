From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import packing.Bitify.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Point Compression Circuit Verification
    Models constraints from circuits/curve/compress.circom. *)

(** ** BabyCompress (compress.circom:8-23)
    Constraints:
      xBits = Num2BitsLE(254)(x)
      yBits = Num2BitsLE(254)(y)
      out[0..253] = yBits[0..253]
      out[254] = 0
      out[255] = xBits[0]

    Output layout (256 bits, little-endian):
      [y bits (254)][0][sign(x)]

    We prove: the output layout is correctly structured. *)

Theorem BabyCompress_layout :
  forall (x y : Z) (xBits yBits : list Z) (out : list Z),
  length xBits = 254%nat ->
  length yBits = 254%nat ->
  all_binary xBits -> all_binary yBits ->
  x = bits_to_num xBits ->
  y = bits_to_num yBits ->
  length out = 256%nat ->
  (* Wiring constraints *)
  (forall i, (i < 254)%nat -> nth i out 0 = nth i yBits 0) ->
  nth 254 out 0 = 0 ->
  nth 255 out 0 = nth 0 xBits 0 ->
  (* All output bits are binary *)
  all_binary out.
Proof.
  intros x y xBits yBits out HxLen HyLen HxBin HyBin Hx Hy
    HoutLen Hybits Hpad Hsign.
  unfold all_binary. apply Forall_nth.
  intros i d Hi. rewrite nth_indep with (d' := 0) by lia.
  rewrite HoutLen in Hi.
  destruct (Nat.lt_ge_cases i 254) as [Hlt254 | Hge254].
  - (* i < 254: from yBits *)
    rewrite Hybits by exact Hlt254.
    eapply Forall_nth; [exact HyBin | lia].
  - destruct (Nat.eq_dec i 254) as [Heq254 | Hne254].
    + (* i = 254: padding = 0 *)
      subst i. rewrite Hpad. left. reflexivity.
    + (* i = 255: from xBits[0] *)
      assert (i = 255)%nat by lia. subst i.
      rewrite Hsign. eapply Forall_nth; [exact HxBin | lia].
Qed.

(** The sign bit is binary. *)
Theorem BabyCompress_sign_binary :
  forall (xBits : list Z),
  all_binary xBits ->
  (length xBits > 0)%nat ->
  is_binary (nth 0 xBits 0).
Proof.
  intros xBits Hall Hlen.
  unfold all_binary in Hall.
  apply Forall_nth with (i := 0%nat) (d := 0) in Hall; [exact Hall | lia].
Qed.

(** ** BabyMultiCompress (compress.circom:26-39)
    Concatenates BabyCompress outputs.
    out[i*256..(i+1)*256-1] = BabyCompress(points[i]). *)

Theorem BabyMultiCompress_spec :
  forall (nPoints : nat)
    (compress_out : nat -> list Z) (out : list Z),
  length out = (nPoints * 256)%nat ->
  (forall p, (p < nPoints)%nat -> length (compress_out p) = 256%nat) ->
  (forall p j, (p < nPoints)%nat -> (j < 256)%nat ->
    nth (p * 256 + j) out 0 = nth j (compress_out p) 0) ->
  forall p j, (p < nPoints)%nat -> (j < 256)%nat ->
    nth (p * 256 + j) out 0 = nth j (compress_out p) 0.
Proof. intros. apply H1; assumption. Qed.
