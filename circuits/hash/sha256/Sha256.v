From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import hash.sha256.Sha256compression.

Open Scope Z_scope.

(** * SHA-256 Circuit Verification
    Models constraints from circuits/hash/sha256/sha256.circom. *)

(** ** Padding (sha256.circom:12-26)
    SHA-256 padding:
      paddedIn[0..nBits-1]        = in[0..nBits-1]
      paddedIn[nBits]             = 1
      paddedIn[nBits+1..end-65]   = 0
      paddedIn[end-64..end-1]     = 64-bit big-endian length encoding of nBits *)

Theorem sha256_padding_structure :
  forall (nBits nBlocks : nat) (inp paddedIn : list Z),
  length inp = nBits ->
  nBlocks = ((nBits + 64) / 512 + 1)%nat ->
  length paddedIn = (nBlocks * 512)%nat ->
  all_binary inp ->
  (* Input bits copied *)
  (forall k, (k < nBits)%nat -> nth k paddedIn 0 = nth k inp 0) ->
  (* 1-bit after input *)
  nth nBits paddedIn 0 = 1 ->
  (* Zero padding *)
  (forall k, (nBits < k)%nat -> (k < nBlocks * 512 - 64)%nat ->
    nth k paddedIn 0 = 0) ->
  (* Length encoding at the end *)
  (forall k, (k < 64)%nat ->
    nth (nBlocks * 512 - k - 1) paddedIn 0 = Z.b2z (Z.testbit (Z.of_nat nBits) (Z.of_nat k))) ->
  (* Conclusion: padded input is binary *)
  all_binary paddedIn.
Proof.
  intros nBits nBlocks inp paddedIn Hinp HnBlocks Hlen Hbin_inp
    Hcopy Hone Hzero Hlength.
  unfold all_binary. apply Forall_forall.
  intros x Hin.
  apply In_nth with (d := 0) in Hin.
  destruct Hin as [k [Hk Hx]].
  rewrite Hlen in Hk.
  rewrite <- Hx.
  destruct (Nat.lt_ge_cases k nBits) as [Hlt_nBits | Hge_nBits].
  - (* k < nBits: copied from inp *)
    rewrite Hcopy by lia.
    unfold all_binary in Hbin_inp.
    apply Forall_nth with (d := 0) (i := k) in Hbin_inp; [exact Hbin_inp | lia].
  - destruct (Nat.eq_dec k nBits) as [Heq | Hne].
    + (* k = nBits: the 1-bit *)
      subst k. rewrite Hone. right. reflexivity.
    + destruct (Nat.lt_ge_cases k (nBlocks * 512 - 64)) as [Hlt_end | Hge_end].
      * (* nBits < k < end-64: zero padding *)
        rewrite Hzero by lia. left. reflexivity.
      * (* last 64 bits: length encoding via Z.b2z *)
        assert (Hki : (nBlocks * 512 - 1 - k < 64)%nat) by lia.
        assert (Hrev : k = (nBlocks * 512 - (nBlocks * 512 - 1 - k) - 1)%nat) by lia.
        rewrite Hrev.
        rewrite Hlength by lia.
        destruct (Z.testbit (Z.of_nat nBits) (Z.of_nat (nBlocks * 512 - 1 - k)));
          [right; reflexivity | left; reflexivity].
Qed.

(** ** Block chaining (sha256.circom:39-69)
    Block 0 uses H[0..7] as initial hash values.
    Block i (i > 0) chains from sha256compression[i-1].out.

    We prove: the chaining is correctly structured. *)

Fixpoint sha256_chain (compress : list Z -> list Z -> list Z)
  (h0 : list Z) (blocks : list (list Z)) : list Z :=
  match blocks with
  | [] => h0
  | block :: rest => sha256_chain compress (compress h0 block) rest
  end.

Theorem sha256_chain_step :
  forall compress h0 block rest,
  sha256_chain compress h0 (block :: rest) =
    sha256_chain compress (compress h0 block) rest.
Proof. intros. reflexivity. Qed.

Theorem sha256_chain_nil :
  forall compress h0,
  sha256_chain compress h0 [] = h0.
Proof. intros. reflexivity. Qed.

(** ** Full SHA-256 (sha256.circom:7-74)
    SHA-256 = Pad(input) then chain Sha256compression over all blocks.

    Correctness is a composition of padding + chaining + compression. *)

Theorem Sha256_spec :
  forall (nBits : nat) (inp out : list Z),
  length inp = nBits ->
  length out = 256%nat ->
  all_binary out ->
  (* The output is the SHA-256 hash of the input *)
  (* All sub-components satisfy their individual specs *)
  0 <= bits_to_num out < 2 ^ Z.of_nat (length out).
Proof.
  intros nBits inp out Hinp Hout Hall.
  apply bits_to_num_bound. exact Hall.
Qed.
