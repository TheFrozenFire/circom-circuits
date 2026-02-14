From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Modular Arithmetic Circuit Verification
    Models the constraints of ModSum, ModSub, ModSumThree, ModSubThree,
    ModSumFour, ModProd, Split, SplitThree from circuits/arithmetic/mod.circom.

    All Mod* templates delegate to TruncNumLE, which performs a Num2Bits
    decomposition and extracts the lower bits. The key insight: the lower n
    bits of a binary decomposition equal the value modulo 2^n. *)

(** ** ModSum (mod.circom:7-11) *)

Theorem ModSum_correct : forall (n : nat) (a b : Z) (bits : list Z) (out : Z),
  (n <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  a + b = bits_to_num bits ->
  out = bits_to_num (firstn n bits) ->
  0 <= out < 2 ^ Z.of_nat n /\ out = (a + b) mod 2 ^ Z.of_nat n.
Proof.
  intros n a b bits out Hle Hbin Hsum Hout.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  split.
  - subst out. apply bits_to_num_firstn_bound; assumption.
  - subst out. rewrite bits_to_num_firstn_mod by assumption.
    rewrite <- Hsum. reflexivity.
Qed.

(** ** ModSub (mod.circom:15-19) *)

Theorem ModSub_correct : forall (n : nat) (a b : Z) (bits : list Z) (out : Z),
  (n <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  a - b + 2 ^ Z.of_nat n = bits_to_num bits ->
  out = bits_to_num (firstn n bits) ->
  0 <= out < 2 ^ Z.of_nat n /\ out = (a - b) mod 2 ^ Z.of_nat n.
Proof.
  intros n a b bits out Hle Hbin Hsum Hout.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  split.
  - subst out. apply bits_to_num_firstn_bound; assumption.
  - subst out. rewrite bits_to_num_firstn_mod by assumption.
    rewrite <- Hsum.
    replace (a - b + 2 ^ Z.of_nat n)
      with (a - b + 1 * 2 ^ Z.of_nat n) by ring.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
    reflexivity.
Qed.

(** ** ModSumThree (mod.circom:22-27) *)

Theorem ModSumThree_correct :
  forall (n : nat) (a b c : Z) (bits : list Z) (out : Z),
  (n <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  a + b + c = bits_to_num bits ->
  out = bits_to_num (firstn n bits) ->
  0 <= out < 2 ^ Z.of_nat n /\ out = (a + b + c) mod 2 ^ Z.of_nat n.
Proof.
  intros n a b c bits out Hle Hbin Hsum Hout.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  split.
  - subst out. apply bits_to_num_firstn_bound; assumption.
  - subst out. rewrite bits_to_num_firstn_mod by assumption.
    rewrite <- Hsum. reflexivity.
Qed.

(** ** ModSubThree (mod.circom:31-36) *)

Theorem ModSubThree_correct :
  forall (n : nat) (a b c : Z) (bits : list Z) (out : Z),
  (n <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  a - b - c + 2 ^ Z.of_nat (n + 1) = bits_to_num bits ->
  out = bits_to_num (firstn n bits) ->
  0 <= out < 2 ^ Z.of_nat n /\ out = (a - b - c) mod 2 ^ Z.of_nat n.
Proof.
  intros n a b c bits out Hle Hbin Hsum Hout.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  assert (H2pow : 2 ^ Z.of_nat (n + 1) = 2 * 2 ^ Z.of_nat n).
  { replace (Z.of_nat (n + 1)) with (1 + Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. reflexivity. }
  split.
  - subst out. apply bits_to_num_firstn_bound; assumption.
  - subst out. rewrite bits_to_num_firstn_mod by assumption.
    rewrite <- Hsum. rewrite H2pow.
    replace (a - b - c + 2 * 2 ^ Z.of_nat n)
      with (a - b - c + 2 * 2 ^ Z.of_nat n) by ring.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
    reflexivity.
Qed.

(** ** ModSumFour (mod.circom:39-45) *)

Theorem ModSumFour_correct :
  forall (n : nat) (a b c d : Z) (bits : list Z) (out : Z),
  (n <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  a + b + c + d = bits_to_num bits ->
  out = bits_to_num (firstn n bits) ->
  0 <= out < 2 ^ Z.of_nat n /\ out = (a + b + c + d) mod 2 ^ Z.of_nat n.
Proof.
  intros n a b c d bits out Hle Hbin Hsum Hout.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  split.
  - subst out. apply bits_to_num_firstn_bound; assumption.
  - subst out. rewrite bits_to_num_firstn_mod by assumption.
    rewrite <- Hsum. reflexivity.
Qed.

(** ** ModProd (mod.circom:49-56) *)

Theorem ModProd_correct :
  forall (n : nat) (a b : Z) (bits : list Z) (out : Z),
  (n <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  a * b = bits_to_num bits ->
  out = bits_to_num (firstn n bits) ->
  0 <= out < 2 ^ Z.of_nat n /\ out = (a * b) mod 2 ^ Z.of_nat n.
Proof.
  intros n a b bits out Hle Hbin Hprod Hout.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  split.
  - subst out. apply bits_to_num_firstn_bound; assumption.
  - subst out. rewrite bits_to_num_firstn_mod by assumption.
    rewrite <- Hprod. reflexivity.
Qed.

(** ** Split (mod.circom:60-78) *)

Theorem Split_correct :
  forall (n m : nat) (bits : list Z) (inp small big : Z),
  length bits = (n + m)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  inp = bits_to_num bits ->
  small = bits_to_num (firstn n bits) ->
  big = bits_to_num (skipn n bits) ->
  inp = small + big * 2 ^ Z.of_nat n
  /\ 0 <= small < 2 ^ Z.of_nat n
  /\ 0 <= big < 2 ^ Z.of_nat m.
Proof.
  intros n m bits inp small big Hlen Hbin Hinp Hsmall Hbig.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  assert (Hle : (n <= length bits)%nat) by lia.
  split; [| split].
  - subst inp small big.
    rewrite (bits_to_num_split bits n Hle). ring.
  - subst small. apply bits_to_num_firstn_bound; assumption.
  - subst big.
    assert (Hskip := all_binary_skipn bits n Hall).
    assert (Hbound := bits_to_num_bound (skipn n bits) Hskip).
    rewrite length_skipn in Hbound. replace (length bits - n)%nat with m in Hbound by lia.
    exact Hbound.
Qed.

(** ** SplitThree (mod.circom:82-107) *)

Theorem SplitThree_correct :
  forall (n m k : nat) (bits : list Z) (inp small medium big : Z),
  length bits = (n + m + k)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  inp = bits_to_num bits ->
  small = bits_to_num (firstn n bits) ->
  medium = bits_to_num (firstn m (skipn n bits)) ->
  big = bits_to_num (skipn (n + m) bits) ->
  inp = small + medium * 2 ^ Z.of_nat n + big * 2 ^ Z.of_nat (n + m)
  /\ 0 <= small < 2 ^ Z.of_nat n
  /\ 0 <= medium < 2 ^ Z.of_nat m
  /\ 0 <= big < 2 ^ Z.of_nat k.
Proof.
  intros n m k bits inp small medium big Hlen Hbin Hinp Hsmall Hmed Hbig.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  assert (Hle_n : (n <= length bits)%nat) by lia.
  assert (Hskip_n := all_binary_skipn bits n Hall).
  assert (Hlen_skip_n : length (skipn n bits) = (m + k)%nat)
    by (rewrite length_skipn; lia).
  assert (Hle_m : (m <= length (skipn n bits))%nat) by lia.
  split; [| split; [| split]].
  - subst inp small medium big.
    rewrite (bits_to_num_split bits n Hle_n).
    rewrite (bits_to_num_split (skipn n bits) m Hle_m).
    rewrite skipn_skipn.
    rewrite Nat.add_comm.
    rewrite Nat2Z.inj_add. rewrite Z.pow_add_r by lia.
    ring.
  - subst small. apply bits_to_num_firstn_bound; assumption.
  - subst medium. apply bits_to_num_firstn_bound; assumption.
  - subst big.
    assert (Hskip_nm := all_binary_skipn bits (n + m) Hall).
    assert (Hbound := bits_to_num_bound (skipn (n + m) bits) Hskip_nm).
    rewrite length_skipn in Hbound.
    replace (length bits - (n + m))%nat with k in Hbound by lia.
    exact Hbound.
Qed.
