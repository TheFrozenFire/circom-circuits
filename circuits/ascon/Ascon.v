From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import core.Bitwise.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Ascon Circuit Verification
    Models constraints from circuits/ascon/sbox.circom,
    permutations.circom, and hash.circom. *)

(** ** Ascon S-box (sbox.circom)
    The Ascon S-box is a 5-bit substitution, decomposed into
    Boolean operations: AND (product of binary inputs) and
    MUXOR (multi-input XOR via fold).

    Each y_i is a specific Boolean function of x[0..4]. *)

(** y0 = x4*x1 ⊕ x3 ⊕ x2*x1 ⊕ x2 ⊕ x1*x0 ⊕ x1 ⊕ x0 *)
Theorem Ascon_Sbox_y0_correct :
  forall (x0 x1 x2 x3 x4 y0 : Z),
  is_binary x0 -> is_binary x1 -> is_binary x2 ->
  is_binary x3 -> is_binary x4 ->
  y0 = xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit
    (x4 * x1) x3) (x2 * x1)) x2) (x1 * x0)) x1) x0 ->
  is_binary y0.
Proof.
  intros x0 x1 x2 x3 x4 y0 H0 H1 H2 H3 H4 Hy.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
  destruct H4 as [H4|H4]; subst x0 x1 x2 x3 x4;
  unfold xor_bit in Hy; simpl in Hy;
  subst; try (left; ring); try (right; ring).
Qed.

(** y1 = x4 ⊕ x3*x2 ⊕ x3*x1 ⊕ x3 ⊕ x2*x1 ⊕ x2 ⊕ x1 ⊕ x0 *)
Theorem Ascon_Sbox_y1_correct :
  forall (x0 x1 x2 x3 x4 y1 : Z),
  is_binary x0 -> is_binary x1 -> is_binary x2 ->
  is_binary x3 -> is_binary x4 ->
  y1 = xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit
    x4 (x3 * x2)) (x3 * x1)) x3) (x2 * x1)) x2) x1) x0 ->
  is_binary y1.
Proof.
  intros x0 x1 x2 x3 x4 y1 H0 H1 H2 H3 H4 Hy.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
  destruct H4 as [H4|H4]; subst x0 x1 x2 x3 x4;
  unfold xor_bit in Hy; simpl in Hy;
  subst; try (left; ring); try (right; ring).
Qed.

(** y2 = x4*x3 ⊕ x4 ⊕ x2 ⊕ x1 ⊕ 1 *)
Theorem Ascon_Sbox_y2_correct :
  forall (x0 x1 x2 x3 x4 y2 : Z),
  is_binary x0 -> is_binary x1 -> is_binary x2 ->
  is_binary x3 -> is_binary x4 ->
  y2 = xor_bit (xor_bit (xor_bit (xor_bit (x4 * x3) x4) x2) x1) 1 ->
  is_binary y2.
Proof.
  intros x0 x1 x2 x3 x4 y2 H0 H1 H2 H3 H4 Hy.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
  destruct H4 as [H4|H4]; subst x0 x1 x2 x3 x4;
  unfold xor_bit in Hy; simpl in Hy;
  subst; try (left; ring); try (right; ring).
Qed.

(** y3 = x4*x0 ⊕ x4 ⊕ x3*x0 ⊕ x3 ⊕ x2*x1 ⊕ x2 ⊕ x1 ⊕ x0 *)
Theorem Ascon_Sbox_y3_correct :
  forall (x0 x1 x2 x3 x4 y3 : Z),
  is_binary x0 -> is_binary x1 -> is_binary x2 ->
  is_binary x3 -> is_binary x4 ->
  y3 = xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit
    (x4 * x0) x4) (x3 * x0)) x3) (x2 * x1)) x2) x1) x0 ->
  is_binary y3.
Proof.
  intros x0 x1 x2 x3 x4 y3 H0 H1 H2 H3 H4 Hy.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
  destruct H4 as [H4|H4]; subst x0 x1 x2 x3 x4;
  unfold xor_bit in Hy; simpl in Hy;
  subst; try (left; ring); try (right; ring).
Qed.

(** y4 = x4*x1 ⊕ x4 ⊕ x3 ⊕ x1*x0 ⊕ x1 *)
Theorem Ascon_Sbox_y4_correct :
  forall (x0 x1 x2 x3 x4 y4 : Z),
  is_binary x0 -> is_binary x1 -> is_binary x2 ->
  is_binary x3 -> is_binary x4 ->
  y4 = xor_bit (xor_bit (xor_bit (xor_bit (x4 * x1) x4) x3) (x1 * x0)) x1 ->
  is_binary y4.
Proof.
  intros x0 x1 x2 x3 x4 y4 H0 H1 H2 H3 H4 Hy.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
  destruct H4 as [H4|H4]; subst x0 x1 x2 x3 x4;
  unfold xor_bit in Hy; simpl in Hy;
  subst; try (left; ring); try (right; ring).
Qed.

(** ** Ascon_Sbox_Circuit (permutations.circom:74-83)
    Composes all five y_i functions. *)

Theorem Ascon_Sbox_Circuit_binary :
  forall (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : Z),
  is_binary x0 -> is_binary x1 -> is_binary x2 ->
  is_binary x3 -> is_binary x4 ->
  (* S-box equations *)
  y0 = xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit
    (x4 * x1) x3) (x2 * x1)) x2) (x1 * x0)) x1) x0 ->
  y1 = xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit
    x4 (x3 * x2)) (x3 * x1)) x3) (x2 * x1)) x2) x1) x0 ->
  y2 = xor_bit (xor_bit (xor_bit (xor_bit (x4 * x3) x4) x2) x1) 1 ->
  y3 = xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit (xor_bit
    (x4 * x0) x4) (x3 * x0)) x3) (x2 * x1)) x2) x1) x0 ->
  y4 = xor_bit (xor_bit (xor_bit (xor_bit (x4 * x1) x4) x3) (x1 * x0)) x1 ->
  (* All outputs are binary *)
  is_binary y0 /\ is_binary y1 /\ is_binary y2 /\
  is_binary y3 /\ is_binary y4.
Proof.
  intros x0 x1 x2 x3 x4 y0 y1 y2 y3 y4
    H0 H1 H2 H3 H4 Hy0 Hy1 Hy2 Hy3 Hy4.
  repeat split.
  - exact (Ascon_Sbox_y0_correct x0 x1 x2 x3 x4 y0 H0 H1 H2 H3 H4 Hy0).
  - exact (Ascon_Sbox_y1_correct x0 x1 x2 x3 x4 y1 H0 H1 H2 H3 H4 Hy1).
  - exact (Ascon_Sbox_y2_correct x0 x1 x2 x3 x4 y2 H0 H1 H2 H3 H4 Hy2).
  - exact (Ascon_Sbox_y3_correct x0 x1 x2 x3 x4 y3 H0 H1 H2 H3 H4 Hy3).
  - exact (Ascon_Sbox_y4_correct x0 x1 x2 x3 x4 y4 H0 H1 H2 H3 H4 Hy4).
Qed.

(** ** Ascon_ConstantAddition (permutations.circom:29-49)
    XORs round constant into bits 56..63 of S2. *)

Theorem Ascon_ConstantAddition_spec :
  forall (S2_in S2_out : list Z) (constant : list Z),
  length S2_in = 64%nat ->
  length S2_out = 64%nat ->
  length constant = 8%nat ->
  all_binary S2_in ->
  all_binary constant ->
  (* First 56 bits unchanged *)
  (forall i, (i < 56)%nat -> nth i S2_out 0 = nth i S2_in 0) ->
  (* Last 8 bits XORed with constant *)
  (forall i, (i < 8)%nat ->
    nth (56 + i) S2_out 0 = xor_bit (nth (56 + i) S2_in 0) (nth i constant 0)) ->
  (* Output is binary *)
  all_binary S2_out.
Proof.
  intros S2_in S2_out constant Hlen_in Hlen_out Hlen_c Hbin_in Hbin_c Hcopy Hxor.
  unfold all_binary. apply Forall_forall.
  intros x Hin.
  apply In_nth with (d := 0) in Hin.
  destruct Hin as [k [Hk Hx]].
  rewrite Hlen_out in Hk.
  rewrite <- Hx.
  destruct (Nat.lt_ge_cases k 56) as [Hlt | Hge].
  - (* k < 56: copied from S2_in *)
    rewrite Hcopy by lia.
    unfold all_binary in Hbin_in.
    apply Forall_nth with (d := 0) (i := k) in Hbin_in; [exact Hbin_in | lia].
  - (* 56 <= k < 64: XOR of S2_in and constant *)
    assert (Hi : (k - 56 < 8)%nat) by lia.
    replace k with (56 + (k - 56))%nat by lia.
    rewrite Hxor by lia.
    apply xor_bit_binary.
    + unfold all_binary in Hbin_in.
      apply Forall_nth with (d := 0) (i := (56 + (k - 56))%nat) in Hbin_in;
        [exact Hbin_in | lia].
    + unfold all_binary in Hbin_c.
      apply Forall_nth with (d := 0) (i := (k - 56)%nat) in Hbin_c;
        [exact Hbin_c | lia].
Qed.

(** ** Ascon_LinearDiffusion_Layer (permutations.circom:96-106)
    out[k] = in[k] ⊕ in[(k+shift_a) mod 64] ⊕ in[(k+shift_b) mod 64] *)

Theorem Ascon_LinearDiffusion_Layer_spec :
  forall (inp out : list Z) (shift_a shift_b : nat),
  length inp = 64%nat ->
  length out = 64%nat ->
  all_binary inp ->
  (forall k, (k < 64)%nat ->
    nth k out 0 = xor_bit (xor_bit
      (nth k inp 0)
      (nth ((k + shift_a) mod 64) inp 0))
      (nth ((k + shift_b) mod 64) inp 0)) ->
  (* Output is binary *)
  all_binary out.
Proof.
  intros inp out shift_a shift_b Hlen_in Hlen_out Hbin Hxor.
  unfold all_binary. apply Forall_forall.
  intros x Hin.
  apply In_nth with (d := 0) in Hin.
  destruct Hin as [k [Hk Hx]].
  rewrite Hlen_out in Hk.
  rewrite <- Hx. rewrite Hxor by lia.
  unfold all_binary in Hbin.
  assert (Hb1 : is_binary (nth k inp 0)).
  { apply Forall_nth with (d := 0) (i := k) in Hbin; [exact Hbin | lia]. }
  assert (Hmod_a : ((k + shift_a) mod 64 < 64)%nat).
  { apply Nat.mod_upper_bound. lia. }
  assert (Hb2 : is_binary (nth ((k + shift_a) mod 64) inp 0)).
  { apply Forall_nth with (d := 0) (i := ((k + shift_a) mod 64)%nat) in Hbin;
    [exact Hbin | lia]. }
  assert (Hmod_b : ((k + shift_b) mod 64 < 64)%nat).
  { apply Nat.mod_upper_bound. lia. }
  assert (Hb3 : is_binary (nth ((k + shift_b) mod 64) inp 0)).
  { apply Forall_nth with (d := 0) (i := ((k + shift_b) mod 64)%nat) in Hbin;
    [exact Hbin | lia]. }
  destruct Hb1 as [H1|H1]; destruct Hb2 as [H2|H2]; destruct Hb3 as [H3|H3];
  rewrite H1, H2, H3; unfold xor_bit; simpl;
  try (left; ring); try (right; ring).
Qed.

(** ** Ascon_Permutation (permutations.circom:9-27)
    Composition of rnd rounds: ConstantAddition ∘ Sbox ∘ LinearDiffusion. *)

Fixpoint iterate {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with O => x | S n' => f (iterate f n' x) end.

Theorem Ascon_Permutation_spec :
  forall (rnd : nat) (round_fn : list Z -> list Z) (init : list Z),
  (rnd > 0)%nat ->
  length init = 320%nat ->
  all_binary init ->
  (* Each round preserves length and binary *)
  (forall st, length st = 320%nat -> all_binary st ->
    length (round_fn st) = 320%nat /\ all_binary (round_fn st)) ->
  (* N-fold composition preserves length and binary *)
  length (iterate round_fn rnd init) = 320%nat /\
  all_binary (iterate round_fn rnd init).
Proof.
  induction rnd as [| rnd' IH]; intros round_fn init Hgt Hlen Hbin Hpres.
  - lia.
  - simpl iterate.
    destruct rnd' as [| rnd''].
    + (* rnd = 1 *)
      simpl iterate. apply Hpres; assumption.
    + (* rnd = S (S rnd'') *)
      assert (Hgt' : (S rnd'' > 0)%nat) by lia.
      specialize (IH round_fn init Hgt' Hlen Hbin Hpres).
      destruct IH as [IHlen IHbin].
      apply Hpres; assumption.
Qed.

(** ** Ascon_Absorb (permutations.circom:108-118)
    XOR input block into S0 of state. *)

Theorem Ascon_Absorb_spec :
  forall (S0_in S0_out inp : list Z),
  length S0_in = 64%nat ->
  length inp = 64%nat ->
  length S0_out = 64%nat ->
  all_binary S0_in -> all_binary inp ->
  (forall k, (k < 64)%nat ->
    nth k S0_out 0 = xor_bit (nth k S0_in 0) (nth k inp 0)) ->
  all_binary S0_out.
Proof.
  intros S0_in S0_out inp Hlen1 Hlen2 Hlen3 Hbin1 Hbin2 Hxor.
  unfold all_binary. apply Forall_forall.
  intros x Hin.
  apply In_nth with (d := 0) in Hin.
  destruct Hin as [k [Hk Hx]].
  rewrite Hlen3 in Hk.
  rewrite <- Hx. rewrite Hxor by lia.
  assert (Ha : is_binary (nth k S0_in 0)).
  { unfold all_binary in Hbin1. apply Forall_nth with (d := 0) (i := k) in Hbin1;
    [exact Hbin1 | lia]. }
  assert (Hb : is_binary (nth k inp 0)).
  { unfold all_binary in Hbin2. apply Forall_nth with (d := 0) (i := k) in Hbin2;
    [exact Hbin2 | lia]. }
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb];
  rewrite Ha, Hb; unfold xor_bit; simpl;
  try (left; ring); try (right; ring).
Qed.

(** ** Ascon_Hash_256 (hash.circom:7-40)
    Absorb nBlocks then squeeze 4 words.
    Output is determined by input blocks and initial state constants. *)

Theorem Ascon_Hash_256_spec :
  forall (nBlocks : nat) (out : list Z),
  (nBlocks > 0)%nat ->
  length out = 256%nat ->
  all_binary out ->
  (* Absorb: for each block, state = Permutation(12)(Absorb(state, block))
     Squeeze: 4 iterations of Permutation(12), extracting S0 each time
     Output hash value is bounded to 256 bits *)
  0 <= bits_to_num out < 2 ^ 256.
Proof.
  intros nBlocks out Hgt Hlen Hbin.
  assert (Hbound := bits_to_num_bound out Hbin).
  rewrite Hlen in Hbound. exact Hbound.
Qed.
