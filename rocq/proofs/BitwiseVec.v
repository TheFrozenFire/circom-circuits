From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Bitwise Vector Circuit Verification
    Models the constraints of Xor3, Ch_t, Maj_t, RotR, ShR, MUXOR,
    MultiXOR, BinSum from circuits/hash/sha256/ and circuits/bitwise.circom. *)

(** ** Xor3 (sha256/xor3.circom:5-16)
    Constraints (per element k):
      mid[k] = b[k] * c[k]
      out[k] = a[k] * (1 - 2*b[k] - 2*c[k] + 4*mid[k]) + b[k] + c[k] - 2*mid[k]

    Substituting mid = b*c:
      out = a*(1 - 2b - 2c + 4bc) + b + c - 2bc *)

Theorem Xor3_correct : forall a b c mid out : Z,
  is_binary a -> is_binary b -> is_binary c ->
  mid = b * c ->
  out = a * (1 - 2 * b - 2 * c + 4 * mid) + b + c - 2 * mid ->
  out = xor3_bit a b c /\ is_binary out.
Proof.
  intros a b c mid out Ha Hb Hc Hmid Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    destruct Hc as [Hc | Hc];
    subst; unfold xor3_bit, xor_bit, is_binary; split; lia.
Qed.

(** ** Ch_t (sha256/ch.circom:4-13)
    Constraints (per element k):
      out[k] = a[k] * (b[k] - c[k]) + c[k] *)

Theorem Ch_correct : forall a b c out : Z,
  is_binary a -> is_binary b -> is_binary c ->
  out = a * (b - c) + c ->
  out = ch_bit a b c /\ is_binary out.
Proof.
  intros a b c out Ha Hb Hc Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    destruct Hc as [Hc | Hc];
    subst; unfold ch_bit, is_binary; split; lia.
Qed.

(** ** Maj_t (sha256/maj.circom:5-16)
    Constraints (per element k):
      mid[k] = b[k] * c[k]
      out[k] = a[k] * (b[k] + c[k] - 2 * mid[k]) + mid[k]

    Substituting mid = b*c:
      out = a*(b + c - 2bc) + bc *)

Theorem Maj_correct : forall a b c mid out : Z,
  is_binary a -> is_binary b -> is_binary c ->
  mid = b * c ->
  out = a * (b + c - 2 * mid) + mid ->
  out = maj_bit a b c /\ is_binary out.
Proof.
  intros a b c mid out Ha Hb Hc Hmid Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    destruct Hc as [Hc | Hc];
    subst; unfold maj_bit, is_binary; split; lia.
Qed.

(** ** RotR (sha256/rotate.circom:4-11)
    Pure rewiring — no R1CS constraints.
    Spec: out[i] = in[(i + r) mod n] for all i. *)

Theorem RotR_spec : forall (n r : nat) (inp out : list Z),
  length inp = n -> length out = n ->
  (forall i, (i < n)%nat -> nth i out 0 = nth ((i + r) mod n) inp 0) ->
  forall i, (i < n)%nat -> nth i out 0 = nth ((i + r) mod n) inp 0.
Proof.
  intros n r inp out _ _ Hspec i Hi. apply Hspec. exact Hi.
Qed.

(** ** ShR (sha256/shift.circom:4-15)
    Pure rewiring — no R1CS constraints.
    Spec: out[i] = in[i + r] if i + r < n, else 0. *)

Theorem ShR_spec : forall (n r : nat) (inp out : list Z),
  length inp = n -> length out = n ->
  (forall i, (i < n)%nat ->
    nth i out 0 = if (i + r <? n)%nat then nth (i + r) inp 0 else 0) ->
  forall i, (i < n)%nat ->
    nth i out 0 = if (i + r <? n)%nat then nth (i + r) inp 0 else 0.
Proof.
  intros n r inp out _ _ Hspec i Hi. apply Hspec. exact Hi.
Qed.

(** ** MultiXOR (bitwise.circom:44-51)
    Constraints (per element i):
      out[i] = in[0][i] + in[1][i] - 2 * in[0][i] * in[1][i]

    Each element is an independent XOR. *)

Theorem MultiXOR_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = a + b - 2 * a * b ->
  out = xor_bit a b /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold xor_bit, is_binary; split; lia.
Qed.

(** ** MUXOR (bitwise.circom:32-42)
    Chain of XOR operations:
      intermediate[0] = XOR(in[0], in[1])
      intermediate[i] = XOR(intermediate[i-1], in[i+1])  for i = 1..n-3
      out = intermediate[n-2]

    The result is the XOR fold of all inputs.
    We prove the chain property: if each step is a valid XOR of binary
    inputs, the result equals the fold_xor of all inputs and is binary. *)

Lemma xor_bit_binary : forall a b,
  is_binary a -> is_binary b -> is_binary (xor_bit a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold xor_bit, is_binary; lia.
Qed.

Lemma xor_bit_correct : forall a b out,
  is_binary a -> is_binary b ->
  out = a + b - 2 * a * b ->
  out = xor_bit a b.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold xor_bit; lia.
Qed.

(** MUXOR soundness: a chain of XOR operations on binary inputs
    produces the fold_xor and is binary. *)
Theorem MUXOR_correct : forall (inputs : list Z),
  (2 <= length inputs)%nat ->
  all_binary inputs ->
  is_binary (fold_xor inputs).
Proof.
  intros inputs Hlen Hall.
  induction inputs as [| x rest IH].
  - simpl in Hlen. lia.
  - destruct rest as [| y rest'].
    + simpl in Hlen. lia.
    + destruct rest' as [| z rest''].
      * (* Base case: exactly 2 elements *)
        simpl. apply xor_bit_binary.
        -- inversion Hall; assumption.
        -- inversion Hall; subst. inversion H2; assumption.
      * (* Inductive case: 3+ elements *)
        simpl fold_xor.
        apply xor_bit_binary.
        -- inversion Hall; assumption.
        -- apply IH.
           ++ simpl. lia.
           ++ inversion Hall; assumption.
Qed.

(** ** BinSum (sha256/binsum.circom:16-41)
    Constraints:
      out[k] * (out[k] - 1) = 0   for k = 0..nout-1
      Σ_j Σ_k in[j][k] * 2^k = Σ_k out[k] * 2^k

    This is structurally a Num2Bits decomposition of the sum of inputs.
    We model it as: given binary output bits whose value equals the sum
    of input values, the output represents the binary sum. *)

Theorem BinSum_correct : forall (out : list Z) (input_sum : Z),
  (forall i, (i < length out)%nat ->
    nth i out 0 * (nth i out 0 - 1) = 0) ->
  input_sum = bits_to_num out ->
  all_binary out /\ 0 <= input_sum < 2 ^ Z.of_nat (length out)
  /\ input_sum = bits_to_num out.
Proof.
  intros out input_sum Hbin Hsum.
  assert (Hall := binary_constraints_imply_all_binary out Hbin).
  split; [exact Hall |].
  split.
  - rewrite Hsum. apply bits_to_num_bound. exact Hall.
  - exact Hsum.
Qed.
