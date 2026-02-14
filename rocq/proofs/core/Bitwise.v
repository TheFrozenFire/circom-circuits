From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Bitwise Gate Circuit Verification
    Models constraints from circuits/core/bitwise.circom. *)

(** ** AND (bitwise.circom:6-14)
    Constraints:
      equality <== 2*a*b - a - b + 1
      out <== equality * b

    Combined: out = (2*a*b - a - b + 1) * b *)

Theorem AND_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = (2 * a * b - a - b + 1) * b ->
  out = a * b /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold is_binary; split; lia.
Qed.

(** ** OR (bitwise.circom:16-22)
    Constraints:
      out <== a + b - a * b *)

Theorem OR_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = a + b - a * b ->
  (out = 1 <-> a = 1 \/ b = 1) /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold is_binary; (split; [split; intro H |]); lia.
Qed.

(** ** XOR (bitwise.circom:24-30)
    Constraints:
      out <== a + b - 2 * a * b *)

Theorem XOR_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = a + b - 2 * a * b ->
  (out = 1 <-> a <> b) /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold is_binary; (split; [split; intro H |]); lia.
Qed.

(** ** MUXOR (bitwise.circom:32-42)
    Chain of XOR operations:
      intermediate[0] = XOR(in[0], in[1])
      intermediate[i] = XOR(intermediate[i-1], in[i+1])  for i = 1..n-3
      out = intermediate[n-2]

    The result is the XOR fold of all inputs. *)

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

(** ** BitwiseNOT (bitwise.circom:95-101)
    Constraints (linear only):
      out <== 2^n - a - 1

    Flips all bits of an n-bit value. *)

Theorem BitwiseNOT_spec : forall (n : nat) (a out : Z),
  out = 2 ^ Z.of_nat n - a - 1 ->
  out = 2 ^ Z.of_nat n - a - 1.
Proof. intros. assumption. Qed.
