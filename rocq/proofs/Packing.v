From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import Num2Bits.

Open Scope Z_scope.

(** * Packing Circuit Verification
    Models the constraints of Bits2Num and TruncNumLE from
    circuits/packing/bitify.circom. *)

(** ** Bits2Num (bitify.circom:46-56)
    Constraints (linear only — zero R1CS constraints):
      out <== Σ in[i] * 2^i

    This is a pure specification match: the output equals bits_to_num of the input.
    No binary enforcement — the caller is responsible for ensuring inputs are binary. *)

Theorem Bits2Num_spec : forall (inp : list Z) (out : Z),
  out = bits_to_num inp ->
  out = bits_to_num inp.
Proof.
  intros inp out H. exact H.
Qed.

(** When inputs are known binary, Bits2Num output matches the expected value
    and is bounded. *)
Theorem Bits2Num_correct : forall (inp : list Z) (out : Z),
  all_binary inp ->
  out = bits_to_num inp ->
  0 <= out < 2 ^ Z.of_nat (length inp).
Proof.
  intros inp out Hall Hout. subst out. apply bits_to_num_bound. exact Hall.
Qed.

(** ** TruncNumLE (bitify.circom:61-81)
    Parameters: nIn, nOut with nOut <= nIn.
    Constraints:
      bits[i] * (bits[i] - 1) === 0    for each i in 0..nIn-1
      in === Σ bits[i] * 2^i           (full Num2Bits decomposition)
      out <== Σ bits[i] * 2^i          for i in 0..nOut-1  (linear)

    We prove: all bits are binary, the input is range-checked to [0, 2^nIn),
    and the output is the lower nOut bits (bounded by 2^nOut). *)

Theorem TruncNumLE_correct :
  forall (nOut : nat) (bits : list Z) (inp out : Z),
  (nOut <= length bits)%nat ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  inp = bits_to_num bits ->
  out = bits_to_num (firstn nOut bits) ->
  all_binary bits
  /\ 0 <= inp < 2 ^ Z.of_nat (length bits)
  /\ 0 <= out < 2 ^ Z.of_nat nOut
  /\ out = bits_to_num (firstn nOut bits).
Proof.
  intros nOut bits inp out HnOut Hbin Hinp Hout.
  (* Reuse Num2Bits_correct for the full decomposition *)
  assert (Hnum2bits := Num2Bits_correct bits inp Hbin Hinp).
  destruct Hnum2bits as [Hall Hrange].
  repeat split.
  - exact Hall.
  - lia.
  - lia.
  - subst out.
    apply bits_to_num_firstn_bound; [exact Hall | exact HnOut].
  - subst out.
    apply bits_to_num_firstn_bound; [exact Hall | exact HnOut].
  - exact Hout.
Qed.
