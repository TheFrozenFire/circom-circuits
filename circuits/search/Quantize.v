From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import linalg.FixedPoint.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * QuantizationProof Circuit Verification
    Models constraints from circuits/search/quantize.circom. *)

(** ** QuantizationProof (quantize.circom:18-49)
    Proves correct rounding of fixed-point embeddings to quantized integers.

    For each element i:
      remainder[i] = embedding[i]*scale - quantized[i]*fullRange + halfRange
      InRange(precision)(remainder[i])

    This ensures |embedding[i]*scale - quantized[i]*2^precision| < 2^(precision-1). *)

Theorem QuantizationProof_commitment_match :
  forall (n : nat) (embedding quantized : list Z)
    (embCommitResult embeddingCommit qCommitResult quantizedCommit : Z),
  length embedding = n -> length quantized = n ->
  embCommitResult = embeddingCommit ->
  qCommitResult = quantizedCommit ->
  embCommitResult = embeddingCommit /\ qCommitResult = quantizedCommit.
Proof. intros. split; assumption. Qed.

Theorem QuantizationProof_rounding :
  forall (scale fullRange halfRange : Z)
    (embedding_i quantized_i remainder_i : Z)
    (bits : list Z) (precision : nat),
  fullRange = 2 ^ Z.of_nat precision ->
  halfRange = 2 ^ (Z.of_nat precision - 1) ->
  remainder_i = embedding_i * scale - quantized_i * fullRange + halfRange ->
  (* InRange(precision): 0 <= remainder_i < 2^precision *)
  length bits = precision ->
  all_binary bits ->
  remainder_i = bits_to_num bits ->
  0 <= remainder_i < fullRange.
Proof.
  intros scale fullRange halfRange embedding_i quantized_i remainder_i
    bits precision Hfull Hhalf Hrem Hlen Hbin Hbtn.
  subst fullRange. rewrite Hbtn.
  assert (Hbound := bits_to_num_bound bits Hbin).
  rewrite Hlen in Hbound. exact Hbound.
Qed.

(** The rounding constraint implies the quantization error is bounded.
    Given remainder = emb*scale - q*fullRange + halfRange
    and 0 <= remainder < fullRange,
    we get -halfRange <= emb*scale - q*fullRange < halfRange. *)
Theorem QuantizationProof_error_bound :
  forall (scale halfRange : Z)
    (embedding_i quantized_i remainder_i fullRange : Z),
  fullRange = 2 * halfRange ->
  remainder_i = embedding_i * scale - quantized_i * fullRange + halfRange ->
  0 <= remainder_i < fullRange ->
  - halfRange <= embedding_i * scale - quantized_i * fullRange < halfRange.
Proof.
  intros scale halfRange embedding_i quantized_i remainder_i fullRange
    Hdouble Hrem Hrange.
  subst remainder_i fullRange. lia.
Qed.
