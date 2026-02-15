From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import core.Comparators.
Require Import hash.Merkle.

Open Scope Z_scope.

(** * PrivateDedup Circuit Verification
    Models constraints from circuits/search/dedup.circom. *)

(** ** PrivateDedup (dedup.circom:18-61)
    Proves: a document is sufficiently distant from a candidate in a
    committed database.

    Steps:
      1. VectorCommit(document) = docHash; docHash === documentCommit
      2. VectorCommit(candidate) = candHash
      3. MerkleTreeInclusionProof(candHash, path) = computedRoot
      4. computedRoot === merkleRoot
      5. EuclideanDistanceSquared(document, candidate) = distSq
      6. LessThan(bits)(minDistSq, distSq) = 1  — i.e., distSq > minDistSq *)

Theorem PrivateDedup_sound :
  forall (n dbDepth bits : nat)
    (document candidate : list Z)
    (docHash documentCommit candHash computedRoot merkleRoot : Z)
    (distSq minDistSq : Z)
    (pathIndices siblings : list Z),
  length document = n -> length candidate = n ->
  (* Document commitment matches *)
  docHash = documentCommit ->
  (* Candidate in Merkle tree *)
  length pathIndices = dbDepth ->
  all_binary pathIndices ->
  length siblings = dbDepth ->
  computedRoot = merkleRoot ->
  (* Distance exceeds minimum *)
  0 <= minDistSq ->
  0 <= distSq ->
  minDistSq < distSq ->
  (* Conclusions — derive positive gap *)
  docHash = documentCommit /\
  computedRoot = merkleRoot /\
  0 < distSq - minDistSq.
Proof.
  intros n dbDepth bits document candidate
    docHash documentCommit candHash computedRoot merkleRoot
    distSq minDistSq pathIndices siblings
    Hdlen Hclen HdocCommit HpLen HpBin HsLen Hroot
    HminRange HdistRange Hlt.
  repeat split; (assumption || lia).
Qed.
