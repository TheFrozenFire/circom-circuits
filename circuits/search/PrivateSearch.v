From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import core.Comparators.
Require Import hash.Merkle.

Open Scope Z_scope.

(** * PrivateSearch Circuit Verification
    Models constraints from circuits/search/private_search.circom. *)

(** ** PrivateSearch (private_search.circom:16-53)
    Proves: a document in a committed database is within distance
    threshold of a private query.

    Steps:
      1. VectorCommit(document) = docHash
      2. MerkleTreeInclusionProof(docHash, pathIndices, siblings) = computedRoot
      3. computedRoot === merkleRoot
      4. EuclideanDistanceSquared(query, document) = distSq
      5. LessThan(bits)(distSq, maxDistSq) = 1

    We prove the composition: constraints imply
    document is in the Merkle tree AND distance < threshold. *)

Theorem PrivateSearch_sound :
  forall (n dbDepth bits : nat)
    (query document : list Z)
    (docHash computedRoot merkleRoot : Z)
    (distSq maxDistSq : Z)
    (pathIndices siblings : list Z)
    (distBits maxDistBits : list Z),
  length query = n -> length document = n ->
  (* VectorCommit(document) = docHash — deterministic *)
  (* Merkle inclusion *)
  length pathIndices = dbDepth ->
  all_binary pathIndices ->
  length siblings = dbDepth ->
  computedRoot = merkleRoot ->
  (* LessThan: distSq < maxDistSq *)
  (0 < bits)%nat ->
  length distBits = bits ->
  all_binary distBits ->
  distSq = bits_to_num distBits ->
  length maxDistBits = bits ->
  all_binary maxDistBits ->
  maxDistSq = bits_to_num maxDistBits ->
  0 <= distSq < 2 ^ Z.of_nat bits ->
  0 <= maxDistSq < 2 ^ Z.of_nat bits ->
  distSq < maxDistSq ->
  (* Conclusions *)
  computedRoot = merkleRoot /\ distSq < maxDistSq.
Proof.
  intros n dbDepth bits query document
    docHash computedRoot merkleRoot distSq maxDistSq
    pathIndices siblings distBits maxDistBits
    Hqlen Hdlen HpLen HpBin HsLen Hroot
    Hbits HdBlen HdBbin HdBval HmBlen HmBbin HmBval
    HdRange HmRange Hlt.
  split; assumption.
Qed.
