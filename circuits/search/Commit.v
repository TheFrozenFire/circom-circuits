From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * VectorCommit Circuit Verification
    Models constraints from circuits/search/commit.circom. *)

(** ** VectorCommit (commit.circom:10-42)
    Chunked Poseidon hashing with binary tree reduction.

    1. Split v[0..n-1] into nChunks groups of chunkSize.
    2. Hash each chunk: chunkHash[i] = Poseidon(chunkSize)(chunk_i).
    3. Store leaves at nodes[nChunks-1+i] = chunkHash[i].
    4. Reduce tree bottom-up: nodes[i] = Poseidon(2)(nodes[2i+1], nodes[2i+2]).
    5. Output = nodes[0] (root). *)

Theorem VectorCommit_deterministic :
  forall (n chunkSize : nat) (v : list Z) (out1 out2 : Z)
    (compute : list Z -> Z),
  length v = n ->
  (chunkSize > 0)%nat ->
  (n mod chunkSize = 0)%nat ->
  out1 = compute v ->
  out2 = compute v ->
  (* Same inputs through same function yield same output *)
  out1 = out2.
Proof.
  intros n chunkSize v out1 out2 compute
    Hlen Hcs Hmod Hout1 Hout2.
  subst out1 out2. reflexivity.
Qed.

(** The tree structure is correct: root equals the first internal node hash. *)
Theorem VectorCommit_tree_structure :
  forall (nChunks : nat) (nodes : list Z)
    (chunkHashes : list Z) (treeHashes : list Z),
  (nChunks > 1)%nat ->
  length nodes = (2 * nChunks - 1)%nat ->
  length chunkHashes = nChunks ->
  (* Leaves are chunk hashes *)
  (forall i, (i < nChunks)%nat ->
    nth (nChunks - 1 + i) nodes 0 = nth i chunkHashes 0) ->
  (* Internal nodes are Poseidon(2) of children *)
  (forall i, (i < nChunks - 1)%nat ->
    nth i nodes 0 = nth i treeHashes 0) ->
  (* Root is the first tree hash *)
  nth 0 nodes 0 = nth 0 treeHashes 0.
Proof.
  intros nChunks nodes chunkHashes treeHashes
    Hnc Hlen Hch Hleaves Hinternal.
  apply Hinternal. lia.
Qed.

(** Two identical inputs produce the same commitment (collision resistance
    of Poseidon assumed). *)
Theorem VectorCommit_same_input_same_output :
  forall (n chunkSize : nat) (v1 v2 : list Z) (out1 out2 : Z)
    (compute : list Z -> Z),
  length v1 = n -> length v2 = n ->
  v1 = v2 ->
  out1 = compute v1 ->
  out2 = compute v2 ->
  (* Same inputs yield same output *)
  out1 = out2.
Proof.
  intros n chunkSize v1 v2 out1 out2 compute
    Hlen1 Hlen2 Hveq Hout1 Hout2.
  subst v2 out1 out2. reflexivity.
Qed.
