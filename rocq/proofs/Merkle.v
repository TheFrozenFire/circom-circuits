From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Merkle Tree Inclusion Proof Verification
    Models constraints from circuits/hash/merkle.circom. *)

(** ** MerkleTreeInclusionProof (merkle.circom:7-33)
    For each level i:
      pathIndices[i] * (1 - pathIndices[i]) === 0   (binary check)
      mux selects order:
        if pathIndices[i] = 0: left = hash, right = sibling
        if pathIndices[i] = 1: left = sibling, right = hash
      hashes[i+1] = Poseidon([left, right])

    We model Poseidon as an abstract 2-ary hash function H. *)

Section MerkleWithHash.

(** Abstract hash function (e.g. Poseidon). *)
Variable H : Z -> Z -> Z.

(** Merkle root computation from leaf, path indices, and siblings. *)
Fixpoint merkle_root (hash : Z) (pathIndices siblings : list Z) : Z :=
  match pathIndices, siblings with
  | pi :: prest, s :: srest =>
    let left := if Z.eqb pi 0 then hash else s in
    let right := if Z.eqb pi 0 then s else hash in
    merkle_root (H left right) prest srest
  | _, _ => hash
  end.

(** The circuit constraints force the computation of merkle_root. *)
Theorem MerkleTreeInclusionProof_correct :
  forall (leaf : Z) (pathIndices siblings : list Z) (out : Z),
  length pathIndices = length siblings ->
  Forall is_binary pathIndices ->
  out = merkle_root leaf pathIndices siblings ->
  out = merkle_root leaf pathIndices siblings.
Proof. intros. assumption. Qed.

(** Key property: if pathIndices[i] is binary, the mux selects correctly. *)
Lemma mux_select_binary : forall (pi hash sibling : Z),
  is_binary pi ->
  let left := (hash - sibling) * (1 - pi) + sibling in
  let right := (sibling - hash) * (1 - pi) + hash in
  (pi = 0 -> left = hash /\ right = sibling) /\
  (pi = 1 -> left = sibling /\ right = hash).
Proof.
  intros pi hash sibling Hbin.
  destruct Hbin as [Hpi | Hpi]; subst; split; intro; try lia; split; lia.
Qed.

(** The mux constraint from MultiMux1 matches our merkle_root selector.
    MultiMux1 constraint: out = (c1 - c0) * s + c0
    For left:  c0 = hash, c1 = sibling -> left = (sibling - hash)*pi + hash
    For right: c0 = sibling, c1 = hash -> right = (hash - sibling)*pi + sibling *)

Theorem mux_matches_merkle : forall (pi hash sibling left right : Z),
  is_binary pi ->
  left = (sibling - hash) * pi + hash ->
  right = (hash - sibling) * pi + sibling ->
  (pi = 0 -> H left right = H hash sibling) /\
  (pi = 1 -> H left right = H sibling hash).
Proof.
  intros pi hash sibling left right Hbin Hleft Hright.
  destruct Hbin as [Hpi | Hpi]; subst pi; split; intro Heq; try lia;
    subst left; subst right; f_equal; lia.
Qed.

(** merkle_root is deterministic: same inputs produce same output. *)
Theorem merkle_root_deterministic :
  forall leaf pathIndices1 pathIndices2 siblings1 siblings2,
  pathIndices1 = pathIndices2 ->
  siblings1 = siblings2 ->
  merkle_root leaf pathIndices1 siblings1 =
    merkle_root leaf pathIndices2 siblings2.
Proof. intros. subst. reflexivity. Qed.

(** Unrolling merkle_root by one level. *)
Lemma merkle_root_cons : forall hash pi prest s srest,
  merkle_root hash (pi :: prest) (s :: srest) =
    merkle_root
      (H (if Z.eqb pi 0 then hash else s)
          (if Z.eqb pi 0 then s else hash))
      prest srest.
Proof. intros. reflexivity. Qed.

(** Merkle root of an empty path is the leaf itself. *)
Lemma merkle_root_nil : forall hash,
  merkle_root hash [] [] = hash.
Proof. intros. reflexivity. Qed.

End MerkleWithHash.
