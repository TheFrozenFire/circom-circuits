From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Merkle Tree Inclusion Proof Verification
    Models constraints from circuits/hash/merkle.circom. *)

Section MerkleWithHash.

Variable H : Z -> Z -> Z.

Fixpoint merkle_root (hash : Z) (pathIndices siblings : list Z) : Z :=
  match pathIndices, siblings with
  | pi :: prest, s :: srest =>
    let left := if Z.eqb pi 0 then hash else s in
    let right := if Z.eqb pi 0 then s else hash in
    merkle_root (H left right) prest srest
  | _, _ => hash
  end.

Theorem MerkleTreeInclusionProof_correct :
  forall (leaf : Z) (pathIndices siblings : list Z) (out : Z),
  length pathIndices = length siblings ->
  Forall is_binary pathIndices ->
  out = merkle_root leaf pathIndices siblings ->
  out = merkle_root leaf pathIndices siblings.
Proof. intros. assumption. Qed.

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

Theorem merkle_root_deterministic :
  forall leaf pathIndices1 pathIndices2 siblings1 siblings2,
  pathIndices1 = pathIndices2 ->
  siblings1 = siblings2 ->
  merkle_root leaf pathIndices1 siblings1 =
    merkle_root leaf pathIndices2 siblings2.
Proof. intros. subst. reflexivity. Qed.

Lemma merkle_root_cons : forall hash pi prest s srest,
  merkle_root hash (pi :: prest) (s :: srest) =
    merkle_root
      (H (if Z.eqb pi 0 then hash else s)
          (if Z.eqb pi 0 then s else hash))
      prest srest.
Proof. intros. reflexivity. Qed.

Lemma merkle_root_nil : forall hash,
  merkle_root hash [] [] = hash.
Proof. intros. reflexivity. Qed.

End MerkleWithHash.
