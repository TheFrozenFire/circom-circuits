From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Ordered Circuit Verification
    Models constraints from circuits/collections/ordered.circom. *)

(** ** Ordered (ordered.circom:9-28)
    Constraints (ascending case):
      lt[i].out = 1  where lt[i] = LessThan(in[i], in[i+1])

    Assuming LessThan_sound: (lt.out = 1 <-> a < b),
    the sequence is strictly ascending. *)

Theorem Ordered_ascending_correct : forall (inputs : list Z),
  (forall i, (S i < length inputs)%nat -> nth i inputs 0 < nth (S i) inputs 0) ->
  strictly_ascending inputs.
Proof.
  induction inputs as [| x rest IH].
  - intros _. simpl. exact I.
  - destruct rest as [| y rest'].
    + intros _. simpl. exact I.
    + intro Hlt. simpl. split.
      * apply (Hlt 0%nat). simpl. lia.
      * apply IH. intros i Hi.
        apply (Hlt (S i)). simpl in *. lia.
Qed.

(** Descending variant: if every adjacent pair satisfies in[i] > in[i+1]. *)

Theorem Ordered_descending_correct : forall (inputs : list Z),
  (forall i, (S i < length inputs)%nat -> nth (S i) inputs 0 < nth i inputs 0) ->
  strictly_descending inputs.
Proof.
  induction inputs as [| x rest IH].
  - intros _. simpl. exact I.
  - destruct rest as [| y rest'].
    + intros _. simpl. exact I.
    + intro Hlt. simpl. split.
      * assert (H := Hlt 0%nat). simpl in H. lia.
      * apply IH. intros i Hi.
        apply (Hlt (S i)). simpl in *. lia.
Qed.
