From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import core.Comparators.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Contains Circuit Verification
    Models constraints from circuits/collections/contains.circom. *)

(** ** Contains (contains.circom:8-37)
    For each right[i], the circuit computes IsEqual indicators against all
    left[j] values. If right[i] is non-zero but no match exists, the
    ForceEqualIfEnabled constraint forces a contradiction.

    We prove: if all constraints are satisfied, a positive sum of binary
    IsEqual indicators implies at least one match. *)

Lemma exists_positive_binary : forall (eq_out : list Z),
  Forall is_binary eq_out ->
  list_sum eq_out > 0 ->
  exists j, (j < length eq_out)%nat /\ nth j eq_out 0 = 1.
Proof.
  induction eq_out as [| e rest IH].
  - simpl. lia.
  - intros Hbin Hpos. inversion Hbin; subst.
    destruct H1 as [He | He]; subst.
    + simpl in Hpos.
      assert (Hrest_pos : list_sum rest > 0) by lia.
      destruct (IH H2 Hrest_pos) as [j [Hj Hjval]].
      exists (S j). simpl. split; [lia | exact Hjval].
    + exists 0%nat. simpl. split; [lia | reflexivity].
Qed.

Theorem Contains_sound :
  forall (nLeft : nat) (left_ : list Z) (right_i : Z)
    (eq_out eq_inv : list Z),
  length left_ = nLeft ->
  length eq_out = nLeft ->
  length eq_inv = nLeft ->
  (* IsEqual constraints *)
  (forall j, (j < nLeft)%nat ->
    nth j eq_out 0 = 1 - (nth j left_ 0 - right_i) * nth j eq_inv 0 /\
    (nth j left_ 0 - right_i) * nth j eq_out 0 = 0) ->
  (* All eq_out are binary *)
  Forall is_binary eq_out ->
  (* Sum of indicators is positive (forced by circuit when right_i /= 0) *)
  list_sum eq_out > 0 ->
  exists j, (j < nLeft)%nat /\ nth j left_ 0 = right_i.
Proof.
  intros nLeft left_ right_i eq_out eq_inv
    Hllen Helen Heilen Heq Hbin Hpos.
  destruct (exists_positive_binary eq_out Hbin Hpos) as [j [Hj Hjval]].
  rewrite Helen in Hj.
  exists j. split; [lia |].
  destruct (Heq j ltac:(lia)) as [Heq1 Heq2].
  assert (Hsound := IsEqual_sound right_i (nth j left_ 0)
    (nth j eq_out 0) (nth j eq_inv 0) Heq1 Heq2).
  destruct Hsound as [_ Hsound]. symmetry. apply Hsound. exact Hjval.
Qed.

(** ** Contains_Points (contains.circom:42-86)
    Same structure but matching on both coordinates.
    match[i][j] = eqX[i][j].out * eqY[i][j].out, both binary,
    so match = 1 iff both coordinates equal. *)

Theorem Contains_Points_match_correct :
  forall (eqX eqY match_val : Z),
  is_binary eqX -> is_binary eqY ->
  match_val = eqX * eqY ->
  (match_val = 1 <-> eqX = 1 /\ eqY = 1).
Proof.
  intros eqX eqY match_val HbX HbY Hmatch.
  destruct HbX as [HX | HX]; destruct HbY as [HY | HY];
    subst; split; intro H; try lia; destruct H; lia.
Qed.
