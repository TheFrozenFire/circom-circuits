From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Selector Circuit Verification
    Models constraints from circuits/collections/selector.circom. *)

(** ** IndexSelector (selector.circom:7-34)
    For each lookup index[i], the circuit uses IsEqual indicators to select
    the matching row. If exactly one row matches, the output equals that row.

    We prove the indicator mux property: if exactly one indicator is 1 and
    the rest are 0, the weighted sum equals the selected element. *)

Theorem indicator_mux_correct : forall (values indicators : list Z) (out : Z),
  length values = length indicators ->
  Forall is_binary indicators ->
  list_sum indicators = 1 ->
  out = list_sum (map (fun p => fst p * snd p) (combine indicators values)) ->
  exists j, (j < length values)%nat /\
    nth j indicators 0 = 1 /\ out = nth j values 0.
Proof.
  intros values indicators.
  revert values.
  induction indicators as [| ind rest IH]; intros values out Hlen Hbin Hone Hout.
  - simpl in Hone. lia.
  - destruct values as [| v vals].
    + simpl in Hlen. lia.
    + inversion_clear Hbin as [| ? ? HindB HrestB].
      destruct HindB as [Hind | Hind]; subst ind.
      * (* ind = 0: the 1 must be in rest *)
        simpl in Hone. simpl in Hout.
        assert (Hout' : out = list_sum (map (fun p => fst p * snd p) (combine rest vals)))
          by lia.
        assert (Hrest_len : length vals = length rest) by (simpl in Hlen; lia).
        destruct (IH vals out Hrest_len HrestB ltac:(lia) Hout')
          as [j [Hj [Hjind Hjval]]].
        exists (S j). simpl. split; [lia |]. split; assumption.
      * (* ind = 1: rest must sum to 0, so all rest are 0 *)
        exists 0%nat. simpl length; simpl nth.
        split; [lia |]. split; [reflexivity |].
        rewrite list_sum_cons in Hone.
        assert (Hrest0 : list_sum rest = 0) by lia.
        assert (Hmap0 := binary_zero_weighted_sum rest vals HrestB Hrest0).
        subst out.
        replace (combine (1 :: rest) (v :: vals))
          with ((1, v) :: combine rest vals) by reflexivity.
        replace (map (fun p : Z * Z => fst p * snd p) ((1, v) :: combine rest vals))
          with (1 * v :: map (fun p : Z * Z => fst p * snd p) (combine rest vals))
          by reflexivity.
        rewrite list_sum_cons. rewrite Hmap0. lia.
Qed.
