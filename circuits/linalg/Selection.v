From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Selection Circuit Verification
    Models constraints from circuits/linalg/selection.circom. *)

(** ** Max (selection.circom:7-48)
    The prover witnesses an index. The circuit verifies:
      1. out = in[index]  (via indicator mux)
      2. out >= in[i] for all i  (via LessThan comparisons)

    We prove: if out >= in[i] for all i, then out is a maximum. *)

Theorem Max_correct : forall (inputs : list Z) (out : Z),
  (forall i, (i < length inputs)%nat -> out >= nth i inputs 0) ->
  In out (map (fun i => nth i inputs 0) (seq 0 (length inputs))) ->
  forall i, (i < length inputs)%nat -> nth i inputs 0 <= out.
Proof.
  intros inputs out Hge _ i Hi.
  specialize (Hge i Hi). lia.
Qed.

(** ** Max Completeness

    Every non-empty list has a maximum element at some index. *)

Lemma list_has_max : forall (l : list Z),
  (1 <= length l)%nat ->
  exists j : nat, (j < length l)%nat /\
    forall i, (i < length l)%nat -> nth i l 0 <= nth j l 0.
Proof.
  induction l as [| x rest IH].
  - simpl. lia.
  - intros Hlen.
    destruct rest as [| y rest'].
    + (* Single element *)
      exists 0%nat. split; [simpl; lia |].
      intros i Hi. assert (i = 0)%nat by (simpl in Hi; lia). subst. simpl. lia.
    + (* x :: y :: rest' *)
      assert (Hrest_len : (1 <= length (y :: rest'))%nat) by (simpl; lia).
      destruct (IH Hrest_len) as [j_rest [Hj_lt Hj_max]].
      assert (Hcmp : nth j_rest (y :: rest') 0 <= x \/
                     x < nth j_rest (y :: rest') 0) by lia.
      destruct Hcmp as [Hle | Hgt].
      * (* x >= max of rest *)
        exists 0%nat. split; [simpl length in *; lia |].
        intros i Hi.
        destruct i as [| i'].
        -- simpl. lia.
        -- change (nth i' (y :: rest') 0 <= x).
           assert (Hi' : (i' < length (y :: rest'))%nat) by (simpl length in *; lia).
           specialize (Hj_max i' Hi'). lia.
      * (* max of rest > x *)
        exists (S j_rest). split; [simpl length in *; lia |].
        intros i Hi.
        destruct i as [| i'].
        -- change (x <= nth j_rest (y :: rest') 0). lia.
        -- change (nth i' (y :: rest') 0 <= nth j_rest (y :: rest') 0).
           assert (Hi' : (i' < length (y :: rest'))%nat) by (simpl length in *; lia).
           exact (Hj_max i' Hi').
Qed.

Theorem Max_complete :
  forall (n bits_param : nat) (inputs : list Z),
  (n >= 1)%nat -> (0 < bits_param)%nat ->
  length inputs = n ->
  (forall i, (i < n)%nat -> 0 <= nth i inputs 0 < 2 ^ Z.of_nat bits_param) ->
  exists (idx out : Z),
    0 <= idx < Z.of_nat n /\
    out = nth (Z.to_nat idx) inputs 0 /\
    (forall i, (i < n)%nat -> nth i inputs 0 <= out).
Proof.
  intros n bits_param inputs Hn Hbits Hlen Hrange.
  assert (Hlen_pos : (1 <= length inputs)%nat) by lia.
  destruct (list_has_max inputs Hlen_pos) as [j [Hj_lt Hj_max]].
  exists (Z.of_nat j), (nth j inputs 0).
  split.
  { split; [lia |]. rewrite Hlen in Hj_lt. lia. }
  split.
  { rewrite Nat2Z.id. reflexivity. }
  intros i Hi. rewrite Hlen in Hj_max. apply Hj_max. lia.
Qed.

