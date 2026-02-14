From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Collections Circuit Verification
    Models constraints from circuits/collections/ordered.circom,
    circuits/collections/selector.circom, circuits/linalg/selection.circom,
    and circuits/linalg/vector.circom (VectorMean). *)

(** ** Ordered (ordered.circom:9-28)
    Constraints (ascending case):
      lt[i].out = 1  where lt[i] = LessThan(in[i], in[i+1])

    Assuming LessThan_sound: (lt.out = 1 <-> a < b),
    the sequence is strictly ascending. *)

(** Helper: strict ordering of a list via adjacent comparisons. *)
Fixpoint strictly_ascending (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as rest) => x < y /\ strictly_ascending rest
  end.

(** If every adjacent pair satisfies the less-than relation,
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
Fixpoint strictly_descending (l : list Z) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as rest) => x > y /\ strictly_descending rest
  end.

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

(** Simplified Max theorem: out >= all elements. *)
Theorem Max_ge_all : forall (inputs : list Z) (out : Z),
  (forall i, (i < length inputs)%nat -> out >= nth i inputs 0) ->
  forall i, (i < length inputs)%nat -> nth i inputs 0 <= out.
Proof.
  intros inputs out Hge i Hi. specialize (Hge i Hi). lia.
Qed.

(** ** VectorMean (vector.circom:140-180)
    Per dimension j:
      s[j] = Σ v[i][j]
      s[j] = q[j] * k + r[j]
      0 <= r[j] < k    (range check + LessThan)
      out[j] = q[j]

    We prove: q and r are the Euclidean quotient and remainder. *)

Theorem VectorMean_correct : forall (k : Z) (s q r : Z),
  k > 0 ->
  s = q * k + r ->
  0 <= r < k ->
  q = s / k /\ r = s mod k.
Proof.
  intros k s q r Hk Hdiv Hrange.
  split.
  - apply Zdiv_unique with r; lia.
  - apply Zmod_unique with q; lia.
Qed.

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
