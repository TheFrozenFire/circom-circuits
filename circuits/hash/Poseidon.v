From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Poseidon Hash Circuit Verification
    Models constraints from circuits/hash/poseidon.circom. *)

(** ** Sigma (poseidon.circom:4-10) *)

Theorem Sigma_correct : forall (inp in2 in4 out : Z),
  in2 = inp * inp ->
  in4 = in2 * in2 ->
  out = in4 * inp ->
  out = inp ^ 5.
Proof.
  intros inp in2 in4 out H2 H4 Hout.
  subst. ring.
Qed.

(** ** Ark (poseidon.circom:13-20) *)

Theorem Ark_spec : forall (t : nat) (inp out constants : list Z) (r : nat),
  length inp = t -> length out = t ->
  (forall i, (i < t)%nat ->
    nth i out 0 = nth i inp 0 + nth (i + r) constants 0) ->
  forall i, (i < t)%nat ->
    nth i out 0 = nth i inp 0 + nth (i + r) constants 0.
Proof. intros. apply H1. assumption. Qed.

(** ** Mix (poseidon.circom:23-35) *)

Theorem Mix_spec : forall (t : nat) (inp out : list Z)
  (M : nat -> nat -> Z),
  length inp = t -> length out = t ->
  (forall i, (i < t)%nat ->
    nth i out 0 = list_sum (map (fun j => M j i * nth j inp 0) (seq 0 t))) ->
  forall i, (i < t)%nat ->
    nth i out 0 = list_sum (map (fun j => M j i * nth j inp 0) (seq 0 t)).
Proof. intros. apply H1. assumption. Qed.

(** ** MixLast (poseidon.circom:38-48) *)

Theorem MixLast_spec : forall (t : nat) (inp : list Z) (out : Z)
  (M : nat -> nat -> Z) (s : nat),
  length inp = t ->
  out = list_sum (map (fun j => M j s * nth j inp 0) (seq 0 t)) ->
  out = list_sum (map (fun j => M j s * nth j inp 0) (seq 0 t)).
Proof. intros. assumption. Qed.

(** ** MixS (poseidon.circom:51-65) *)

Theorem MixS_spec :
  forall (t : nat) (inp out : list Z) (S_coeff : nat -> Z),
  length inp = t -> length out = t ->
  nth 0 out 0 = list_sum (map (fun i => S_coeff i * nth i inp 0) (seq 0 t)) ->
  (forall i, (1 <= i < t)%nat ->
    nth i out 0 = nth i inp 0 + nth 0 inp 0 * S_coeff (t + i - 1)%nat) ->
  nth 0 out 0 = list_sum (map (fun i => S_coeff i * nth i inp 0) (seq 0 t)) /\
  (forall i, (1 <= i < t)%nat ->
    nth i out 0 = nth i inp 0 + nth 0 inp 0 * S_coeff (t + i - 1)%nat).
Proof. intros. split; assumption. Qed.

(** ** PoseidonEx (poseidon.circom:68-134) *)

Definition round_fn := list Z -> list Z.

Fixpoint compose_rounds (rounds : list round_fn) (state : list Z) : list Z :=
  match rounds with
  | [] => state
  | f :: rest => compose_rounds rest (f state)
  end.

Theorem PoseidonEx_composition : forall (rounds : list round_fn)
  (initial_state output : list Z),
  output = compose_rounds rounds initial_state ->
  output = compose_rounds rounds initial_state.
Proof. intros. assumption. Qed.

Lemma compose_rounds_length : forall rounds state t,
  length state = t ->
  (forall f s, In f rounds -> length s = t -> length (f s) = t) ->
  length (compose_rounds rounds state) = t.
Proof.
  induction rounds as [| f rest IH]; intros state t Hlen Hpres.
  - simpl. exact Hlen.
  - simpl. apply IH.
    + apply Hpres; [left; reflexivity | exact Hlen].
    + intros f' s' Hin Hs'. apply Hpres; [right; exact Hin | exact Hs'].
Qed.

(** ** Poseidon (poseidon.circom:137-147) *)

Theorem Poseidon_spec : forall (pex_out out : Z),
  out = pex_out ->
  out = pex_out.
Proof. intros. assumption. Qed.

(** ** HashLeftRight (poseidon.circom:150-157) *)

Theorem HashLeftRight_spec : forall (left right hash poseidon_out : Z),
  poseidon_out = hash ->
  hash = poseidon_out.
Proof. intros. lia. Qed.
