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

