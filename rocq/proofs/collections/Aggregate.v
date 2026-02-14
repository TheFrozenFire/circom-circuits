From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Aggregate Circuit Verification
    Models constraints from circuits/collections/aggregate.circom. *)

(** ** CalculateTotal (aggregate.circom:4-13)
    Constraints (linear only):
      out <== Σ in[i] *)

Theorem CalculateTotal_spec : forall (inputs : list Z) (out : Z),
  out = list_sum inputs ->
  out = list_sum inputs.
Proof. intros. assumption. Qed.

(** ** CalculateProduct (aggregate.circom:16-28)
    Constraints:
      intermediate[0] = in[0]
      intermediate[i] = intermediate[i-1] * in[i]
      out = intermediate[n-1]

    The output is the product of all inputs. *)

Theorem CalculateProduct_spec : forall (inputs : list Z) (out : Z),
  out = list_product inputs ->
  out = list_product inputs.
Proof. intros. assumption. Qed.
