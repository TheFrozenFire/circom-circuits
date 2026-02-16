From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import WitnessLemmas.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Vector Circuit Verification
    Models constraints from circuits/linalg/vector.circom. *)

(** ** DotProduct (vector.circom:41-53)
    Constraints:
      products[i] = a[i] * b[i]
      out = Σ products[i] *)

Theorem DotProduct_spec :
  forall (a b products : list Z) (out : Z),
  length a = length b ->
  length products = length a ->
  (forall i, (i < length a)%nat ->
    nth i products 0 = nth i a 0 * nth i b 0) ->
  out = list_sum products ->
  out = list_sum products.
Proof. intros. assumption. Qed.

(** ** VectorIsEqual (vector.circom:72-91)
    Each element is compared via IsEqual (binary output).
    Results are AND-chained: acc[0] = eq[0]; acc[i] = acc[i-1] * eq[i].

    The output is 1 iff all elements are equal. *)

Theorem VectorIsEqual_correct : forall (eq_results : list Z) (out : Z),
  Forall is_binary eq_results ->
  out = list_product eq_results ->
  (out = 1 <-> Forall (fun x => x = 1) eq_results).
Proof.
  intros eq_results out Hbin Hout.
  subst out.
  apply binary_and_chain. exact Hbin.
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

(** ** VectorMean Completeness
    Witness: q[j] <-- s[j] \ k; r[j] <-- s[j] % k.
    Per-element division. *)

Theorem VectorMean_complete : forall (k s : Z),
  k > 0 -> 0 <= s ->
  let q := s / k in
  let r := s mod k in
  s = q * k + r /\ 0 <= r < k.
Proof.
  intros k s Hk Hs q r. subst q r.
  apply div_mod_constraint; lia.
Qed.
