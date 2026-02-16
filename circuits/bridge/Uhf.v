From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Polynomial Universal Hash Function Verification
    Models constraints from circuits/bridge/uhf.circom. *)

(** ** PolyUHF (uhf.circom:15-34)
    UHF(r, x) = x[0] + x[1]*r + x[2]*r^2 + ... + x[n-1]*r^(n-1)

    Evaluated using Horner's method (right-to-left):
      acc[0] = x[n-1] * r + x[n-2]
      acc[k] = acc[k-1] * r + x[n-2-k]
      out = acc[n-3] * r + x[0]

    Constraints: exactly n-1 quadratic constraints. *)

Fixpoint poly_eval (coeffs : list Z) (r : Z) : Z :=
  match coeffs with
  | [] => 0
  | c :: rest => c + r * poly_eval rest r
  end.

Lemma poly_eval_cons : forall c rest r,
  poly_eval (c :: rest) r = c + r * poly_eval rest r.
Proof. intros. reflexivity. Qed.

Lemma poly_eval_app_singleton : forall l x r,
  poly_eval (l ++ [x]) r = poly_eval l r + r ^ Z.of_nat (length l) * x.
Proof.
  induction l as [| c rest IH].
  - intros x r. simpl app. simpl poly_eval. simpl length.
    rewrite Z.pow_0_r. ring.
  - intros x r. simpl app. rewrite !poly_eval_cons.
    rewrite IH. simpl length. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia. ring.
Qed.

Lemma poly_eval_removelast_last : forall (l : list Z) (d : Z) r,
  l <> [] ->
  poly_eval l r = poly_eval (removelast l) r +
    r ^ Z.of_nat (length (removelast l)) * last l d.
Proof.
  intros l d r Hne.
  assert (Heq : l = removelast l ++ [last l d])
    by (apply app_removelast_last; assumption).
  rewrite Heq at 1.
  apply poly_eval_app_singleton.
Qed.

Fixpoint horner_chain (seed : Z) (r : Z) (coeffs : list Z) : Z :=
  match coeffs with
  | [] => seed
  | c :: rest => horner_chain (seed * r + c) r rest
  end.

Lemma horner_chain_step : forall seed r c rest,
  horner_chain seed r (c :: rest) = horner_chain (seed * r + c) r rest.
Proof. intros. reflexivity. Qed.

Lemma horner_chain_poly_eval : forall coeffs r seed,
  horner_chain seed r coeffs =
    seed * r ^ Z.of_nat (length coeffs) + poly_eval (rev coeffs) r.
Proof.
  induction coeffs as [| c rest IH].
  - intros. simpl. ring.
  - intros r seed. rewrite horner_chain_step.
    rewrite IH. simpl length. simpl rev.
    rewrite poly_eval_app_singleton. rewrite length_rev.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    ring.
Qed.

Theorem PolyUHF_correct : forall (x : list Z) (r out : Z),
  (2 <= length x)%nat ->
  out = horner_chain (last x 0) r (rev (removelast x)) ->
  out = poly_eval x r.
Proof.
  intros x r out Hlen Hout.
  rewrite Hout.
  rewrite horner_chain_poly_eval.
  rewrite rev_involutive.
  rewrite length_rev.
  assert (Hlen_rm : length (removelast x) = (length x - 1)%nat).
  { rewrite removelast_firstn_len. rewrite length_firstn. lia. }
  rewrite Hlen_rm.
  rewrite (poly_eval_removelast_last x 0 r)
    by (destruct x; [simpl in Hlen; lia | discriminate]).
  rewrite Hlen_rm. ring.
Qed.

Theorem PolyUHF_base_correct : forall (x0 x1 r out : Z),
  out = x1 * r + x0 ->
  out = poly_eval [x0; x1] r.
Proof.
  intros x0 x1 r out Hout. simpl. lia.
Qed.
