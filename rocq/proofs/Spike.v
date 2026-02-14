From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

Open Scope Z_scope.

(** Horner evaluation of a polynomial: x[0] + x[1]*r + x[2]*r^2 + ... *)
Fixpoint horner (r : Z) (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest => x + r * horner r rest
  end.

(** Sum of a list *)
Fixpoint sum_list (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest => x + sum_list rest
  end.

(** Evaluating at r=1 gives the sum *)
Lemma horner_r1 : forall xs, horner 1 xs = sum_list xs.
Proof.
  induction xs as [| x rest IH].
  - reflexivity.
  - simpl. rewrite IH. destruct (sum_list rest); reflexivity.
Qed.

(** Two different vectors produce different UHF values *)
Lemma uhf_distinguishes :
  horner 7 [3; 5; 11; 13] <> horner 7 [13; 11; 5; 3].
Proof.
  simpl. discriminate.
Qed.

(** Horner matches explicit polynomial evaluation *)
Lemma horner_example :
  horner 7 [3; 5; 11; 13] = 3 + 5*7 + 11*7^2 + 13*7^3.
Proof.
  simpl. reflexivity.
Qed.
