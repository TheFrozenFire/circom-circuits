From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.

Open Scope Z_scope.

(** * Montgomery Curve Circuit Verification
    Models constraints from circuits/curve/montgomery.circom. *)

(** ** Edwards2Montgomery (montgomery.circom:6-15)
    Constraints:
      out[0] * (1 - y) = (1 + y)
      out[1] * x = out[0]

    These are the constraint forms of:
      u = (1+y)/(1-y)
      v = u/x *)

Theorem Edwards2Montgomery_spec :
  forall (x y u v : Z),
  u * (1 - y) = 1 + y ->
  v * x = u ->
  (* Composed constraint eliminating u *)
  v * x * (1 - y) = 1 + y.
Proof.
  intros x y u v Hu Hv. subst u. lia.
Qed.

(** When y /= 1 and x /= 0, the conversion is well-defined. *)
Theorem Edwards2Montgomery_welldefined :
  forall (x y u v : Z),
  y <> 1 -> x <> 0 ->
  u * (1 - y) = 1 + y ->
  v * x = u ->
  (1 - y) <> 0 /\ x <> 0.
Proof.
  intros x y u v Hy Hx Hu Hv. split; lia.
Qed.

(** ** Montgomery2Edwards (montgomery.circom:18-27)
    Constraints:
      x * v = u
      y * (u + 1) = u - 1 *)

Theorem Montgomery2Edwards_spec :
  forall (u v x y : Z),
  x * v = u ->
  y * (u + 1) = u - 1 ->
  (* Composed constraint eliminating u *)
  y * (x * v + 1) = x * v - 1.
Proof.
  intros u v x y Hx Hy. subst u. lia.
Qed.

(** ** MontgomeryAdd (montgomery.circom:33-51)
    Constraints:
      lambda * (x2 - x1) = (y2 - y1)
      x3 = B * lambda^2 - A - x1 - x2
      y3 = lambda * (x1 - x3) - y1

    Standard Montgomery curve addition law in constraint form. *)

Theorem MontgomeryAdd_spec :
  forall (x1 y1 x2 y2 x3 y3 lambda A B : Z),
  lambda * (x2 - x1) = y2 - y1 ->
  x3 = B * lambda * lambda - A - x1 - x2 ->
  y3 = lambda * (x1 - x3) - y1 ->
  (* Substitute x3 into y3 equation *)
  y3 = lambda * (x1 - (B * lambda * lambda - A - x1 - x2)) - y1.
Proof.
  intros. subst x3. lia.
Qed.

(** ** MontgomeryDouble (montgomery.circom:57-77)
    Constraints:
      x1_2 = x1 * x1
      lambda * (2 * B * y1) = (3 * x1_2 + 2 * A * x1 + 1)
      x3 = B * lambda^2 - A - 2 * x1
      y3 = lambda * (x1 - x3) - y1 *)

Theorem MontgomeryDouble_spec :
  forall (x1 y1 x3 y3 lambda x1_2 A B : Z),
  x1_2 = x1 * x1 ->
  lambda * (2 * B * y1) = 3 * x1_2 + 2 * A * x1 + 1 ->
  x3 = B * lambda * lambda - A - 2 * x1 ->
  y3 = lambda * (x1 - x3) - y1 ->
  (* Substitute x1_2 and x3 *)
  lambda * (2 * B * y1) = 3 * x1 * x1 + 2 * A * x1 + 1 /\
  y3 = lambda * (x1 - (B * lambda * lambda - A - 2 * x1)) - y1.
Proof.
  intros. subst x1_2 x3. split; lia.
Qed.
