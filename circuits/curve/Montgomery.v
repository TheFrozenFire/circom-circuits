From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.
Require Import FieldBridge.

Open Scope Z_scope.

Set Default Proof Using "Type".

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

(** ** Edwards2Montgomery Completeness
    Witness: u <-- (1+y)/(1-y), v <-- u/x
    Preconditions: y != 1 (so 1-y != 0 in F_p), x != 0 *)

Theorem Edwards2Montgomery_complete : forall x y : Z,
  in_field x -> in_field y ->
  (1 - y) mod p_field <> 0 -> x <> 0 ->
  exists u v : Z,
    in_field u /\ in_field v /\
    (u * (1 - y) - (1 + y)) mod p_field = 0 /\
    (v * x - u) mod p_field = 0.
Proof.
  intros x y Hx Hy Hny Hnx.
  set (one_minus_y := (1 - y) mod p_field).
  assert (Homy_field : in_field one_minus_y) by (unfold one_minus_y; solve_in_field_modp).
  set (u := ((1 + y) * fp_inv one_minus_y) mod p_field).
  assert (Hu_field : in_field u) by (unfold u; solve_in_field_modp).
  set (v := (u * fp_inv x) mod p_field).
  assert (Hv_field : in_field v) by (unfold v; solve_in_field_modp).
  exists u, v. split; [exact Hu_field |]. split; [exact Hv_field |].
  assert (Hinv_omy : (one_minus_y * fp_inv one_minus_y) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  assert (Hinv_x : (x * fp_inv x) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  assert (Hinv_1my : ((1 - y) * fp_inv one_minus_y) mod p_field = 1)
    by derive_raw_fp_inv Hinv_omy.
  split.
  - solve_mod_zero. unfold u. fp_inv_cancel Hinv_1my.
  - solve_mod_zero. unfold v. fp_inv_cancel Hinv_x.
Qed.

(** ** Montgomery2Edwards Completeness
    Witness: x <-- u/v, y <-- (u-1)/(u+1)
    Preconditions: v != 0, (u + 1) mod p != 0 *)

Theorem Montgomery2Edwards_complete : forall u v : Z,
  in_field u -> in_field v ->
  v <> 0 -> (u + 1) mod p_field <> 0 ->
  exists x y : Z,
    in_field x /\ in_field y /\
    (x * v - u) mod p_field = 0 /\
    (y * (u + 1) - (u - 1)) mod p_field = 0.
Proof.
  intros u v Hu Hv Hv_nz Hu1_nz.
  set (u_plus_1 := (u + 1) mod p_field).
  assert (Hu1_field : in_field u_plus_1) by (unfold u_plus_1; solve_in_field_modp).
  set (x := (u * fp_inv v) mod p_field).
  set (y := ((u - 1) * fp_inv u_plus_1) mod p_field).
  assert (Hx_field : in_field x) by (unfold x; solve_in_field_modp).
  assert (Hy_field : in_field y) by (unfold y; solve_in_field_modp).
  assert (Hinv_v : (v * fp_inv v) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  assert (Hinv_u1 : (u_plus_1 * fp_inv u_plus_1) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  exists x, y. split; [exact Hx_field |]. split; [exact Hy_field |].
  assert (Hinv_u1p : ((u + 1) * fp_inv u_plus_1) mod p_field = 1)
    by derive_raw_fp_inv Hinv_u1.
  split.
  - solve_mod_zero. unfold x. fp_inv_cancel Hinv_v.
  - solve_mod_zero. unfold y. fp_inv_cancel Hinv_u1p.
Qed.

(** ** MontgomeryAdd Completeness
    Witness: lambda <-- (y2-y1)/(x2-x1)
             x3 <-- B*lambda^2 - A - x1 - x2
             y3 <-- lambda*(x1-x3) - y1
    Precondition: (x2 - x1) mod p != 0 *)

Theorem MontgomeryAdd_complete : forall x1 y1 x2 y2 A B : Z,
  in_field x1 -> in_field y1 -> in_field x2 -> in_field y2 ->
  in_field A -> in_field B ->
  (x2 - x1) mod p_field <> 0 ->
  exists lam x3 y3 : Z,
    in_field lam /\ in_field x3 /\ in_field y3 /\
    (lam * (x2 - x1) - (y2 - y1)) mod p_field = 0 /\
    (x3 - (B * lam * lam - A - x1 - x2)) mod p_field = 0 /\
    (y3 - (lam * (x1 - x3) - y1)) mod p_field = 0.
Proof.
  intros x1 y1 x2 y2 A B Hx1 Hy1 Hx2 Hy2 HA HB Hdx_nz.
  set (dx := (x2 - x1) mod p_field).
  assert (Hdx_field : in_field dx) by (unfold dx; solve_in_field_modp).
  assert (Hinv_dx : (dx * fp_inv dx) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  set (lam := ((y2 - y1) * fp_inv dx) mod p_field).
  set (x3 := (B * lam * lam - A - x1 - x2) mod p_field).
  set (y3 := (lam * (x1 - x3) - y1) mod p_field).
  assert (Hlam_field : in_field lam) by (unfold lam; solve_in_field_modp).
  assert (Hx3_field : in_field x3) by (unfold x3; solve_in_field_modp).
  assert (Hy3_field : in_field y3) by (unfold y3; solve_in_field_modp).
  exists lam, x3, y3.
  split; [exact Hlam_field |]. split; [exact Hx3_field |]. split; [exact Hy3_field |].
  assert (Hinv_dx2 : ((x2 - x1) * fp_inv dx) mod p_field = 1)
    by derive_raw_fp_inv Hinv_dx.
  split.
  - solve_mod_zero. unfold lam. fp_inv_cancel Hinv_dx2.
  - split; [unfold x3; solve_mod_self_zero | unfold y3; solve_mod_self_zero].
Qed.

(** ** MontgomeryDouble Completeness
    Witness: x1_2 <-- x1*x1
             lambda <-- (3*x1_2 + 2*A*x1 + 1) / (2*B*y1)
             x3 <-- B*lambda^2 - A - 2*x1
             y3 <-- lambda*(x1-x3) - y1
    Precondition: (2*B*y1) mod p != 0 *)

Theorem MontgomeryDouble_complete : forall x1 y1 A B : Z,
  in_field x1 -> in_field y1 -> in_field A -> in_field B ->
  (2 * B * y1) mod p_field <> 0 ->
  exists lam x3 y3 x1_2 : Z,
    in_field lam /\ in_field x3 /\ in_field y3 /\
    x1_2 = x1 * x1 /\
    (lam * (2 * B * y1) - (3 * x1_2 + 2 * A * x1 + 1)) mod p_field = 0 /\
    (x3 - (B * lam * lam - A - 2 * x1)) mod p_field = 0 /\
    (y3 - (lam * (x1 - x3) - y1)) mod p_field = 0.
Proof.
  intros x1 y1 A B Hx1 Hy1 HA HB Hden_nz.
  set (den := (2 * B * y1) mod p_field).
  assert (Hden_field : in_field den) by (unfold den; solve_in_field_modp).
  assert (Hinv_den : (den * fp_inv den) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  set (x1_2 := x1 * x1).
  set (num := 3 * x1_2 + 2 * A * x1 + 1).
  set (lam := (num * fp_inv den) mod p_field).
  set (x3 := (B * lam * lam - A - 2 * x1) mod p_field).
  set (y3 := (lam * (x1 - x3) - y1) mod p_field).
  assert (Hlam_field : in_field lam) by (unfold lam; solve_in_field_modp).
  assert (Hx3_field : in_field x3) by (unfold x3; solve_in_field_modp).
  assert (Hy3_field : in_field y3) by (unfold y3; solve_in_field_modp).
  exists lam, x3, y3, x1_2.
  split; [exact Hlam_field |]. split; [exact Hx3_field |]. split; [exact Hy3_field |].
  split; [reflexivity |].
  assert (Hinv_den2 : ((2 * B * y1) * fp_inv den) mod p_field = 1)
    by derive_raw_fp_inv Hinv_den.
  split.
  - solve_mod_zero. unfold lam. fp_inv_cancel Hinv_den2.
  - split; [unfold x3; solve_mod_self_zero | unfold y3; solve_mod_self_zero].
Qed.
