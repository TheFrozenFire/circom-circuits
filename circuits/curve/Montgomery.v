From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.
Require Import FieldBridge.

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
  (* 1 - y mod p is in [0, p), and nonzero, so it's a valid field element for inversion *)
  set (one_minus_y := (1 - y) mod p_field).
  assert (Homy_field : in_field one_minus_y).
  { unfold one_minus_y, in_field. split.
    - apply Z.mod_pos_bound. pose proof p_field_pos. lia.
    - apply Z.mod_pos_bound. pose proof p_field_pos. lia. }
  assert (Homy_nz : one_minus_y <> 0) by exact Hny.
  (* Build u = (1 + y) * fp_inv(1 - y) mod p *)
  set (u := ((1 + y) * fp_inv one_minus_y) mod p_field).
  assert (Hu_field : in_field u).
  { unfold u, in_field. split.
    - apply Z.mod_pos_bound. pose proof p_field_pos. lia.
    - apply Z.mod_pos_bound. pose proof p_field_pos. lia. }
  (* x is in field and nonzero, so fp_inv x is valid *)
  assert (Hx_nz : x <> 0) by exact Hnx.
  set (v := (u * fp_inv x) mod p_field).
  assert (Hv_field : in_field v).
  { unfold v, in_field. split.
    - apply Z.mod_pos_bound. pose proof p_field_pos. lia.
    - apply Z.mod_pos_bound. pose proof p_field_pos. lia. }
  exists u, v. split; [exact Hu_field |]. split; [exact Hv_field |].
  assert (Hp_pos : 0 < p_field) by exact p_field_pos.
  assert (Hinv_omy : (one_minus_y * fp_inv one_minus_y) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  assert (Hinv_x : (x * fp_inv x) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  (* Helper: (1-y) * fp_inv(omy) ≡ 1 (mod p) since (1-y) ≡ omy (mod p) *)
  assert (Hinv_1my : ((1 - y) * fp_inv one_minus_y) mod p_field = 1).
  { transitivity ((one_minus_y * fp_inv one_minus_y) mod p_field).
    - symmetry. apply Z.mul_mod_idemp_l. lia.
    - exact Hinv_omy. }
  split.
  - (* (u * (1 - y) - (1 + y)) mod p = 0 *)
    apply mod_eq_sub_zero; [lia |].
    unfold u. rewrite Z.mul_mod_idemp_l by lia.
    (* ((1+y) * fp_inv omy * (1-y)) mod p = (1+y) mod p *)
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm (fp_inv one_minus_y) (1 - y)).
    rewrite Z.mul_mod by lia.
    rewrite Hinv_1my. rewrite Z.mul_1_r. rewrite Z.mod_mod by lia.
    reflexivity.
  - (* (v * x - u) mod p = 0 *)
    apply mod_eq_sub_zero; [lia |].
    unfold v. rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc. rewrite Z.mul_mod by lia.
    rewrite (Z.mul_comm (fp_inv x) x). rewrite Hinv_x.
    rewrite Z.mul_1_r. rewrite Z.mod_mod by lia. reflexivity.
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
  assert (Hp_pos : 0 < p_field) by exact p_field_pos.
  set (u_plus_1 := (u + 1) mod p_field).
  assert (Hu1_field : in_field u_plus_1).
  { unfold u_plus_1, in_field. split; apply Z.mod_pos_bound; lia. }
  set (x := (u * fp_inv v) mod p_field).
  set (y := ((u - 1) * fp_inv u_plus_1) mod p_field).
  assert (Hx_field : in_field x).
  { unfold x, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hy_field : in_field y).
  { unfold y, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hinv_v : (v * fp_inv v) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  assert (Hinv_u1 : (u_plus_1 * fp_inv u_plus_1) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  exists x, y. split; [exact Hx_field |]. split; [exact Hy_field |].
  (* Helper: (u+1) * fp_inv(u_plus_1) ≡ 1 mod p since u+1 ≡ u_plus_1 mod p *)
  assert (Hinv_u1p : ((u + 1) * fp_inv u_plus_1) mod p_field = 1).
  { transitivity ((u_plus_1 * fp_inv u_plus_1) mod p_field).
    - symmetry. apply Z.mul_mod_idemp_l. lia.
    - exact Hinv_u1. }
  split.
  - (* (x * v - u) mod p = 0 *)
    apply mod_eq_sub_zero; [lia |].
    unfold x. rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc. rewrite Z.mul_mod by lia.
    rewrite (Z.mul_comm (fp_inv v) v). rewrite Hinv_v.
    rewrite Z.mul_1_r. rewrite Z.mod_mod by lia. reflexivity.
  - (* (y * (u+1) - (u-1)) mod p = 0 *)
    apply mod_eq_sub_zero; [lia |].
    unfold y. rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm (fp_inv u_plus_1) (u + 1)).
    rewrite Z.mul_mod by lia.
    rewrite Hinv_u1p.
    rewrite Z.mul_1_r. rewrite Z.mod_mod by lia. reflexivity.
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
  assert (Hp_pos : 0 < p_field) by exact p_field_pos.
  set (dx := (x2 - x1) mod p_field).
  assert (Hdx_field : in_field dx).
  { unfold dx, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hinv_dx : (dx * fp_inv dx) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  set (lam := ((y2 - y1) * fp_inv dx) mod p_field).
  set (x3 := (B * lam * lam - A - x1 - x2) mod p_field).
  set (y3 := (lam * (x1 - x3) - y1) mod p_field).
  assert (Hlam_field : in_field lam).
  { unfold lam, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hx3_field : in_field x3).
  { unfold x3, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hy3_field : in_field y3).
  { unfold y3, in_field. split; apply Z.mod_pos_bound; lia. }
  exists lam, x3, y3.
  split; [exact Hlam_field |]. split; [exact Hx3_field |]. split; [exact Hy3_field |].
  (* Helper: (x2-x1) * fp_inv(dx) ≡ 1 mod p since x2-x1 ≡ dx mod p *)
  assert (Hinv_dx2 : ((x2 - x1) * fp_inv dx) mod p_field = 1).
  { transitivity ((dx * fp_inv dx) mod p_field).
    - symmetry. apply Z.mul_mod_idemp_l. lia.
    - exact Hinv_dx. }
  split.
  - (* (lam * (x2-x1) - (y2-y1)) mod p = 0 *)
    apply mod_eq_sub_zero; [lia |].
    unfold lam. rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm (fp_inv dx) (x2 - x1)).
    rewrite Z.mul_mod by lia.
    rewrite Hinv_dx2. rewrite Z.mul_1_r. rewrite Z.mod_mod by lia.
    reflexivity.
  - split.
    + (* (x3 - (B*lam*lam - A - x1 - x2)) mod p = 0 *)
      unfold x3.
      rewrite Zminus_mod_idemp_l. rewrite Z.sub_diag.
      rewrite Z.mod_0_l by lia. reflexivity.
    + (* (y3 - (lam*(x1-x3) - y1)) mod p = 0 *)
      unfold y3.
      rewrite Zminus_mod_idemp_l. rewrite Z.sub_diag.
      rewrite Z.mod_0_l by lia. reflexivity.
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
  assert (Hp_pos : 0 < p_field) by exact p_field_pos.
  set (den := (2 * B * y1) mod p_field).
  assert (Hden_field : in_field den).
  { unfold den, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hinv_den : (den * fp_inv den) mod p_field = 1)
    by (apply fp_inv_spec; assumption).
  set (x1_2 := x1 * x1).
  set (num := 3 * x1_2 + 2 * A * x1 + 1).
  set (lam := (num * fp_inv den) mod p_field).
  set (x3 := (B * lam * lam - A - 2 * x1) mod p_field).
  set (y3 := (lam * (x1 - x3) - y1) mod p_field).
  assert (Hlam_field : in_field lam).
  { unfold lam, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hx3_field : in_field x3).
  { unfold x3, in_field. split; apply Z.mod_pos_bound; lia. }
  assert (Hy3_field : in_field y3).
  { unfold y3, in_field. split; apply Z.mod_pos_bound; lia. }
  exists lam, x3, y3, x1_2.
  split; [exact Hlam_field |]. split; [exact Hx3_field |]. split; [exact Hy3_field |].
  split; [reflexivity |].
  split.
  (* Helper: (2*B*y1) * fp_inv(den) ≡ 1 mod p since 2*B*y1 ≡ den mod p *)
  assert (Hinv_den2 : ((2 * B * y1) * fp_inv den) mod p_field = 1).
  { transitivity ((den * fp_inv den) mod p_field).
    - symmetry. apply Z.mul_mod_idemp_l. lia.
    - exact Hinv_den. }
  - (* (lam * (2*B*y1) - num) mod p = 0 *)
    apply mod_eq_sub_zero; [lia |].
    unfold lam. rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm (fp_inv den) (2 * B * y1)).
    rewrite Z.mul_mod by lia.
    rewrite Hinv_den2. rewrite Z.mul_1_r. rewrite Z.mod_mod by lia.
    reflexivity.
  - split.
    + unfold x3. rewrite Zminus_mod_idemp_l. rewrite Z.sub_diag.
      rewrite Z.mod_0_l by lia. reflexivity.
    + unfold y3. rewrite Zminus_mod_idemp_l. rewrite Z.sub_diag.
      rewrite Z.mod_0_l by lia. reflexivity.
Qed.
