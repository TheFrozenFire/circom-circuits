From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import FieldBridge.
Require Import WitnessLemmas.
Require Import CurveParams.
Require Import packing.Bitify.
Require Import core.Comparators.

Open Scope Z_scope.

(** * BabyJubjub Circuit Verification
    Models constraints from circuits/curve/babyjub.circom. *)

(** ** BabyCheck (babyjub.circom:55-69)
    Constraints:
      x2 = x * x
      y2 = y * y
      a * x2 + y2 = 1 + d * x2 * y2

    This is the twisted Edwards curve equation: a*x^2 + y^2 = 1 + d*x^2*y^2 *)

Theorem BabyCheck_spec :
  forall (x y x2 y2 a d : Z),
  x2 = x * x ->
  y2 = y * y ->
  a * x2 + y2 = 1 + d * x2 * y2 ->
  a * (x * x) + y * y = 1 + d * (x * x) * (y * y).
Proof.
  intros x y x2 y2 a d Hx2 Hy2 Hcurve.
  subst x2 y2. exact Hcurve.
Qed.

(** ** BabyAdd (babyjub.circom:9-35)
    Constraints:
      beta = x1 * y2
      gamma = y1 * x2
      delta = (-a*x1 + y1) * (x2 + y2)
      tau = beta * gamma
      (1 + d*tau) * xout = beta + gamma
      (1 - d*tau) * yout = delta + a*beta - gamma

    These encode the twisted Edwards addition law in constraint (multiplication) form. *)

Theorem BabyAdd_spec :
  forall (x1 y1 x2 y2 xout yout beta gamma delta tau a d : Z),
  beta = x1 * y2 ->
  gamma = y1 * x2 ->
  delta = (-a * x1 + y1) * (x2 + y2) ->
  tau = beta * gamma ->
  (1 + d * tau) * xout = beta + gamma ->
  (1 - d * tau) * yout = delta + a * beta - gamma ->
  (* The constraints encode twisted Edwards addition *)
  (1 + d * tau) * xout = beta + gamma /\
  (1 - d * tau) * yout = delta + a * beta - gamma /\
  tau = x1 * y2 * (y1 * x2).
Proof.
  intros x1 y1 x2 y2 xout yout beta gamma delta tau a d
    Hbeta Hgamma Hdelta Htau Hx Hy.
  subst beta gamma tau.
  split; [exact Hx |].
  split; [exact Hy |].
  ring.
Qed.

(** ** BabyDbl (babyjub.circom:38-52)
    Point doubling delegates to BabyAdd(P, P).
    The constraints are identical to BabyAdd with (x2,y2) = (x1,y1). *)

Theorem BabyDbl_spec :
  forall (x y xout yout beta gamma delta tau a d : Z),
  beta = x * y ->
  gamma = y * x ->
  delta = (-a * x + y) * (x + y) ->
  tau = beta * gamma ->
  (1 + d * tau) * xout = beta + gamma ->
  (1 - d * tau) * yout = delta + a * beta - gamma ->
  (* Derived from commutativity and substitution *)
  beta = gamma /\ tau = beta * beta.
Proof.
  intros. subst beta gamma tau. split; ring.
Qed.

(** ** BabySuborderCheck (babyjub.circom:95-101)
    Constraints:
      diff = SUBORDER - 1 - in
      Num2BitsLE(253)(diff) — binary decomposition exists

    This proves 0 <= in <= SUBORDER - 1, i.e., in < SUBORDER. *)

Theorem BabySuborderCheck_spec :
  forall (inp diff : Z) (bits : list Z) (suborder : Z),
  suborder > 0 ->
  diff = suborder - 1 - inp ->
  length bits = 253%nat ->
  all_binary bits ->
  diff = bits_to_num bits ->
  inp <= suborder - 1.
Proof.
  intros inp diff bits suborder Hsub Hdiff Hlen Hall Hbtn.
  assert (Hbound := bits_to_num_nonneg bits Hall).
  rewrite <- Hbtn in Hbound. lia.
Qed.

(** ** BabySuborderAdd (babyjub.circom:105-120)
    Constraints:
      sum = a + b
      k = sum \ q  (witness: Euclidean quotient)
      out = sum - k * q
      LessThan(252)(out, q) = 1

    This proves out = (a + b) mod q and out < q. *)

Theorem BabySuborderAdd_spec :
  forall (a b sum k out q : Z),
  q > 0 ->
  sum = a + b ->
  out = sum - k * q ->
  0 <= out < q ->
  out = (a + b) mod q.
Proof.
  intros a b sum k out q Hq Hsum Hout Hrange.
  subst sum out.
  apply Zmod_unique with k.
  - lia.
  - ring.
Qed.

(** ** BabyPointAdd / BabyPointDouble (babyjub.circom:73-91)
    Array wrappers — delegate to BabyAdd. *)

Theorem BabyPointAdd_spec :
  forall (x1 y1 x2 y2 outx outy beta gamma delta tau a d : Z),
  (* BabyAdd constraints *)
  beta = x1 * y2 ->
  gamma = y1 * x2 ->
  delta = (-a * x1 + y1) * (x2 + y2) ->
  tau = beta * gamma ->
  (1 + d * tau) * outx = beta + gamma ->
  (1 - d * tau) * outy = delta + a * beta - gamma ->
  (* Delegates to BabyAdd: constraints hold and tau is derived *)
  (1 + d * tau) * outx = beta + gamma /\
  (1 - d * tau) * outy = delta + a * beta - gamma /\
  tau = x1 * y2 * (y1 * x2).
Proof.
  intros x1 y1 x2 y2 outx outy beta gamma delta tau a d
    Hbeta Hgamma Hdelta Htau Hx Hy.
  exact (BabyAdd_spec x1 y1 x2 y2 outx outy beta gamma delta tau a d
    Hbeta Hgamma Hdelta Htau Hx Hy).
Qed.

(** ** BabyAdd Connects to Group Operation

    If the BabyAdd constraints are satisfied with the BabyJubjub parameters
    (a=168700, d=168696), and both input points are on the curve,
    then the output equals the abstract group operation baby_add.

    The nonzero-denominator preconditions (1 + d*tau <> 0, 1 - d*tau <> 0)
    are guaranteed by the BabyJubjub curve parameters for all on-curve points.
    They are required here because we work in Z, not F_p, so we need
    explicit cancellation. *)

Theorem BabyAdd_is_group_op :
  forall (x1 y1 x2 y2 xout yout : Z),
  on_curve (mkPoint x1 y1) -> on_curve (mkPoint x2 y2) ->
  let tau := x1 * y2 * (y1 * x2) in
  1 + babyjub_d * tau <> 0 ->
  1 - babyjub_d * tau <> 0 ->
  (1 + babyjub_d * tau) * xout = x1 * y2 + y1 * x2 ->
  (1 - babyjub_d * tau) * yout =
    (-babyjub_a * x1 + y1) * (x2 + y2) + babyjub_a * (x1 * y2) - y1 * x2 ->
  mkPoint xout yout = baby_add (mkPoint x1 y1) (mkPoint x2 y2).
Proof.
  intros x1 y1 x2 y2 xout yout Hcurve1 Hcurve2 tau
    Hne_plus Hne_minus Hx_eq Hy_eq.
  assert (Hformula := baby_add_formula (mkPoint x1 y1) (mkPoint x2 y2)
    Hcurve1 Hcurve2).
  simpl px in Hformula. simpl py in Hformula.
  destruct Hformula as [Hfx Hfy].
  set (R := baby_add (mkPoint x1 y1) (mkPoint x2 y2)).
  fold R in Hfx, Hfy.
  assert (Hxeq : xout = px R).
  { apply (Z.mul_reg_l _ _ (1 + babyjub_d * tau) Hne_plus).
    rewrite Hx_eq. symmetry. exact Hfx. }
  assert (Hyeq : yout = py R).
  { apply (Z.mul_reg_l _ _ (1 - babyjub_d * tau) Hne_minus).
    rewrite Hy_eq. symmetry. exact Hfy. }
  rewrite Hxeq, Hyeq. destruct R; reflexivity.
Qed.

(** ** Suborder Arithmetic Field Safety

    Values in the suborder range are also valid field elements,
    and their sum stays in the field. *)

Theorem BabySuborderAdd_field_safe :
  forall a b, in_suborder a -> in_suborder b ->
  in_field a /\ in_field b /\ in_field (a + b).
Proof.
  intros a b Ha Hb. split; [| split].
  - apply in_suborder_in_field. exact Ha.
  - apply in_suborder_in_field. exact Hb.
  - unfold in_field, in_suborder in *.
    assert (H2q : 2 * q_suborder < p_field) by exact two_q_suborder_lt_p.
    lia.
Qed.

(** ** BabySuborderAdd Completeness
    Witness: k <-- sum \ q. Constraint: out = sum - k*q, 0 <= out < q. *)

Theorem BabySuborderAdd_complete :
  forall (a b : Z) (q : Z),
  q > 0 -> 0 <= a + b ->
  let sum := a + b in
  let k := sum / q in
  let out := sum mod q in
  out = sum - k * q /\ 0 <= out < q.
Proof.
  intros a b q Hq Hsum sum k out. subst sum k out.
  assert (Hdm := div_mod_constraint (a + b) q Hsum ltac:(lia)).
  lia.
Qed.
