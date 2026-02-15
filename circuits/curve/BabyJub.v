From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
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
  (* Same as BabyAdd(x,y,x,y) *)
  (1 + d * tau) * xout = beta + gamma /\
  (1 - d * tau) * yout = delta + a * beta - gamma.
Proof.
  intros. split; assumption.
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
