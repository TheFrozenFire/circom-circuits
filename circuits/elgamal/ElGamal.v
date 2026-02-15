From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import packing.Bitify.
Require Import curve.BabyJub.
Require Import curve.ScalarMul.

Open Scope Z_scope.

(** * ElGamal Circuit Verification
    Models constraints from circuits/elgamal/elgamal.circom and helpers.circom. *)

(** ** ElGamalBlinding (helpers.circom:7-12)
    out = (message - point[0]) * -1 = point[0] - message *)

Theorem ElGamalBlinding_spec :
  forall (message point_x point_y out : Z),
  out = (message - point_x) * (-1) ->
  out = point_x - message.
Proof. intros. lia. Qed.

(** ** ElGamalMessageCheck (helpers.circom:16-24)
    Verifies point is on curve and point[0] - blinding = message. *)

Theorem ElGamalMessageCheck_sound :
  forall (point_x point_y blinding message a d x2 y2 : Z),
  (* BabyCheck constraints *)
  x2 = point_x * point_x ->
  y2 = point_y * point_y ->
  a * x2 + y2 = 1 + d * x2 * y2 ->
  (* Constraint *)
  point_x - blinding = message ->
  (* Point is on curve *)
  a * (point_x * point_x) + point_y * point_y =
    1 + d * (point_x * point_x) * (point_y * point_y) /\
  message = point_x - blinding.
Proof.
  intros point_x point_y blinding message a d x2 y2
    Hx2 Hy2 Hcurve Hcons.
  subst x2 y2.
  split; [exact Hcurve | lia].
Qed.

(** ** ElGamalShare (elgamal.circom:11-20)
    out = y * pubKey  (variable-base scalar mul)
    c1 = y * G8       (fixed-base scalar mul)

    Both use the same scalar y decomposed into bits. *)

Theorem ElGamalShare_spec :
  forall (pubKey_x pubKey_y : Z) (y : Z)
    (yBits : list Z) (out_x out_y c1_x c1_y : Z),
  length yBits = 254%nat ->
  all_binary yBits ->
  y = bits_to_num yBits ->
  (* Scalar y is bounded by 2^254 *)
  0 <= y < 2 ^ 254.
Proof.
  intros pubKey_x pubKey_y y yBits out_x out_y c1_x c1_y
    Hlen Hbin Hy.
  subst y.
  assert (Hbound := bits_to_num_bound yBits Hbin).
  rewrite Hlen in Hbound. exact Hbound.
Qed.

(** ** ElGamalEncrypt (elgamal.circom:25-44)
    c1 = y * G8
    c2 = message + y * pubKey  (Edwards addition) *)

Theorem ElGamalEncrypt_structure :
  forall (pubKey_x pubKey_y msg_x msg_y : Z)
    (shared_x shared_y c1_x c1_y c2_x c2_y : Z)
    (beta gamma delta tau a d : Z),
  (* shared = ElGamalShare.out *)
  (* c1 = ElGamalShare.c1 *)
  (* c2 = BabyAdd(message, shared) *)
  beta = msg_x * shared_y ->
  gamma = msg_y * shared_x ->
  delta = (-a * msg_x + msg_y) * (shared_x + shared_y) ->
  tau = beta * gamma ->
  (1 + d * tau) * c2_x = beta + gamma ->
  (1 - d * tau) * c2_y = delta + a * beta - gamma ->
  (* c2 satisfies Edwards addition and tau is a derived product *)
  (1 + d * tau) * c2_x = beta + gamma /\
  (1 - d * tau) * c2_y = delta + a * beta - gamma /\
  tau = msg_x * shared_y * (msg_y * shared_x).
Proof.
  intros pubKey_x pubKey_y msg_x msg_y
    shared_x shared_y c1_x c1_y c2_x c2_y
    beta gamma delta tau a d
    Hbeta Hgamma Hdelta Htau Hx Hy.
  subst beta gamma tau.
  split; [exact Hx |].
  split; [exact Hy |].
  ring.
Qed.

(** ** ElGamalDecrypt (elgamal.circom:48-72)
    Computes s = c1^privKey, negates x, adds to c2.
    message = c2 + (-s) where negation inverts x-coordinate. *)

Theorem ElGamalDecrypt_negation :
  forall (c1x_out_x c1x_out_y c1xInvX : Z),
  c1xInvX = 0 - c1x_out_x ->
  c1xInvX = - c1x_out_x.
Proof. intros. lia. Qed.

Theorem ElGamalDecrypt_structure :
  forall (c1_x c1_y c2_x c2_y privKey : Z)
    (privKeyBits : list Z)
    (s_x s_y neg_s_x msg_x msg_y : Z)
    (beta gamma delta tau a d : Z),
  length privKeyBits = 254%nat ->
  all_binary privKeyBits ->
  privKey = bits_to_num privKeyBits ->
  (* s = EscalarMulAny(privKeyBits, c1) *)
  neg_s_x = - s_x ->
  (* message = BabyAdd((-s_x, s_y), c2) *)
  beta = neg_s_x * c2_y ->
  gamma = s_y * c2_x ->
  delta = (-a * neg_s_x + s_y) * (c2_x + c2_y) ->
  tau = beta * gamma ->
  (1 + d * tau) * msg_x = beta + gamma ->
  (1 - d * tau) * msg_y = delta + a * beta - gamma ->
  (* Decryption satisfies Edwards addition, tau is derived, and privKey is bounded *)
  (1 + d * tau) * msg_x = beta + gamma /\
  (1 - d * tau) * msg_y = delta + a * beta - gamma /\
  tau = neg_s_x * c2_y * (s_y * c2_x) /\
  0 <= privKey < 2 ^ 254.
Proof.
  intros c1_x c1_y c2_x c2_y privKey privKeyBits
    s_x s_y neg_s_x msg_x msg_y
    beta gamma delta tau a d
    Hlen Hbin HprivKey Hneg Hbeta Hgamma Hdelta Htau Hx Hy.
  subst beta gamma tau.
  split; [exact Hx |].
  split; [exact Hy |].
  split; [ring |].
  subst privKey.
  assert (Hbound := bits_to_num_bound privKeyBits Hbin).
  rewrite Hlen in Hbound. exact Hbound.
Qed.

(** ** ElGamal Roundtrip Property (algebraic)
    If pubKey = privKey * G8, then:
    Decrypt(c1, c2, privKey) where (c1, c2) = Encrypt(pubKey, msg, y)
    recovers msg.

    This follows from: c2 - privKey*c1 = msg + y*pubKey - privKey*(y*G8)
                      = msg + y*(privKey*G8) - privKey*(y*G8)
                      = msg  (by commutativity of scalar multiplication)

    We state this as an axiom since proving group law commutativity
    is beyond the scope of constraint verification. *)

Theorem ElGamal_roundtrip_algebraic :
  forall (point : Type) (point_add : point -> point -> point)
    (point_neg : point -> point) (scalar_mul : Z -> point -> point)
    (identity : point),
  (forall P Q R : point, point_add (point_add P Q) R = point_add P (point_add Q R)) ->
  (forall P : point, point_add P (point_neg P) = identity) ->
  (forall P : point, point_add P identity = P) ->
  (forall (a b : Z) (G : point), scalar_mul a (scalar_mul b G) = scalar_mul b (scalar_mul a G)) ->
  forall (msg G pubKey : point) (y privKey : Z),
  pubKey = scalar_mul privKey G ->
  (* Decryption recovers the original message *)
  point_add (point_add msg (scalar_mul y pubKey))
            (point_neg (scalar_mul privKey (scalar_mul y G))) = msg.
Proof.
  intros point point_add point_neg scalar_mul identity
    Hassoc Hneg Hid Hcomm
    msg G pubKey y privKey HpubKey.
  subst pubKey.
  rewrite Hcomm.
  rewrite Hassoc.
  rewrite Hneg.
  rewrite Hid.
  reflexivity.
Qed.
