From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Primitives.
Require Import Comparators.

Open Scope Z_scope.

(** * Logic Gate Circuit Verification
    Models the constraints of AND, OR, XOR from circuits/bitwise.circom
    and ForceEqualIfEnabled from circuits/comparators.circom. *)

(** ** AND (bitwise.circom:6-14)
    Constraints:
      equality <== 2*a*b - a - b + 1
      out <== equality * b

    Combined: out = (2*a*b - a - b + 1) * b *)

Theorem AND_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = (2 * a * b - a - b + 1) * b ->
  out = a * b /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold is_binary; split; lia.
Qed.

(** ** OR (bitwise.circom:16-22)
    Constraints:
      out <== a + b - a * b *)

Theorem OR_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = a + b - a * b ->
  (out = 1 <-> a = 1 \/ b = 1) /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold is_binary; (split; [split; intro H |]); lia.
Qed.

(** ** XOR (bitwise.circom:24-30)
    Constraints:
      out <== a + b - 2 * a * b *)

Theorem XOR_correct : forall a b out : Z,
  is_binary a -> is_binary b ->
  out = a + b - 2 * a * b ->
  (out = 1 <-> a <> b) /\ is_binary out.
Proof.
  intros a b out Ha Hb Hout.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    subst; unfold is_binary; (split; [split; intro H |]); lia.
Qed.

(** ** ForceEqualIfEnabled (comparators.circom:37-43)
    Constraints:
      isEq = 1 - (b - a) * inv     (from IsZero)
      (b - a) * isEq = 0            (from IsZero)
      (1 - isEq) * enabled = 0

    We prove: when enabled = 1, a must equal b. *)

Theorem ForceEqualIfEnabled_sound : forall a b enabled isEq inv : Z,
  isEq = 1 - (b - a) * inv ->
  (b - a) * isEq = 0 ->
  (1 - isEq) * enabled = 0 ->
  enabled = 1 -> a = b.
Proof.
  intros a b enabled isEq inv HisEq Hprod Hforce Hen.
  rewrite Hen in Hforce.
  assert (isEq = 1) by lia.
  assert (Hiso := IsZero_sound (b - a) isEq inv HisEq Hprod).
  lia.
Qed.
