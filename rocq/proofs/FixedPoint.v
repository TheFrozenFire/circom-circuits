From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.

Open Scope Z_scope.

(** * Fixed-Point Arithmetic Circuit Verification
    Models constraints from circuits/linalg/fixedpoint.circom. *)

(** ** InRange (fixedpoint.circom:8-12)
    Wraps Num2Bits(bits). Constrains 0 <= in < 2^bits. *)

Theorem InRange_correct : forall (bits_list : list Z) (inp : Z),
  (forall i, (i < length bits_list)%nat ->
    nth i bits_list 0 * (nth i bits_list 0 - 1) = 0) ->
  inp = bits_to_num bits_list ->
  0 <= inp < 2 ^ Z.of_nat (length bits_list).
Proof.
  intros bits_list inp Hbin Hinp.
  assert (Hall := binary_constraints_imply_all_binary bits_list Hbin).
  subst inp. apply bits_to_num_bound. exact Hall.
Qed.

(** ** ApproxEqual (fixedpoint.circom:17-28)
    Constraints:
      diff = a - b + 2^t
      Num2Bits(t+1) applied to diff  (range check: 0 <= diff < 2^(t+1))

    This implies |a - b| < 2^t. *)

Theorem ApproxEqual_correct :
  forall (t : nat) (a b diff : Z) (bits : list Z),
  diff = a - b + 2 ^ Z.of_nat t ->
  length bits = S t ->
  (forall i, (i < length bits)%nat ->
    nth i bits 0 * (nth i bits 0 - 1) = 0) ->
  diff = bits_to_num bits ->
  - 2 ^ Z.of_nat t <= a - b < 2 ^ Z.of_nat t.
Proof.
  intros t a b diff bits Hdiff Hlen Hbin Hbtn.
  assert (Hall := binary_constraints_imply_all_binary bits Hbin).
  assert (Hbound := bits_to_num_bound bits Hall).
  rewrite Hlen in Hbound. rewrite Nat2Z.inj_succ in Hbound.
  rewrite Z.pow_succ_r in Hbound by lia.
  rewrite <- Hbtn in Hbound. rewrite Hdiff in Hbound. lia.
Qed.

(** ** FixedPointMul (fixedpoint.circom:34-53)
    Constraints:
      a * b = q * S + r    where S = 2^scale_bits
      0 <= r < S            (from Num2Bits on r)
      out = q

    We prove: q and r are the unique Euclidean quotient and remainder. *)

Theorem FixedPointMul_correct :
  forall (scale_bits : nat) (a b q r : Z),
  let S := 2 ^ Z.of_nat scale_bits in
  a * b = q * S + r ->
  0 <= r < S ->
  q = (a * b) / S /\ r = (a * b) mod S.
Proof.
  intros scale_bits a b q r S Hdiv Hrange.
  split.
  - apply Zdiv_unique with r; lia.
  - apply Zmod_unique with q; lia.
Qed.

(** ** FixedPointDiv (fixedpoint.circom:108-134)
    Constraints:
      qb = q * b
      qb + r = a * S        where S = 2^scale_bits
      0 <= q < 2^(max_bits + scale_bits)   (Num2Bits)
      0 <= r < 2^max_bits                   (Num2Bits)
      r < b                                 (LessThan)
      out = q

    We prove: q = floor(a * S / b) when b > 0. *)

Theorem FixedPointDiv_correct :
  forall (scale_bits : nat) (a b q r : Z),
  let S := 2 ^ Z.of_nat scale_bits in
  b > 0 ->
  q * b + r = a * S ->
  0 <= r < b ->
  q = (a * S) / b /\ r = (a * S) mod b.
Proof.
  intros scale_bits a b q r S Hb Hdiv Hrange.
  split.
  - apply Zdiv_unique with r; lia.
  - apply Zmod_unique with q; lia.
Qed.

(** ** FixedPointDotProduct (fixedpoint.circom:58-85)
    Composes DotProduct with a single FixedPointMul-style rescaling.

    Constraints:
      products[i] = a[i] * b[i]
      rawDot = Σ products[i]
      rawDot = q * S + r
      0 <= r < S
      out = q *)

Theorem FixedPointDotProduct_correct :
  forall (scale_bits : nat) (rawDot q r : Z),
  let S := 2 ^ Z.of_nat scale_bits in
  rawDot = q * S + r ->
  0 <= r < S ->
  q = rawDot / S /\ r = rawDot mod S.
Proof.
  intros scale_bits rawDot q r S Hdiv Hrange.
  split.
  - apply Zdiv_unique with r; lia.
  - apply Zmod_unique with q; lia.
Qed.
