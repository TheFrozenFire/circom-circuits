From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import WitnessLemmas.

Open Scope Z_scope.

(** * Fixed-Point Arithmetic Circuit Verification
    Models constraints from circuits/linalg/fixedpoint.circom. *)

(** ** InRange (fixedpoint.circom:8-12) *)

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

(** ** ApproxEqual (fixedpoint.circom:17-28) *)

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

(** ** FixedPointMul (fixedpoint.circom:34-53) *)

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

(** ** FixedPointMul Completeness
    Witness: q <-- (a*b) >> s; r <-- (a*b) % (1 << s).
    Constraints: a*b = q*S + r, 0 <= r < S. *)

Theorem FixedPointMul_complete :
  forall (scale_bits : nat) (a b : Z),
  let S := 2 ^ Z.of_nat scale_bits in
  0 <= a * b ->
  let q := (a * b) / S in
  let r := (a * b) mod S in
  a * b = q * S + r /\ 0 <= r < S.
Proof.
  intros scale_bits a b S Hprod q r. subst q r S.
  apply div_mod_constraint; [exact Hprod | apply Z.pow_pos_nonneg; lia].
Qed.

(** ** FixedPointDiv (fixedpoint.circom:108-134) *)

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

(** ** FixedPointDiv Completeness
    Witness: q <-- (a*(1<<s)) \ b; r <-- (a*(1<<s)) % b.
    Constraints: q*b + r = a*S, 0 <= r < b. *)

Theorem FixedPointDiv_complete :
  forall (scale_bits : nat) (a b : Z),
  let S := 2 ^ Z.of_nat scale_bits in
  0 <= a * S -> b > 0 ->
  let q := (a * S) / b in
  let r := (a * S) mod b in
  q * b + r = a * S /\ 0 <= r < b.
Proof.
  intros scale_bits a b S Hprod Hb q r. subst q r S.
  assert (Hdm := div_mod_constraint (a * 2 ^ Z.of_nat scale_bits) b Hprod ltac:(lia)).
  lia.
Qed.

(** ** FixedPointDotProduct (fixedpoint.circom:58-85) *)

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

(** ** FixedPointDotProduct Completeness
    Witness: q <-- rawDot >> s; r <-- rawDot % (1 << s).
    Same pattern as FixedPointMul. *)

Theorem FixedPointDotProduct_complete :
  forall (scale_bits : nat) (rawDot : Z),
  let S := 2 ^ Z.of_nat scale_bits in
  0 <= rawDot ->
  let q := rawDot / S in
  let r := rawDot mod S in
  rawDot = q * S + r /\ 0 <= r < S.
Proof.
  intros scale_bits rawDot S Hprod q r. subst q r S.
  apply div_mod_constraint; [exact Hprod | apply Z.pow_pos_nonneg; lia].
Qed.
