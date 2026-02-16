From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Primitives.
Require Import core.Comparators.
Require Import packing.Bitify.
Require Import collections.Selector.

Open Scope Z_scope.

Set Default Proof Using "Type".

(** * Similarity Circuit Verification
    Models constraints from circuits/linalg/similarity.circom. *)

(** ** CosineSimilarityCheck (similarity.circom:10-64)
    Constraints:
      dotAB = a . b
      normSqA = ||a||^2, normSqB = ||b||^2
      lhs = dotAB^2
      rhs = threshold_sq * normSqA * normSqB
      NOT (lhs < rhs) — i.e., lhs >= rhs
      dotAB is non-negative (range-checked via Num2Bits) *)

Theorem CosineSimilarityCheck_sound :
  forall (bits : nat) (dotAB normSqA normSqB threshold_sq lhs rhs normProd : Z),
  (0 < bits)%nat ->
  0 <= dotAB < 2 ^ Z.of_nat bits ->
  0 <= lhs < 2 ^ Z.of_nat bits -> 0 <= rhs < 2 ^ Z.of_nat bits ->
  lhs = dotAB * dotAB ->
  normProd = normSqA * normSqB ->
  rhs = threshold_sq * normProd ->
  (* LessThan(bits) says NOT (lhs < rhs) *)
  (lhs < rhs -> False) ->
  dotAB * dotAB >= threshold_sq * normSqA * normSqB /\ dotAB >= 0.
Proof.
  intros bits dotAB normSqA normSqB threshold_sq lhs rhs normProd
    Hbits HdotR HlhsR HrhsR Hlhs Hnp Hrhs Hnlt.
  split.
  - subst lhs rhs normProd. lia.
  - lia.
Qed.

(** ** NearestNeighborCheck (similarity.circom:68-110)
    The circuit computes squared distances for all candidates, extracts
    the claimed distance via indicator mux, then verifies it's minimal. *)

Theorem NearestNeighborCheck_sound :
  forall (k : nat) (dist : list Z) (claimedDist : Z),
  length dist = k ->
  (* LessThan says: for all c, NOT (dist[c] < claimedDist) *)
  (forall c, (c < k)%nat -> ~ (nth c dist 0 < claimedDist)) ->
  forall c, (c < k)%nat -> claimedDist <= nth c dist 0.
Proof.
  intros k dist claimedDist Hlen Hnlt c Hc.
  specialize (Hnlt c Hc). lia.
Qed.

(** Indicator mux extracts the correct distance. *)
Theorem indicator_mux_extracts_distance :
  forall (k : nat) (dist indicators : list Z) (claimedDist : Z),
  length dist = k ->
  length indicators = k ->
  Forall is_binary indicators ->
  list_sum indicators = 1 ->
  claimedDist = list_sum (map (fun p => fst p * snd p) (combine indicators dist)) ->
  exists idx, (idx < k)%nat /\ nth idx indicators 0 = 1 /\ claimedDist = nth idx dist 0.
Proof.
  intros k dist indicators claimedDist Hdlen Hilen Hbin Hone HclDist.
  assert (Hmux := indicator_mux_correct dist indicators claimedDist
    ltac:(lia) Hbin Hone HclDist).
  destruct Hmux as [j [Hj [Hjind Hjval]]].
  exists j. rewrite Hdlen in Hj. split; [lia |]. split; assumption.
Qed.
