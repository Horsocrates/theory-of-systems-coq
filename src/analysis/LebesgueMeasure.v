(** * LebesgueMeasure.v — Measure derived from integral (Bishop-Cheng)
    Elements: Characteristic step functions, measure as integral
    Roles:    Measure of intervals, additivity, monotonicity
    Rules:    mu(A) = I(chi_A), measure from integration not sigma-algebras
    STATUS:   20 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    In the Bishop-Cheng approach, MEASURE IS DERIVED FROM INTEGRAL.
    The Lebesgue measure of a set A is defined as mu(A) = I(chi_A),
    where chi_A is the characteristic function of A.

    For intervals [c,d], chi_[c,d] is itself a step function with value 1.
    So mu([c,d]) = I(chi_[c,d]) = 1 * (d - c) = d - c.

    This reverses the standard textbook order (measure -> integral)
    and aligns with P4: we COMPUTE integrals, then DEFINE measure.

    Measurability = distinguishability: a set is measurable when
    its characteristic function is approximable by step functions.
    No sigma-algebras, no AC, no completed infinities.
*)

From Stdlib Require Import QArith Qabs List Lqa Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  REPLICATED DEFINITIONS (from StepIntegral.v / L1Space.v)          *)
(* ================================================================== *)

(* Replicated from StepIntegral.v to keep file standalone *)
Record Step := mkStep {
  step_val : Q;
  step_left : Q;
  step_right : Q;
  step_valid : step_left <= step_right
}.

Definition StepFun := list Step.

Definition step_integral (s : Step) : Q :=
  step_val s * (step_right s - step_left s).

Fixpoint step_fun_integral (f : StepFun) : Q :=
  match f with
  | [] => 0
  | s :: rest => step_integral s + step_fun_integral rest
  end.

(* ================================================================== *)
(*  CHARACTERISTIC STEP FUNCTIONS                                      *)
(* ================================================================== *)

(** Characteristic step function for interval [c,d]:
    chi_[c,d] = step function with value 1 on [c,d] *)
Definition characteristic_step (c d : Q) (H : c <= d) : StepFun :=
  [mkStep 1 c d H].

(** ★ Integral of characteristic = length of interval *)
Lemma characteristic_integral : forall c d (H : c <= d),
  step_fun_integral (characteristic_step c d H) == d - c.
Proof.
  intros c d H. unfold characteristic_step. simpl.
  unfold step_integral. simpl. ring.
Qed.

(* ================================================================== *)
(*  MEASURE = INTEGRAL OF CHARACTERISTIC                               *)
(* ================================================================== *)

(** Measure of interval [c,d] defined as integral of chi_[c,d] *)
Definition measure_interval (c d : Q) (H : c <= d) : Q :=
  step_fun_integral (characteristic_step c d H).

(** ★ measure_interval computes to d - c *)
Lemma measure_interval_eq : forall c d (H : c <= d),
  measure_interval c d H == d - c.
Proof.
  intros c d H. unfold measure_interval.
  apply characteristic_integral.
Qed.

(* ================================================================== *)
(*  CONCRETE CALCULATIONS                                              *)
(* ================================================================== *)

Lemma le_0_1 : 0 <= 1. Proof. lra. Qed.
Lemma le_0_half : 0 <= 1#2. Proof. lra. Qed.
Lemma le_half_1 : 1#2 <= 1. Proof. lra. Qed.
Lemma le_0_2 : 0 <= 2. Proof. lra. Qed.
Lemma le_1_3 : 1 <= 3. Proof. lra. Qed.
Lemma le_0_0 : (0:Q) <= 0. Proof. apply Qle_refl. Qed.

(** ★ mu([0,1]) = 1 *)
Lemma measure_unit : measure_interval 0 1 le_0_1 == 1.
Proof.
  rewrite measure_interval_eq. ring.
Qed.

(** ★ mu([0, 1/2]) = 1/2 *)
Lemma measure_half : measure_interval 0 (1#2) le_0_half == 1#2.
Proof.
  rewrite measure_interval_eq. ring.
Qed.

(** ★ mu([0, 2]) = 2 *)
Lemma measure_double : measure_interval 0 2 le_0_2 == 2.
Proof.
  rewrite measure_interval_eq. ring.
Qed.

(** ★ mu([1, 3]) = 2 *)
Lemma measure_shift : measure_interval 1 3 le_1_3 == 2.
Proof.
  rewrite measure_interval_eq. ring.
Qed.

(* ================================================================== *)
(*  MEASURE PROPERTIES                                                 *)
(* ================================================================== *)

(** ★ Measure is non-negative *)
Lemma measure_nonneg : forall c d (H : c <= d),
  0 <= measure_interval c d H.
Proof.
  intros c d H. rewrite measure_interval_eq. lra.
Qed.

(** ★ Measure is monotone: [c,d] subset [a,b] implies mu([c,d]) <= mu([a,b]) *)
Lemma measure_monotone : forall a b c d
  (Hab : a <= b) (Hcd : c <= d),
  a <= c -> d <= b ->
  measure_interval c d Hcd <= measure_interval a b Hab.
Proof.
  intros a b c d Hab Hcd Hac Hdb.
  rewrite !measure_interval_eq. lra.
Qed.

(** ★ Measure additive for adjacent intervals: mu([a,b]) + mu([b,c]) = mu([a,c]) *)
Lemma measure_additive : forall a b c
  (Hab : a <= b) (Hbc : b <= c) (Hac : a <= c),
  measure_interval a b Hab + measure_interval b c Hbc ==
  measure_interval a c Hac.
Proof.
  intros a b c Hab Hbc Hac.
  rewrite !measure_interval_eq. ring.
Qed.

(* ================================================================== *)
(*  DEGENERATE CASES                                                   *)
(* ================================================================== *)

(** ★ Point has measure zero: mu([a,a]) = 0 *)
Lemma measure_point_zero : forall a (H : a <= a),
  measure_interval a a H == 0.
Proof.
  intros a H. rewrite measure_interval_eq. ring.
Qed.

(** ★ Measure zero implies degenerate interval *)
Lemma measure_zero_point : forall c d (H : c <= d),
  measure_interval c d H == 0 -> c == d.
Proof.
  intros c d H Hm. rewrite measure_interval_eq in Hm. lra.
Qed.

(* ================================================================== *)
(*  SCALING AND TRANSLATION                                            *)
(* ================================================================== *)

(** ★ Scaling: mu([0, k]) = k for 0 <= k *)
Lemma measure_scale : forall k (H : 0 <= k),
  measure_interval 0 k H == k.
Proof.
  intros k H. rewrite measure_interval_eq. ring.
Qed.

(** ★ Translation invariance: mu([a, a+w]) = mu([b, b+w]) = w *)
Lemma measure_translation : forall a b w
  (Ha : a <= a + w) (Hb : b <= b + w),
  measure_interval a (a + w) Ha == measure_interval b (b + w) Hb.
Proof.
  intros a b w Ha Hb. rewrite !measure_interval_eq. ring.
Qed.

(* ================================================================== *)
(*  CHARACTERISTIC FUNCTION PROPERTIES                                 *)
(* ================================================================== *)

(** ★ Characteristic of [0,1] has integral 1 *)
Lemma char_unit_integral :
  step_fun_integral (characteristic_step 0 1 le_0_1) == 1.
Proof.
  apply characteristic_integral.
Qed.

(** ★ Two adjacent characteristics = characteristic of union *)
Lemma char_adjacent_sum : forall a b c
  (Hab : a <= b) (Hbc : b <= c) (Hac : a <= c),
  step_fun_integral (characteristic_step a b Hab ++ characteristic_step b c Hbc) ==
  step_fun_integral (characteristic_step a c Hac).
Proof.
  intros a b c Hab Hbc Hac.
  unfold characteristic_step. simpl.
  unfold step_integral. simpl. ring.
Qed.

(* ================================================================== *)
(*  PHILOSOPHICAL COMMENTARY                                           *)
(* ================================================================== *)

(** ★ Grand summary: measure theory without sigma-algebras *)
Theorem measure_from_integral_works :
  (* Unit interval has measure 1 *)
  measure_interval 0 1 le_0_1 == 1 /\
  (* Half interval has measure 1/2 *)
  measure_interval 0 (1#2) le_0_half == 1#2 /\
  (* Additivity holds *)
  measure_interval 0 (1#2) le_0_half + measure_interval (1#2) 1 le_half_1 ==
  measure_interval 0 1 le_0_1 /\
  (* Points have measure zero *)
  measure_interval 0 0 le_0_0 == 0.
Proof.
  split. { apply measure_unit. }
  split. { apply measure_half. }
  split. { apply measure_additive. }
  apply measure_point_zero.
Qed.

(** * PHILOSOPHICAL NOTE: Measurability = Distinguishability
    In ToS, a set is "measurable" when its boundary can be
    distinguished to arbitrary precision by step functions.
    This is EXACTLY the Bishop-Cheng criterion.

    The classical approach (sigma-algebras, Caratheodory extension)
    is ontologically problematic:
    - It assumes completed infinity (countable unions)
    - It invokes AC for non-measurable sets (Vitali)
    - It separates "measure" from "computation"

    Our approach: measure IS computation.
    mu(A) = lim I(chi_A_n) where chi_A_n are step approximations.
    No sigma-algebras needed. No AC invoked. Everything computable.
*)
