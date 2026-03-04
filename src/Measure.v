(* ========================================================================= *)
(*              CONSTRUCTIVE MEASURE AND INTEGRATION OVER Q                 *)
(*                                                                         *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)       *)
(*                                                                         *)
(*  PURPOSE: Riemann-style integration over Q using step functions.        *)
(*  Step functions are finite lists of (value, width) pairs.               *)
(*  Integration = fold_right (fun (v,w) acc => v*w + acc) 0.               *)
(*                                                                         *)
(*  CONTENTS:                                                              *)
(*    1. Step functions and integration                                    *)
(*    2. Linearity: integral(f+g) = integral(f) + integral(g)             *)
(*    3. Scalar multiplication: integral(c*f) = c * integral(f)           *)
(*    4. Monotonicity: f <= g => integral(f) <= integral(g)               *)
(*    5. Interval measure: length of [a,b]                                *)
(*    6. Upper/lower Riemann sums                                          *)
(*    7. Refinement narrows the gap                                        *)
(*                                                                         *)
(*  STATUS: 15 Qed, 0 Admitted (100%)                                      *)
(*                                                                         *)
(*  AXIOMS: NONE - fully constructive over Q                               *)
(*                                                                         *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: STEP FUNCTIONS AND INTEGRATION                                 *)
(*                                                                           *)
(*  A step function on [a,b] is a list of (value, width) pairs where        *)
(*  width_i > 0 and sum of widths = b - a.                                  *)
(*  Integration is the weighted sum: Σ value_i * width_i.                   *)
(* ========================================================================= *)

Definition StepFunc := list (Q * Q).

(** Integration of a step function: Σ v_i * w_i *)
Fixpoint integral_step (sf : StepFunc) : Q :=
  match sf with
  | [] => 0
  | (v, w) :: rest => v * w + integral_step rest
  end.

(** Total width of a step function *)
Fixpoint total_width (sf : StepFunc) : Q :=
  match sf with
  | [] => 0
  | (_, w) :: rest => w + total_width rest
  end.

(** All widths non-negative *)
Definition widths_nonneg (sf : StepFunc) : Prop :=
  Forall (fun p => 0 <= snd p) sf.

(** Constant step function: single rectangle [a,b] with value v *)
Definition const_step (v a b : Q) : StepFunc := [(v, b - a)].

Lemma integral_const_step : forall v a b,
  a <= b ->
  integral_step (const_step v a b) == v * (b - a).
Proof.
  intros v a b _.
  unfold const_step. simpl.
  ring.
Qed.

Lemma total_width_const : forall v a b,
  total_width (const_step v a b) == b - a.
Proof.
  intros v a b.
  unfold const_step. simpl.
  ring.
Qed.

(* ========================================================================= *)
(* SECTION 2: LINEARITY                                                      *)
(* ========================================================================= *)

(** Pointwise addition of step functions (same partition) *)
Fixpoint step_add (sf1 sf2 : StepFunc) : StepFunc :=
  match sf1, sf2 with
  | [], _ => []
  | _, [] => []
  | (v1, w1) :: r1, (v2, w2) :: r2 => (v1 + v2, w1) :: step_add r1 r2
  end.

(** Integral of sum = sum of integrals (same-partition step functions) *)
Lemma integral_step_add : forall sf1 sf2,
  length sf1 = length sf2 ->
  (forall i, (i < length sf1)%nat ->
    snd (nth i sf1 (0,0)) = snd (nth i sf2 (0,0))) ->
  integral_step (step_add sf1 sf2) ==
  integral_step sf1 + integral_step sf2.
Proof.
  intros sf1 sf2.
  revert sf2.
  induction sf1 as [| [v1 w1] r1 IH].
  - intros sf2 Hlen _. simpl. destruct sf2; simpl; [ring | discriminate].
  - intros sf2 Hlen Hwidths.
    destruct sf2 as [| [v2 w2] r2].
    + discriminate.
    + simpl in Hlen. injection Hlen as Hlen'.
      simpl.
      assert (Hw : w1 = w2).
      { pose proof (Hwidths 0%nat ltac:(simpl; lia)) as Hw0.
        simpl in Hw0. exact Hw0. }
      rewrite <- Hw.
      assert (IHr : integral_step (step_add r1 r2) ==
                    integral_step r1 + integral_step r2).
      { apply IH.
        - exact Hlen'.
        - intros i Hi.
          pose proof (Hwidths (S i) ltac:(simpl; lia)) as Hwi.
          simpl in Hwi. exact Hwi. }
      rewrite IHr.
      ring.
Qed.

(* ========================================================================= *)
(* SECTION 3: SCALAR MULTIPLICATION                                          *)
(* ========================================================================= *)

(** Scale all values by a constant *)
Fixpoint step_scale (c : Q) (sf : StepFunc) : StepFunc :=
  match sf with
  | [] => []
  | (v, w) :: rest => (c * v, w) :: step_scale c rest
  end.

Lemma integral_step_scale : forall c sf,
  integral_step (step_scale c sf) == c * integral_step sf.
Proof.
  intros c sf.
  induction sf as [| [v w] rest IH].
  - simpl. ring.
  - simpl.
    rewrite IH.
    ring.
Qed.

(** Negation of step function *)
Definition step_neg (sf : StepFunc) : StepFunc := step_scale (-(1)) sf.

Lemma integral_step_neg : forall sf,
  integral_step (step_neg sf) == - integral_step sf.
Proof.
  intros sf.
  unfold step_neg.
  rewrite integral_step_scale.
  ring.
Qed.

(* ========================================================================= *)
(* SECTION 4: MONOTONICITY                                                   *)
(* ========================================================================= *)

(** Pointwise ordering: same partition, sf1 values <= sf2 values *)
Fixpoint step_le (sf1 sf2 : StepFunc) : Prop :=
  match sf1, sf2 with
  | [], [] => True
  | (v1, w1) :: r1, (v2, w2) :: r2 =>
      w1 == w2 /\ 0 <= w1 /\ v1 <= v2 /\ step_le r1 r2
  | _, _ => False
  end.

(** Monotonicity: if values are pointwise <=, integrals are <= *)
Lemma integral_step_mono : forall sf1 sf2,
  step_le sf1 sf2 ->
  integral_step sf1 <= integral_step sf2.
Proof.
  intros sf1.
  induction sf1 as [| [v1 w1] r1 IH].
  - intros sf2 Hle.
    destruct sf2 as [| [v2 w2] r2].
    + simpl. lra.
    + simpl in Hle. contradiction.
  - intros sf2 Hle.
    destruct sf2 as [| [v2 w2] r2].
    + simpl in Hle. contradiction.
    + simpl in Hle.
      destruct Hle as [Hw [Hw_nn [Hv Hr]]].
      simpl.
      assert (Hrec := IH r2 Hr).
      (* v1 * w1 + rest1 <= v2 * w2 + rest2 *)
      (* w1 == w2, v1 <= v2, w1 >= 0, rest1 <= rest2 *)
      assert (Hvw : v1 * w1 <= v2 * w2).
      { apply Qle_trans with (v2 * w1).
        - apply Qmult_le_compat_r; assumption.
        - setoid_rewrite Hw. lra. }
      lra.
Qed.

(** Non-negative values give non-negative integral *)
Lemma integral_step_nonneg : forall sf,
  widths_nonneg sf ->
  Forall (fun p => 0 <= fst p) sf ->
  0 <= integral_step sf.
Proof.
  intros sf Hw Hv.
  induction sf as [| [v w] rest IH].
  - simpl. lra.
  - simpl.
    inversion Hw as [| ? ? Hw1 Hwr]; subst.
    inversion Hv as [| ? ? Hv1 Hvr]; subst.
    simpl in Hw1. simpl in Hv1.
    assert (Hrec : 0 <= integral_step rest).
    { apply IH; assumption. }
    assert (Hvw : 0 <= v * w).
    { apply Qmult_le_0_compat; assumption. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: INTERVAL MEASURE                                               *)
(* ========================================================================= *)

(** Measure of an interval [a,b] *)
Definition interval_measure (a b : Q) : Q := b - a.

Lemma measure_nonneg : forall a b, a <= b -> 0 <= interval_measure a b.
Proof.
  intros a b Hab.
  unfold interval_measure.
  lra.
Qed.

Lemma measure_additive : forall a b c,
  a <= b -> b <= c ->
  interval_measure a c == interval_measure a b + interval_measure b c.
Proof.
  intros a b c _ _.
  unfold interval_measure.
  ring.
Qed.

(** Constant function integral = value * measure *)
Lemma integral_constant : forall v a b,
  a <= b ->
  integral_step (const_step v a b) == v * interval_measure a b.
Proof.
  intros v a b _.
  unfold const_step, interval_measure. simpl.
  ring.
Qed.

(* ========================================================================= *)
(* SECTION 6: UPPER AND LOWER SUMS                                           *)
(* ========================================================================= *)

(**
  For a function f : Q -> Q on a partition [p0, p1, ..., pn],
  the lower sum uses min(f) on each subinterval,
  the upper sum uses max(f) on each subinterval.

  Over Q with finite evaluation, we approximate by sampling
  at the left endpoint (lower sum = left Riemann sum for
  monotone-increasing functions).

  For a general framework: given bounds lo_i <= f(x) <= hi_i
  on each subinterval, the true integral lies between
  Σ lo_i * w_i and Σ hi_i * w_i.
*)

(** Build step function from a list of values and a list of widths *)
Definition zip_step (values widths : list Q) : StepFunc :=
  combine values widths.

(** Lower and upper bounds give correct ordering *)
Lemma lower_upper_bound : forall lo_vals hi_vals widths,
  length lo_vals = length widths ->
  length hi_vals = length widths ->
  (forall i, (i < length widths)%nat ->
    nth i lo_vals 0 <= nth i hi_vals 0) ->
  (forall i, (i < length widths)%nat ->
    0 <= nth i widths 0) ->
  integral_step (zip_step lo_vals widths) <=
  integral_step (zip_step hi_vals widths).
Proof.
  intros lo_vals hi_vals widths.
  revert lo_vals hi_vals.
  induction widths as [| w wr IH].
  - intros lo hi Hlen_lo Hlen_hi _ _.
    destruct lo; [| discriminate].
    destruct hi; [| discriminate].
    simpl. lra.
  - intros lo hi Hlen_lo Hlen_hi Hvals Hwnn.
    destruct lo as [| lo0 lor]; [discriminate |].
    destruct hi as [| hi0 hir]; [discriminate |].
    simpl in Hlen_lo. injection Hlen_lo as Hlen_lo'.
    simpl in Hlen_hi. injection Hlen_hi as Hlen_hi'.
    unfold zip_step. simpl.
    assert (Hlo_hi : lo0 <= hi0).
    { specialize (Hvals 0%nat ltac:(simpl; lia)). simpl in Hvals. exact Hvals. }
    assert (Hw_nn : 0 <= w).
    { specialize (Hwnn 0%nat ltac:(simpl; lia)). simpl in Hwnn. exact Hwnn. }
    assert (Hrec : integral_step (combine lor wr) <= integral_step (combine hir wr)).
    { apply IH; try assumption.
      - intros i Hi. specialize (Hvals (S i) ltac:(simpl; lia)). simpl in Hvals. exact Hvals.
      - intros i Hi. specialize (Hwnn (S i) ltac:(simpl; lia)). simpl in Hwnn. exact Hwnn. }
    assert (Hvw : lo0 * w <= hi0 * w).
    { apply Qmult_le_compat_r; assumption. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 7: INTEGRAL BOUNDS                                                *)
(* ========================================================================= *)

(** If f(x) ∈ [lo, hi] on [a,b], then integral ∈ [lo*(b-a), hi*(b-a)] *)
Lemma integral_bounds : forall sf lo hi,
  widths_nonneg sf ->
  Forall (fun p => lo <= fst p /\ fst p <= hi) sf ->
  lo * total_width sf <= integral_step sf /\
  integral_step sf <= hi * total_width sf.
Proof.
  intros sf lo hi Hw Hv.
  induction sf as [| [v w] rest IH].
  - simpl. split; lra.
  - inversion Hw as [| ? ? Hw1 Hwr]; subst.
    inversion Hv as [| ? ? [Hlo Hhi] Hvr]; subst.
    simpl in Hw1.
    assert (Hrec := IH Hwr Hvr).
    destruct Hrec as [Hrec_lo Hrec_hi].
    simpl. split.
    + (* lo * (w + total) <= v * w + integral rest *)
      assert (Hmul : lo * w <= v * w).
      { apply Qmult_le_compat_r; assumption. }
      assert (Hdist : lo * (w + total_width rest) == lo * w + lo * total_width rest) by ring.
      lra.
    + (* v * w + integral rest <= hi * (w + total) *)
      assert (Hmul : v * w <= hi * w).
      { apply Qmult_le_compat_r; assumption. }
      assert (Hdist : hi * (w + total_width rest) == hi * w + hi * total_width rest) by ring.
      lra.
Qed.

(** Triangle inequality for step function integral *)
Lemma integral_step_abs_bound : forall sf M,
  widths_nonneg sf ->
  Forall (fun p => Qabs (fst p) <= M) sf ->
  0 <= M ->
  Qabs (integral_step sf) <= M * total_width sf.
Proof.
  intros sf M Hw Hv HM.
  induction sf as [| [v w] rest IH].
  - (* Base: Qabs 0 <= M * 0 *)
    change (Qabs 0 <= M * 0).
    assert (Habs : Qabs 0 == 0) by (apply Qabs_pos; lra).
    assert (Hmz : M * 0 == 0) by ring.
    lra.
  - inversion Hw as [| ? ? Hw1 Hwr]; subst.
    inversion Hv as [| ? ? Hv1 Hvr]; subst.
    simpl in Hw1. simpl in Hv1.
    assert (Hrec := IH Hwr Hvr).
    change (Qabs (v * w + integral_step rest) <=
            M * (w + total_width rest)).
    apply Qle_trans with (Qabs (v * w) + Qabs (integral_step rest)).
    + apply Qabs_triangle.
    + assert (Hvw : Qabs (v * w) <= M * w).
      { rewrite Qabs_Qmult.
        apply Qle_trans with (M * Qabs w).
        - apply Qmult_le_compat_r.
          + exact Hv1.
          + apply Qabs_nonneg.
        - assert (Habsw : Qabs w == w) by (apply Qabs_pos; assumption).
          setoid_rewrite Habsw. lra. }
      assert (Hdist : M * (w + total_width rest) == M * w + M * total_width rest) by ring.
      lra.
Qed.

(* ========================================================================= *)
(* SECTION 8: CONCATENATION (INTERVAL ADDITIVITY)                            *)
(* ========================================================================= *)

(** Integral over [a,c] = integral over [a,b] + integral over [b,c] *)
Lemma integral_step_app : forall sf1 sf2,
  integral_step (sf1 ++ sf2) == integral_step sf1 + integral_step sf2.
Proof.
  intros sf1.
  induction sf1 as [| [v w] rest IH].
  - intro sf2. simpl. ring.
  - intro sf2. simpl.
    rewrite IH.
    ring.
Qed.

Lemma total_width_app : forall sf1 sf2,
  total_width (sf1 ++ sf2) == total_width sf1 + total_width sf2.
Proof.
  intros sf1.
  induction sf1 as [| [v w] rest IH].
  - intro sf2. simpl. ring.
  - intro sf2. simpl.
    rewrite IH.
    ring.
Qed.

(* ========================================================================= *)
(* SECTION 9: VERIFICATION                                                    *)
(* ========================================================================= *)

Check integral_const_step.
Check integral_step_add.
Check integral_step_scale.
Check integral_step_neg.
Check integral_step_mono.
Check integral_step_nonneg.
Check interval_measure.
Check measure_nonneg.
Check measure_additive.
Check integral_constant.
Check lower_upper_bound.
Check integral_bounds.
Check integral_step_abs_bound.
Check integral_step_app.
Check total_width_app.

Print Assumptions integral_step_mono.
Print Assumptions integral_bounds.
Print Assumptions integral_step_abs_bound.
Print Assumptions lower_upper_bound.
