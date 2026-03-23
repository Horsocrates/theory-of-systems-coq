(** * PhaseDetector.v — Trending vs mean-reverting via variance scaling
    Elements: variance ratios, market phases;
    Roles:    detect_phase classifies regime, variance_ratio computes scaling;
    Rules:    ratio > 1.1 = trending, ratio < 0.9 = reverting, else random.
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.trading.CorrMatrix.
Open Scope Q_scope.

(* ================================================================ *)
(* Market phase classification                                       *)
(* ================================================================ *)

Inductive MarketPhase :=
  | TrendingPhase | RandomPhase | MeanRevertingPhase.

Definition detect_phase (ratio : Q) : MarketPhase :=
  if Qlt_le_dec (11#10) ratio then TrendingPhase
  else if Qlt_le_dec ratio (9#10) then MeanRevertingPhase
  else RandomPhase.

(* Variance ratio: long-window variance / short-window variance *)
Definition variance_ratio (short_returns long_returns : list Q) : Q :=
  let vs := variance short_returns in
  let vl := variance long_returns in
  if Qlt_le_dec vs 0 then 0
  else if Qlt_le_dec 0 vs then vl / vs
  else 0.

(* ================================================================ *)
(* Phase detection lemmas                                            *)
(* ================================================================ *)

Lemma detect_trending : detect_phase (3#2) = TrendingPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) (3#2)).
  - reflexivity.
  - exfalso. lra.
Qed.

Lemma detect_random : detect_phase 1 = RandomPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) 1).
  - exfalso. lra.
  - destruct (Qlt_le_dec 1 (9#10)).
    + exfalso. lra.
    + reflexivity.
Qed.

Lemma detect_reverting : detect_phase (1#2) = MeanRevertingPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) (1#2)).
  - exfalso. lra.
  - destruct (Qlt_le_dec (1#2) (9#10)).
    + reflexivity.
    + exfalso. lra.
Qed.

Lemma detect_boundary_high : detect_phase (11#10) = RandomPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) (11#10)).
  - exfalso. lra.
  - destruct (Qlt_le_dec (11#10) (9#10)).
    + exfalso. lra.
    + reflexivity.
Qed.

Lemma detect_boundary_low : detect_phase (9#10) = RandomPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) (9#10)).
  - exfalso. lra.
  - destruct (Qlt_le_dec (9#10) (9#10)).
    + exfalso. lra.
    + reflexivity.
Qed.

Lemma detect_strong_trend : detect_phase 2 = TrendingPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) 2).
  - reflexivity.
  - exfalso. lra.
Qed.

Lemma detect_deep_reversion : detect_phase (1#10) = MeanRevertingPhase.
Proof.
  unfold detect_phase. destruct (Qlt_le_dec (11#10) (1#10)).
  - exfalso. lra.
  - destruct (Qlt_le_dec (1#10) (9#10)).
    + reflexivity.
    + exfalso. lra.
Qed.

(* ================================================================ *)
(* Phase decidability                                                *)
(* ================================================================ *)

Lemma phase_decidable : forall ratio,
  detect_phase ratio = TrendingPhase \/
  detect_phase ratio = RandomPhase \/
  detect_phase ratio = MeanRevertingPhase.
Proof.
  intros. unfold detect_phase.
  destruct (Qlt_le_dec (11#10) ratio).
  - left. reflexivity.
  - destruct (Qlt_le_dec ratio (9#10)).
    + right. right. reflexivity.
    + right. left. reflexivity.
Qed.

(* ================================================================ *)
(* Concrete variance ratio using CorrMatrix                         *)
(* ================================================================ *)

Definition short_ret : list Q := [1; -(1); 1; -(1)].
Definition long_ret  : list Q := [2; -(2); 2; -(2)].

Lemma var_short : variance short_ret == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma var_long : variance long_ret == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_example : variance_ratio short_ret long_ret == 4.
Proof.
  unfold variance_ratio.
  destruct (Qlt_le_dec (variance short_ret) 0).
  - exfalso. assert (variance short_ret == 1) by (exact var_short). lra.
  - destruct (Qlt_le_dec 0 (variance short_ret)).
    + assert (Hvs : variance short_ret == 1) by exact var_short.
      assert (Hvl : variance long_ret == 4) by exact var_long.
      rewrite Hvl, Hvs. field.
    + exfalso. assert (variance short_ret == 1) by (exact var_short). lra.
Qed.

Lemma ratio_trending :
  detect_phase 4 = TrendingPhase.
Proof. exact detect_strong_trend. Qed.

(* ================================================================ *)
(* Phase equality decidable                                          *)
(* ================================================================ *)

Definition phase_eqb (p1 p2 : MarketPhase) : bool :=
  match p1, p2 with
  | TrendingPhase, TrendingPhase => true
  | RandomPhase, RandomPhase => true
  | MeanRevertingPhase, MeanRevertingPhase => true
  | _, _ => false
  end.

Lemma phase_eqb_refl : forall p, phase_eqb p p = true.
Proof. destruct p; reflexivity. Qed.

Lemma phase_eqb_eq : forall p1 p2,
  phase_eqb p1 p2 = true -> p1 = p2.
Proof. destruct p1, p2; simpl; intros; try reflexivity; discriminate. Qed.

(* ================================================================ *)
(* Synthesis: phase detection captures market regimes               *)
(* ================================================================ *)

Theorem phase_detector_synthesis :
  (* Three regimes are detectable *)
  detect_phase (3#2) = TrendingPhase /\
  detect_phase 1 = RandomPhase /\
  detect_phase (1#2) = MeanRevertingPhase /\
  (* Boundaries are random (conservative) *)
  detect_phase (11#10) = RandomPhase /\
  detect_phase (9#10) = RandomPhase.
Proof.
  split. { exact detect_trending. }
  split. { exact detect_random. }
  split. { exact detect_reverting. }
  split. { exact detect_boundary_high. }
  exact detect_boundary_low.
Qed.
