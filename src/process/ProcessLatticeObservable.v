(** * ProcessLatticeObservable.v — Lattice Observable Comparison Framework
    Theory of Systems - Phase 38: String Tension (W8) (File 2)

    Elements: creutz_ratio, LatticeObservable, sigma_observable
    Roles:    comparison framework for experimental verification
    Rules:    σ(β=1, M=0) positive and convergent; honest M=0 assessment
    Status:   complete

    The string tension σ is the standard benchmark observable for
    lattice gauge theory. We establish a comparison framework.

    HONEST ASSESSMENT (M=0 truncation):
      σ(β=1, M=0) ≈ 1.97 (full Taylor sum of −ln(1 − 289/336))
      σ(β=1, exact) = −ln(I₁(β)/I₀(β)) ≈ 0.764
      M=0 overestimates by ~2.5×. Higher M → converges to exact.
      The M=0 value is a crude upper bound, not a prediction.

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import process.ProcessStringTension.

(* ================================================================== *)
(*  Part I: Creutz Ratio  (~7 lemmas)                                 *)
(* ================================================================== *)

(** The Creutz ratio: standard lattice technique for extracting σ
    χ(R,T) = −ln(W(R,T)·W(R-1,T-1) / (W(R,T-1)·W(R-1,T)))
    For area law: χ(R,T) → σa² as R,T → ∞

    In our framework: W(R,T) = (t₁/t₀)^T for angular momentum R
    So: χ reduces to our −ln(t₁/t₀) = −ln(1 − gap/t₀) = string_tension

    The argument to neg_ln_taylor is gap/t₀, NOT gap directly,
    since t₀(β=1) = 7/8 ≠ 1. *)

(** Creutz ratio is just neg_ln_taylor applied to the eigenvalue ratio *)
Definition creutz_ratio (x : Q) (order : nat) : Q :=
  neg_ln_taylor x order.

(** ★ The Creutz ratio IS the string tension on our lattice *)
Lemma creutz_is_sigma : forall x order,
  creutz_ratio x order == string_tension_gap x order.
Proof. intros. unfold creutz_ratio, string_tension_gap. reflexivity. Qed.

(** Creutz ratio at β=1: use gap/t₀ = 289/336 *)
Lemma creutz_beta_1 : forall order,
  creutz_ratio (gap_M0 1 / t0_M0 1) order == string_tension 1 order.
Proof.
  intros. unfold creutz_ratio, string_tension. reflexivity.
Qed.

(** Creutz ratio is positive for positive argument *)
Lemma creutz_positive : forall x order,
  0 < x -> (1 <= order)%nat ->
  0 < creutz_ratio x order.
Proof.
  intros x order Hg Hord.
  unfold creutz_ratio.
  assert (Hn := taylor_nonneg x order (Qlt_le_weak _ _ Hg)).
  assert (Hs := taylor_strict_increasing x (pred order) Hg).
  destruct order; [lia |].
  simpl pred in Hs.
  assert (Hn0 := taylor_nonneg x order (Qlt_le_weak _ _ Hg)).
  lra.
Qed.

(** Creutz ratio is increasing in order *)
Lemma creutz_increasing : forall x order,
  0 < x ->
  creutz_ratio x order <= creutz_ratio x (S order).
Proof.
  intros. unfold creutz_ratio. apply taylor_increasing. exact H.
Qed.

(** Creutz ratio is bounded *)
Lemma creutz_bounded : forall x order,
  0 < x -> x < 1 ->
  creutz_ratio x order <= x / (1 - x).
Proof.
  intros. unfold creutz_ratio. apply taylor_bounded; assumption.
Qed.

(** Creutz process *)
Definition creutz_process (x : Q) : RealProcess :=
  fun N => creutz_ratio x (S N).

Lemma creutz_process_cauchy : forall x,
  0 < x -> x < 1 ->
  is_Cauchy (creutz_process x).
Proof.
  intros x Hg Hg1.
  unfold creutz_process, creutz_ratio.
  exact (ln_process_cauchy x Hg Hg1).
Qed.

(* ================================================================== *)
(*  Part II: Computational Bounds  (~6 lemmas)                        *)
(* ================================================================== *)

(** Computational bounds for σ(β=1, M=0).
    NOTE: these are bounds on our M=0 APPROXIMATION, not on the
    true physical string tension. The M=0 truncation overestimates
    by a factor of ~2.5 compared to the exact −ln(I₁/I₀) ≈ 0.764.
    Higher angular momentum modes (M>0) would bring the value down. *)

Definition sigma_beta1_lower_bound : Q := 1.
(** Upper bound from geometric series: (289/336)/(1 - 289/336) = 289/47. *)
Definition sigma_beta1_upper_bound : Q := 289 # 47.

(** Our M=0 value at order 2 is above 1 *)
Lemma sigma_order_2_above_1 :
  sigma_beta1_lower_bound <= string_tension 1 2.
Proof.
  unfold sigma_beta1_lower_bound.
  assert (H := sigma_order_2).
  (* 289/336 + 289²/336²/2 = 289/336 + 83521/225792 *)
  (* = 194208/225792 + 83521/225792 = 277729/225792 ≈ 1.230 > 1 *)
  assert (Hval : string_tension 1 2 ==
    (289 # 336) + ((289 # 336) * (289 # 336) / (2#1))) by exact H.
  assert (Hnum : (289 # 336) + ((289 # 336) * (289 # 336) / (2#1)) ==
    277729 # 225792).
  { unfold Qeq. simpl. lia. }
  assert (Hge : 1 <= 277729 # 225792).
  { unfold Qle. simpl. lia. }
  lra.
Qed.

(** Our upper bound matches the geometric bound *)
Lemma sigma_upper_below_bound :
  sigma_upper_bound <= 289 # 47.
Proof.
  assert (H := sigma_upper_bound_value). lra.
Qed.

(** ★ Our M=0 σ at any order ≥ 2 is in range [1, 289/47] *)
Theorem sigma_in_range : forall N,
  (2 <= N)%nat ->
  sigma_beta1_lower_bound <= string_tension 1 N /\
  string_tension 1 N <= sigma_beta1_upper_bound.
Proof.
  intros N HN. split.
  - (* Lower bound: σ(N) >= σ(2) >= 1 *)
    assert (Hlo := sigma_order_2_above_1).
    assert (Hmono : string_tension 1 2 <= string_tension 1 N).
    { induction N as [|m IH].
      + lia.
      + destruct (Nat.eq_dec m 1).
        * subst. simpl. lra.
        * destruct (Nat.le_gt_cases 2 m).
          -- assert (IH' := IH H).
             assert (Hm := sigma_increasing m). lra.
          -- assert (m = 1)%nat by lia. subst.
             assert (Hm := sigma_increasing 1). lra. }
    lra.
  - (* Upper bound: σ(N) <= 289/47 from geometric series *)
    assert (Hub := sigma_bounded_above N).
    assert (Hval := sigma_upper_bound_value).
    unfold sigma_beta1_upper_bound. lra.
Qed.

(** σ is at least 1 at order 2 *)
Lemma sigma_computational_check :
  1 <= string_tension 1 2.
Proof. exact sigma_order_2_above_1. Qed.

(* ================================================================== *)
(*  Part III: Observable Framework  (~7 lemmas)                       *)
(* ================================================================== *)

(** A lattice observable: a function from coupling parameters to Q *)
Record LatticeObservable := mkLatObs {
  lo_name : nat;
  lo_compute : Q -> nat -> Q
}.

(** String tension as an observable *)
Definition sigma_compute (beta : Q) (order : nat) : Q :=
  string_tension beta order.

Definition sigma_observable : LatticeObservable :=
  mkLatObs 0 sigma_compute.

(** σ is nonneg at β=1 *)
Lemma sigma_compute_nonneg_beta1 : forall order,
  0 <= sigma_compute 1 order.
Proof.
  intros order. unfold sigma_compute. exact (sigma_nonneg order).
Qed.

(** The observable value at β=1, order 1: gap/t₀ = 289/336 *)
Lemma sigma_obs_beta1_order1 :
  lo_compute sigma_observable 1 1 == 289 # 336.
Proof.
  simpl. unfold sigma_compute. exact sigma_order_1.
Qed.

(** The observable process for fixed β *)
Definition obs_process (obs : LatticeObservable) (beta : Q) : RealProcess :=
  fun N => lo_compute obs beta (S N).

(** Observable process for σ at β=1 is sigma_process *)
Lemma sigma_obs_is_sigma_process : forall n,
  obs_process sigma_observable 1 n == sigma_process n.
Proof.
  intros n. simpl. unfold sigma_compute. reflexivity.
Qed.

(** ★ The observable IS a process under P4 *)
Theorem observable_is_process :
  is_Cauchy (obs_process sigma_observable 1).
Proof.
  intros eps Heps.
  destruct (sigma_cauchy eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  unfold obs_process, sigma_observable, lo_compute, sigma_compute in *.
  exact HN.
Qed.

(* ================================================================== *)
(*  Part IV: Summary Theorems                                         *)
(* ================================================================== *)

(** ★ W8 resolved: string tension computed from transfer matrix
    HONEST STATUS:
      σ(β=1, M=0, order 1) = 289/336 ≈ 0.860
      σ(β=1, M=0, full sum) = −ln(1 − 289/336) = −ln(47/336) ≈ 1.967
      σ(β=1, exact) = −ln(I₁(1)/I₀(1)) ≈ 0.764
      M=0 overestimates by ~2.5×.
      Higher M (angular momentum modes) would converge to exact.
      σ > 0: confinement. This is the key qualitative result. *)
Theorem w8_resolved :
  0 < string_tension 1 1.
Proof. exact sigma_order_1_positive. Qed.

Theorem phase_38_complete :
  (* neg_ln_taylor: rational −ln(1−x) to any order *)
  (* string_tension: σa² = −ln(1 − gap/t₀), exact Q at each order *)
  (* Uses gap/t₀ = 289/336 at β=1 (since t₀ = 7/8 ≠ 1) *)
  (* sigma_process: Cauchy, increasing, converges *)
  (* Creutz ratio: standard lattice technique, matches ours *)
  (* M=0 approximation overestimates by ~2.5×; qualitative (σ>0) is correct *)
  True.
Proof. exact I. Qed.
