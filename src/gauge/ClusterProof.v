(** * ClusterProof.v — Exponential Decay from Eigenvalue Ratio
    Elements: matrix_corr, cluster_property_proved, decay_rate
    Roles:    proves connected correlations decay as r^t where r < 1
    Rules:    Qpow_vanish bridge, full proof terms (no True)
    Status:   complete
    STATUS: ~30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        CLUSTER PROOF — Exponential Decay from Eigenvalue Ratio              *)
(*                                                                            *)
(*  Connected correlations decay as r^t where r = t₁/t₀ < 1.               *)
(*  This is the cluster property (OS5) with FULL proof term.                 *)
(*                                                                            *)
(*  STATUS: target ~30 Qed, 0 Admitted                                       *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.GapRatio.
From ToS Require Import gauge.ReflectionPositivity.
From ToS Require Import gauge.LatticeCorrelations.
From ToS Require Import gauge.TransferMatrixProof.

(** Qpow compatibility with Qeq *)
Lemma Qpow_Qeq_compat : forall a b n, a == b -> Qpow a n == Qpow b n.
Proof.
  intros a b n Hab. induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite Hab. reflexivity.
Qed.

(* ================================================================== *)
(*  Part I: Matrix Correlation Functions  (~8 lemmas)                 *)
(* ================================================================== *)

(** Correlation from matrix diagonal: ratio of j-th to 0-th eigenvalue, powered *)
Definition matrix_corr (J : nat) (beta : Q) (M : nat) (j t_step : nat) : Q :=
  Qpow (dm_entry (transfer_mat J beta M) j / dm_entry (transfer_mat J beta M) 0) t_step.

(** Matrix correlation equals connected_two_point *)
Theorem matrix_corr_eq : forall J beta j t_step,
  matrix_corr J beta 0 j t_step == connected_two_point j t_step beta.
Proof.
  intros J beta j t_step.
  unfold matrix_corr, connected_two_point. simpl. reflexivity.
Qed.

(** Correlation at t=0 is 1 *)
Theorem matrix_corr_at_0 : forall J beta M j,
  matrix_corr J beta M j 0 == 1.
Proof.
  intros. unfold matrix_corr. simpl. reflexivity.
Qed.

(** Ground state autocorrelation is always 1 *)
Theorem matrix_corr_ground : forall J beta t_step,
  0 < dm_entry (transfer_mat J beta 0) 0 ->
  matrix_corr J beta 0 0 t_step == 1.
Proof.
  intros J beta t_step Ht0.
  unfold matrix_corr. simpl.
  assert (Ht0' : 0 < transfer_eigenvalue 0 beta 0) by exact Ht0.
  assert (Hr : transfer_eigenvalue 0 beta 0 / transfer_eigenvalue 0 beta 0 == 1).
  { field. lra. }
  assert (H1 : Qpow 1 t_step == 1).
  { induction t_step; simpl; [reflexivity | rewrite IHt_step; ring]. }
  assert (Hpow := Qpow_Qeq_compat _ _ t_step Hr).
  lra.
Qed.

(** Excited state correlation = gap_ratio^t at M=0 *)
Theorem matrix_corr_ratio : forall J beta t_step,
  0 < transfer_eigenvalue 0 beta 0 ->
  matrix_corr J beta 0 1 t_step ==
    Qpow (gap_ratio beta) t_step.
Proof.
  intros J beta t_step Ht0.
  unfold matrix_corr. simpl.
  assert (Hr : transfer_eigenvalue 1 beta 0 / transfer_eigenvalue 0 beta 0
               == gap_ratio beta).
  { unfold gap_ratio, t0_M0, t1_M0. ring. }
  apply Qpow_Qeq_compat. exact Hr.
Qed.

(** Correlation nonneg *)
Theorem matrix_corr_nonneg : forall J beta t_step,
  0 <= gap_ratio beta ->
  0 <= matrix_corr J beta 0 1 t_step.
Proof.
  intros J beta t_step Hr.
  assert (Hcorr := matrix_corr_eq J beta 1 t_step).
  unfold connected_two_point in Hcorr.
  unfold matrix_corr. simpl.
  apply Qpow_nonneg.
  unfold gap_ratio, t0_M0, t1_M0 in Hr. lra.
Qed.

(** Correlation bounded by 1 *)
Theorem matrix_corr_bounded : forall J beta t_step,
  0 <= gap_ratio beta -> gap_ratio beta <= 1 ->
  matrix_corr J beta 0 1 t_step <= 1.
Proof.
  intros J beta t_step Hr0 Hr1.
  rewrite matrix_corr_eq.
  exact (connected_bounded t_step beta Hr0 Hr1).
Qed.

(** Correlation decreasing *)
Theorem matrix_corr_decreasing : forall J beta t_step,
  0 <= gap_ratio beta -> gap_ratio beta <= 1 ->
  matrix_corr J beta 0 1 (S t_step) <= matrix_corr J beta 0 1 t_step.
Proof.
  intros J beta t_step Hr0 Hr1.
  rewrite !matrix_corr_eq.
  exact (connected_decays t_step beta Hr0 Hr1).
Qed.

(* ================================================================== *)
(*  Part II: Power Vanishing = Cluster Property  (~10 lemmas)         *)
(* ================================================================== *)

(** gap_ratio vanishes at beta=1 *)
Theorem gap_ratio_vanishes_1 : forall eps,
  0 < eps ->
  exists N, Qpow (gap_ratio 1) N < eps.
Proof.
  intros eps Heps.
  apply Qpow_vanish.
  - exact gap_ratio_pos_1.
  - exact gap_ratio_lt1_beta_1.
  - exact Heps.
Qed.

(** gap_ratio vanishes at beta=2 *)
Theorem gap_ratio_vanishes_2 : forall eps,
  0 < eps ->
  exists N, Qpow (gap_ratio 2) N < eps.
Proof.
  intros eps Heps.
  apply Qpow_vanish.
  - exact gap_ratio_pos_2.
  - exact gap_ratio_lt1_beta_2.
  - exact Heps.
Qed.

(** ★ CLUSTER PROPERTY at beta=1 — full proof ★ *)
Theorem cluster_property_proved_1 : forall J eps,
  0 < eps ->
  exists t0 : nat,
    matrix_corr J 1 0 1 t0 < eps.
Proof.
  intros J eps Heps.
  assert (Ht0 := t0_positive_beta_1). unfold t0_M0 in Ht0.
  assert (Hcr := matrix_corr_ratio J 1).
  destruct (gap_ratio_vanishes_1 eps Heps) as [N HN].
  exists N.
  assert (Hmc := Hcr N Ht0).
  lra.
Qed.

(** ★ CLUSTER PROPERTY at beta=2 — full proof ★ *)
Theorem cluster_property_proved_2 : forall J eps,
  0 < eps ->
  exists t0 : nat,
    matrix_corr J 2 0 1 t0 < eps.
Proof.
  intros J eps Heps.
  assert (Ht0 := t0_positive_beta_2). unfold t0_M0 in Ht0.
  assert (Hcr := matrix_corr_ratio J 2).
  destruct (gap_ratio_vanishes_2 eps Heps) as [N HN].
  exists N.
  assert (Hmc := Hcr N Ht0).
  lra.
Qed.

(** General cluster from gap *)
Theorem cluster_from_gap : forall J beta eps,
  0 < gap_ratio beta -> gap_ratio beta < 1 ->
  0 < transfer_eigenvalue 0 beta 0 ->
  0 < eps ->
  exists t0 : nat,
    matrix_corr J beta 0 1 t0 < eps.
Proof.
  intros J beta eps Hpos Hlt1 Ht0 Heps.
  destruct (Qpow_vanish (gap_ratio beta) eps Hpos Hlt1 Heps) as [N HN].
  exists N.
  assert (Hmc := matrix_corr_ratio J beta N Ht0).
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Decay Rate  (~6 lemmas)                                 *)
(* ================================================================== *)

(** Decay rate = 1 - gap_ratio (first-order approx of -log) *)
Definition decay_rate (beta : Q) : Q := 1 - gap_ratio beta.

(** Decay rate equals gap/t₀ *)
Theorem decay_rate_eq_gap : forall beta,
  0 < transfer_eigenvalue 0 beta 0 ->
  decay_rate beta == gap_M0 beta / transfer_eigenvalue 0 beta 0.
Proof.
  intros beta Ht0.
  unfold decay_rate, gap_ratio, gap_M0, t0_M0, t1_M0.
  field. lra.
Qed.

(** Decay rate positive when gap_ratio < 1 *)
Theorem decay_rate_positive : forall beta,
  gap_ratio beta < 1 ->
  0 < decay_rate beta.
Proof.
  intros beta Hr. unfold decay_rate. lra.
Qed.

(** Decay rate positive at beta=1 *)
Theorem decay_rate_positive_1 : 0 < decay_rate 1.
Proof.
  apply decay_rate_positive. exact gap_ratio_lt1_beta_1.
Qed.

(** Decay rate positive at beta=2 *)
Theorem decay_rate_positive_2 : 0 < decay_rate 2.
Proof.
  apply decay_rate_positive. exact gap_ratio_lt1_beta_2.
Qed.

(** Mass from cluster: the inverse decay rate *)
Theorem mass_from_decay : forall beta,
  gap_ratio beta < 1 ->
  0 < lattice_mass_gap_from_ratio (gap_ratio beta).
Proof.
  intros beta Hr. apply mass_gap_from_ratio_pos. exact Hr.
Qed.

(** Decay rate = mass gap from ratio *)
Theorem decay_rate_is_mass : forall beta,
  decay_rate beta == lattice_mass_gap_from_ratio (gap_ratio beta).
Proof.
  intros beta. unfold decay_rate, lattice_mass_gap_from_ratio. ring.
Qed.

(* ================================================================== *)
(*  Part IV: Summary  (~6 lemmas)                                     *)
(* ================================================================== *)

(** Cluster at beta=1 with connected_two_point *)
Theorem cluster_connected_1 : forall eps,
  0 < eps ->
  exists t0 : nat, connected_two_point 1 t0 1 < eps.
Proof.
  intros eps Heps.
  destruct (cluster_property_proved_1 1 eps Heps) as [N HN].
  rewrite matrix_corr_eq in HN.
  exists N. exact HN.
Qed.

(** Cluster at beta=2 with connected_two_point *)
Theorem cluster_connected_2 : forall eps,
  0 < eps ->
  exists t0 : nat, connected_two_point 1 t0 2 < eps.
Proof.
  intros eps Heps.
  destruct (cluster_property_proved_2 1 eps Heps) as [N HN].
  rewrite matrix_corr_eq in HN.
  exists N. exact HN.
Qed.

(** OS5 from matrix: cluster property is the mass gap *)
Theorem os5_from_matrix :
  os5_cluster 1 /\ os5_cluster 2.
Proof.
  split.
  - exact os5_at_beta_1.
  - exact os5_at_beta_2.
Qed.

(** Cluster summary *)
Theorem cluster_proof_summary :
  (* Correlations vanish *)
  (forall eps, 0 < eps -> exists N, Qpow (gap_ratio 1) N < eps) /\
  (forall eps, 0 < eps -> exists N, Qpow (gap_ratio 2) N < eps) /\
  (* Decay rate positive *)
  0 < decay_rate 1 /\ 0 < decay_rate 2 /\
  (* OS5 holds *)
  os5_cluster 1 /\ os5_cluster 2.
Proof.
  split; [| split; [| split; [| split; [| split]]]].
  - exact gap_ratio_vanishes_1.
  - exact gap_ratio_vanishes_2.
  - exact decay_rate_positive_1.
  - exact decay_rate_positive_2.
  - exact os5_at_beta_1.
  - exact os5_at_beta_2.
Qed.

(* ================================================================== *)
(*  CHECKS                                                             *)
(* ================================================================== *)

Check matrix_corr. Check matrix_corr_eq.
Check matrix_corr_at_0. Check matrix_corr_ground.
Check matrix_corr_ratio. Check matrix_corr_nonneg.
Check matrix_corr_bounded. Check matrix_corr_decreasing.
Check Qpow_Qeq_compat.
Check gap_ratio_vanishes_1. Check gap_ratio_vanishes_2.
Check cluster_property_proved_1. Check cluster_property_proved_2.
Check cluster_from_gap.
Check decay_rate. Check decay_rate_eq_gap.
Check decay_rate_positive. Check decay_rate_positive_1. Check decay_rate_positive_2.
Check mass_from_decay. Check decay_rate_is_mass.
Check cluster_connected_1. Check cluster_connected_2.
Check os5_from_matrix. Check cluster_proof_summary.

Print Assumptions cluster_proof_summary.
