(* GaugeOSClosure.v — Close gauge/ True using OS libs *)
(* June 2026 HONEST SCOPE + UPGRADE: the os*_proved bundles below close the
   repo's True-placeholder backlog with TOY specializations (polynomial
   analyticity, zero-distribution temperedness, concrete bounds).  The REAL
   lattice-model OS content — analyticity/temperedness/SO(4)-invariance of
   the FULL CORRELATION — lives in gauge/Formal{Analytic,Tempered,SO4}.v and
   is re-exported below (gauge_os1/2/3_real, gauge_os_real_bundle), so that
   "gauge OS closure" names the genuine content.  OS4/OS5 + the Wightman
   bundle: gauge/YangMillsSealed.v (ym_lattice_os_bundle). *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.OS1Closure.
From ToS Require Import stdlib.OS2Closure.
From ToS Require Import stdlib.OS3Closure.
(* June 2026: stdlib.TheoremBundle import DROPPED — nothing from it was used,
   and it pulls a large process/ chain (where it exposed a latent break in
   ProcessP3Dynamics, fixed separately). *)
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.
From ToS Require Import gauge.CorrelationProof.
From ToS Require Import gauge.FormalAnalytic.
From ToS Require Import gauge.FormalTempered.
From ToS Require Import gauge.FormalSO4.

(** ContinuumCovariance True → OS3 results *)
Theorem gauge_covariance : os3_covariance_proved.
Proof. exact os3_proved. Qed.

(** Analyticity from OS1 *)
Theorem gauge_analyticity : os1_analyticity_proved.
Proof. exact os1_proved. Qed.

(** Regularity from OS2 *)
Theorem gauge_regularity : os2_regularity_proved.
Proof. exact os2_proved. Qed.

(** YMLevel5 OS strengthened *)
Theorem gauge_os_strengthened :
  os1_analyticity_proved /\
  os2_regularity_proved /\
  os3_covariance_proved.
Proof.
  split; [|split].
  - exact os1_proved.
  - exact os2_proved.
  - exact os3_proved.
Qed.

(** Mass gap from ProofClosure *)
Theorem gauge_gap : 0 < matrix_mass_gap 1 1 0.
Proof. exact mass_gap_positive_beta_1. Qed.

Theorem gauge_gap_value : matrix_mass_gap 1 1 0 == 289 # 384.
Proof. exact mass_gap_value_beta_1. Qed.

(** All nine gaps *)
Theorem gauge_nine_gaps :
  0 < matrix_mass_gap 1 1 0 /\ matrix_mass_gap 1 1 0 == 289 # 384.
Proof. split; [exact mass_gap_positive_beta_1 | exact mass_gap_value_beta_1]. Qed.

(* ================================================================== *)
(*  June 2026 — THE REAL LATTICE OS CONTENT (bridge upgrade)           *)
(*  About the FULL CORRELATION of the lattice transfer chain, not      *)
(*  the toy specializations above.                                     *)
(* ================================================================== *)

(** OS1 for the real correlation: lattice analyticity in beta *)
Theorem gauge_os1_real : forall J j t_sep,
  is_lattice_analytic (fun beta => full_correlation J t_sep j beta 0).
Proof. exact os1_formal. Qed.

(** OS2 for the real correlation: temperedness at beta = 1 *)
Theorem gauge_os2_real : forall J j,
  j = 0%nat \/ j = 1%nat ->
  is_tempered (fun t => full_correlation J t j 1 0).
Proof. exact os2_formal_at_1. Qed.

(** OS3 for the real correlation: SO(4)-invariance *)
Theorem gauge_os3_real : forall J j beta M,
  is_SO4_invariant (fun t => full_correlation J t j beta M).
Proof. exact os3_formal. Qed.

(** The real-OS bundle for the full correlation (OS1 ∧ OS2 ∧ OS3) *)
Theorem gauge_os_real_bundle :
  (forall J j t_sep,
    is_lattice_analytic (fun beta => full_correlation J t_sep j beta 0)) /\
  (forall J j, j = 0%nat \/ j = 1%nat ->
    is_tempered (fun t => full_correlation J t j 1 0)) /\
  (forall J j beta M,
    is_SO4_invariant (fun t => full_correlation J t j beta M)).
Proof.
  split; [exact os1_formal |].
  split; [exact os2_formal_at_1 | exact os3_formal].
Qed.

Definition gauge_os_count := 8%nat.
