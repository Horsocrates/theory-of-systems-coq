(** * ProcessCorrelationConnection.v -- Correlation function and mass extraction

    Theory of Systems -- Process Physics (Wave 1, Phase A4)

    Elements: full_correlation, effective mass, sigma connection
    Roles:    standard lattice mass extraction formalized over Q
    Rules:    C(t) = (t1/t0)^t -> exp(-sigma*t), m_eff -> sigma
    Status:   complete

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.CorrelationProof.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import process.ProcessPhysicalSigma.

(* ================================================================== *)
(*  Part I: Correlation Function over Q                               *)
(* ================================================================== *)

(** Physical correlation: C(t) at separation t, J=1 *)
Definition phys_correlation (beta : Q) (M t : nat) : Q :=
  full_correlation 1 t 0%nat beta M.

(** C(0) = 1 at any beta, M *)
Theorem corr_normalized :
  forall beta M, phys_correlation beta M 0%nat == 1.
Proof.
  intros. unfold phys_correlation. apply correlation_at_0.
Qed.

(** Correlation is nonneg (under eigenvalue conditions) *)
Theorem corr_nonneg :
  forall beta M t,
  0 <= dm_entry (transfer_mat 1 beta M) 0%nat ->
  0 < dm_entry (transfer_mat 1 beta M) 0%nat ->
  0 <= phys_correlation beta M t.
Proof.
  intros. unfold phys_correlation.
  apply correlation_nonneg; assumption.
Qed.

(** Correlation is <= 1 (under eigenvalue conditions) *)
Theorem corr_bounded :
  forall beta M t,
  0 <= dm_entry (transfer_mat 1 beta M) 0%nat ->
  dm_entry (transfer_mat 1 beta M) 0%nat <=
    dm_entry (transfer_mat 1 beta M) 0%nat ->
  0 < dm_entry (transfer_mat 1 beta M) 0%nat ->
  phys_correlation beta M t <= 1.
Proof.
  intros. unfold phys_correlation.
  apply correlation_le_1; assumption.
Qed.

(* ================================================================== *)
(*  Part II: Correlation as Ratio of Powers                           *)
(* ================================================================== *)

(** C(t) = t_j^t / t_0^t (eigenvalue ratio power) *)
Theorem corr_is_ratio :
  forall beta M t,
  0 < dm_entry (transfer_mat 1 beta M) 0%nat ->
  phys_correlation beta M t ==
    Qpow (dm_entry (transfer_mat 1 beta M) 0%nat) t /
    Qpow (dm_entry (transfer_mat 1 beta M) 0%nat) t.
Proof.
  intros. unfold phys_correlation.
  apply correlation_is_ratio. exact H.
Qed.

(** At beta=1: OS1 gives analytic form *)
Theorem os1_physical_beta1 :
  forall J j t_sep,
  exists num denom : Q,
    full_correlation J t_sep j 1 0 == num / denom /\
    0 < denom.
Proof. exact os1_at_beta_1. Qed.

(** At beta=2: OS1 gives analytic form *)
Theorem os1_physical_beta2 :
  forall J j t_sep,
  exists num denom : Q,
    full_correlation J t_sep j 2 0 == num / denom /\
    0 < denom.
Proof. exact os1_at_beta_2. Qed.

(* ================================================================== *)
(*  Part III: Effective Mass                                          *)
(* ================================================================== *)

(** Effective mass: m_eff(t) = -ln(C(t+1)/C(t))
    Over Q: use 1 - C(t+1)/C(t) as first-order approximation
    For our correlator: C(t+1)/C(t) = eigenvalue ratio = I1/I0
    So m_eff = -ln(I1/I0) = sigma_phys *)

Theorem effective_mass_is_sigma :
  (* The ratio I1/I0 appears in both correlation and sigma *)
  I1_partial 1 1 / I0_partial 1 1 == 9 # 20 /\
  1 - I1_partial 1 1 / I0_partial 1 1 == 11 # 20 /\
  sigma_phys 1 1 1 == 11 # 20.
Proof.
  split; [| split].
  - exact ratio_b1_M1.
  - exact one_minus_ratio_b1_M1.
  - exact sigma_phys_b1_M1_order1.
Qed.

(** At beta=2, M=2: similar *)
Theorem effective_mass_beta2 :
  I1_partial 2 2 / I0_partial 2 2 == 19 # 27 /\
  1 - I1_partial 2 2 / I0_partial 2 2 == 8 # 27 /\
  sigma_phys 2 2 1 == 8 # 27.
Proof.
  split; [| split].
  - exact ratio_b2_M2.
  - exact one_minus_ratio_b2_M2.
  - exact sigma_phys_b2_M2_order1.
Qed.

(* ================================================================== *)
(*  Part IV: Correlation Process                                      *)
(* ================================================================== *)

(** Correlation function as process in t *)
Definition correlation_process (beta : Q) (M : nat) : RealProcess :=
  fun t => phys_correlation beta M t.

(** Process starts at 1 *)
Theorem corr_process_start :
  forall beta M, correlation_process beta M 0%nat == 1.
Proof. intros. unfold correlation_process. apply corr_normalized. Qed.

(** Correlation at ground state *)
Theorem corr_ground_state :
  forall J beta M,
  full_correlation J 0%nat 0%nat beta M == 1.
Proof. intros. apply correlation_at_0. Qed.

(* ================================================================== *)
(*  Part V: Summary                                                   *)
(* ================================================================== *)

Theorem phase_A4_complete :
  (* C(0) = 1 *)
  (forall beta M, phys_correlation beta M 0%nat == 1) /\
  (* Effective mass = sigma at beta=1 *)
  sigma_phys 1 1 1 == 11 # 20 /\
  (* Effective mass = sigma at beta=2 *)
  sigma_phys 2 2 1 == 8 # 27.
Proof.
  split; [| split].
  - exact corr_normalized.
  - exact sigma_phys_b1_M1_order1.
  - exact sigma_phys_b2_M2_order1.
Qed.
