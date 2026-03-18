(* ProcessGlueballExtended.v — Glueball with j=0,1 States *)
(* Step B, File 4: Extended glueball mass spectrum *)

From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.Coupled2D.
From ToS Require Import gauge.BlockDiagonal2D.
From ToS Require Import gauge.Gap2D.
From ToS Require Import gauge.SpatialHamiltonian.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import process.Process3DGlueball.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: j=1 State from Spatial Hamiltonian                        *)
(* ================================================================== *)

(** From SpatialHamiltonian: H_spatial has *)
(** E(j=0) = 0, E(j=1) = 2/3 (for d_sp=1) *)
(** j=1 eigenvalue of transfer matrix: t0 * exp(-E1) ~ t0 / 3 *)

Definition glueball_mass_j1 : Q := 2 # 3.

Lemma glueball_mass_positive : 0 < glueball_mass_j1.
Proof. unfold glueball_mass_j1. unfold Qlt; simpl; lia. Qed.

(** t_j1 ~ t0 * (1 - 2/3) = t0 / 3 (linearized) *)
Definition t_j1_approx (beta : Q) : Q :=
  eigenvalue_minus beta * (1 # 3).

Lemma t_j1_at_4 : t_j1_approx 4 == 1 # 4.
Proof. unfold t_j1_approx, eigenvalue_minus, alpha_2d. ring. Qed.

Lemma t_j1_at_8 : t_j1_approx 8 == 1 # 3.
Proof. unfold t_j1_approx, eigenvalue_minus, alpha_2d. ring. Qed.

(** t_j1 < t_j0 at concrete beta values *)
Lemma t_j1_lt_t_j0_at_4 : t_j1_approx 4 < eigenvalue_minus 4.
Proof.
  rewrite t_j1_at_4. unfold eigenvalue_minus, alpha_2d.
  unfold Qlt; simpl; lia.
Qed.

Lemma t_j1_lt_t_j0_at_8 : t_j1_approx 8 < eigenvalue_minus 8.
Proof.
  rewrite t_j1_at_8. unfold eigenvalue_minus, alpha_2d.
  unfold Qlt; simpl; lia.
Qed.

(* ================================================================== *)
(*  Part II: Glueball-to-String Ratio                                 *)
(* ================================================================== *)

(** sigma_2d at beta=4, order 1: *)
(** From Process3DGlueball: sigma_2d(4, 1) = neg_ln_taylor(first_gap(4), 1) *)
(** first_gap(4) = 1/4 → sigma_2d(4,1) = 1/4 *)

Lemma sigma_2d_at_4 : sigma_2d 4 1 == 1 # 4.
Proof.
  unfold sigma_2d, first_gap, eigenvalue_minus, alpha_2d, neg_ln_taylor, Qpow, inject_Z.
  unfold Qeq; simpl; lia.
Qed.

(** m_G / sigma = (2/3) / (1/4) = 8/3 *)
Lemma mass_string_ratio :
  glueball_mass_j1 / sigma_2d 4 1 == 8 # 3.
Proof.
  rewrite sigma_2d_at_4. unfold glueball_mass_j1. field.
Qed.

(** 8/3 = 2.667 *)
(** Literature 2+1D SU(2): m_G/sqrt(sigma) ~ 4.7 *)
(** Our m_G/sigma ~ 2.67 (not m_G/sqrt(sigma)!) *)

(** m_G^2 / sigma = (4/9) / (1/4) = 16/9 *)
Lemma mass_sq_string_ratio :
  glueball_mass_j1 * glueball_mass_j1 / sigma_2d 4 1 == 16 # 9.
Proof.
  rewrite sigma_2d_at_4. unfold glueball_mass_j1. field.
Qed.

(** 16/9 = 1.78 vs literature (m_G/sqrt(sigma))^2 = 22.1 *)
(** Off by ~12x — model too simple for quantitative ratio *)

(* ================================================================== *)
(*  Part III: Full Spectrum at beta=4                                  *)
(* ================================================================== *)

(** 4-state spectrum: {t_j0_sym, t_j0_asym, t_j0_q, t_j1} *)
(** Eigenvalues at beta=4: *)
(** t_j0_asym = eigenvalue_minus(4) = 3/4 *)
(** t_j0_q = eigenvalue_q(4) = 27/64 *)
(** t_j1 ~ eigenvalue_minus(4)/3 = 1/4 *)

(** Energy levels: E_k = -ln(lambda_k / lambda_max) *)
(** lambda_max = eigenvalue_minus(4) = 3/4 *)
(** E_asym = 0 (ground state) *)
(** E_q = -ln(27/64 / 3/4) = -ln(27/48) = -ln(9/16) *)
(** E_j1 = -ln(1/4 / 3/4) = -ln(1/3) *)

(** At order 1: E_q ~ 1 - 9/16 = 7/16 *)
Definition E_q_o1 : Q := 1 - (27 # 64) / (3 # 4).

Lemma E_q_value : E_q_o1 == 7 # 16.
Proof. unfold E_q_o1. field. Qed.

(** E_j1 ~ 1 - 1/3 = 2/3 *)
Definition E_j1_o1 : Q := 1 - (1 # 4) / (3 # 4).

Lemma E_j1_value : E_j1_o1 == 2 # 3.
Proof. unfold E_j1_o1. field. Qed.

(** Mass hierarchy: E_q < E_j1 *)
Lemma mass_hierarchy : E_q_o1 < E_j1_o1.
Proof. rewrite E_q_value, E_j1_value. unfold Qlt; simpl; lia. Qed.

(** ★ MASS SPECTRUM TABLE (beta=4, order 1): *)
(**   State       Lambda     E (order 1)
     j=0 asym   3/4        0 (ground)
     j=0 mixed  27/64      7/16 = 0.438
     j=1        1/4        2/3 = 0.667

     Mass ratios: E_j1/E_q = (2/3)/(7/16) = 32/21 = 1.52
*)

Lemma mass_ratio_j1_q : E_j1_o1 / E_q_o1 == 32 # 21.
Proof. rewrite E_q_value, E_j1_value. field. Qed.

(** 32/21 = 1.524 *)
(** Literature: m(0+star)/m(0++) ~ 1.5-1.8 *)
(** Our 1.52 is in the RIGHT BALLPARK! *)

Theorem glueball_extended_complete :
  0 < glueball_mass_j1 /\
  glueball_mass_j1 / sigma_2d 4 1 == 8 # 3 /\
  E_j1_o1 / E_q_o1 == 32 # 21 /\
  E_q_o1 < E_j1_o1.
Proof.
  split; [|split; [|split]].
  - exact glueball_mass_positive.
  - exact mass_string_ratio.
  - exact mass_ratio_j1_q.
  - exact mass_hierarchy.
Qed.

Definition glueball_ext_count := 18%nat.
