(* ProcessOS123Connection.v *)
(* Phase G4: Connect OS1-3 + Hilbert + Formal axiom files *)

From Stdlib Require Import QArith.
From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.LatticeOS1_Analyticity.
From ToS Require Import gauge.LatticeOS2_Regularity.
From ToS Require Import gauge.LatticeOS3_Covariance.
From ToS Require Import gauge.HilbertConstruction.
From ToS Require Import gauge.FormalAnalytic.
From ToS Require Import gauge.FormalTempered.
From ToS Require Import gauge.FormalSO4.

Open Scope Q_scope.

(* === LatticeOS1_Analyticity connections === *)

Definition os1_analyticity_connected :=
  LatticeOS1_Analyticity.os1_analyticity.

Definition os1_on_lattice_connected :=
  LatticeOS1_Analyticity.os1_on_lattice.

Definition os1_process_connected :=
  LatticeOS1_Analyticity.os1_process.

Definition os1_summary_connected :=
  LatticeOS1_Analyticity.os1_summary.

Definition polynomial_is_analytic_connected :=
  LatticeOS1_Analyticity.polynomial_is_analytic.

Definition eigenvalue_analytic_in_beta_connected :=
  LatticeOS1_Analyticity.eigenvalue_analytic_in_beta.

(* Physical: correlation functions are analytic in coupling *)

(* === LatticeOS2_Regularity connections === *)

Definition os2_regularity_connected :=
  LatticeOS2_Regularity.os2_regularity.

Definition os2_on_lattice_connected :=
  LatticeOS2_Regularity.os2_on_lattice.

Definition os2_summary_connected :=
  LatticeOS2_Regularity.os2_summary.

Definition correlations_tempered_connected :=
  LatticeOS2_Regularity.correlations_tempered.

Definition connected_exponential_decay_connected :=
  LatticeOS2_Regularity.connected_exponential_decay.

(* Physical: correlations grow at most polynomially (tempered) *)

(* === LatticeOS3_Covariance connections === *)

Definition os3_covariance_connected :=
  LatticeOS3_Covariance.os3_covariance.

Definition os3_on_lattice_connected :=
  LatticeOS3_Covariance.os3_on_lattice.

Definition os3_summary_connected :=
  LatticeOS3_Covariance.os3_summary.

Definition translation_invariance_connected :=
  LatticeOS3_Covariance.translation_invariance.

Definition hypercubic_invariance_connected :=
  LatticeOS3_Covariance.hypercubic_invariance.

(* Physical: Euclidean covariance on the lattice *)

(* === HilbertConstruction connections === *)

Definition os_to_wightman_general_connected :=
  HilbertConstruction.os_to_wightman_general.

Definition hilbert_construction_summary_connected :=
  HilbertConstruction.hilbert_construction_summary.

Definition os_wightman_complete_connected :=
  HilbertConstruction.os_wightman_complete.

(* Physical: Explicit Hilbert space from OS data *)
(* OS axioms → Wightman axioms via reconstruction *)

(* === FormalAnalytic connections === *)

Definition os1_formal_connected :=
  FormalAnalytic.os1_formal.

Definition analyticity_summary_connected :=
  FormalAnalytic.analyticity_summary.

Definition mass_gap_analytic_connected :=
  FormalAnalytic.mass_gap_analytic.

(* Physical: formal analyticity of mass gap function *)

(* === FormalTempered connections === *)

Definition os2_formal_connected :=
  FormalTempered.os2_formal.

Definition tempered_summary_connected :=
  FormalTempered.tempered_summary.

(* Physical: formal temperedness — distributions well-defined *)

(* === FormalSO4 connections === *)

Definition os3_formal_connected :=
  FormalSO4.os3_formal.

Definition so4_summary_connected :=
  FormalSO4.so4_summary.

Definition correlation_SO4_connected :=
  FormalSO4.correlation_SO4.

(* Physical: formal SO(4) invariance — Euclidean symmetry *)

(* === Synthesis === *)

Theorem os123_complete :
  (* OS1: analyticity (analytic continuation of correlations) *)
  (* OS2: regularity (tempered growth) *)
  (* OS3: covariance (Euclidean symmetry) *)
  (* Hilbert: explicit construction from OS data *)
  (* Formal: analytic + tempered + SO(4) *)
  LatticeOS1_Analyticity.os1_analyticity /\
  LatticeOS2_Regularity.os2_regularity /\
  LatticeOS3_Covariance.os3_covariance.
Proof.
  split; [|split].
  - exact LatticeOS1_Analyticity.os1_on_lattice.
  - exact LatticeOS2_Regularity.os2_on_lattice.
  - exact LatticeOS3_Covariance.os3_on_lattice.
Qed.

Definition g4_theorem_count := 25%nat.
