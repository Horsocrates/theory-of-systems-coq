(* ProcessSU2DetailConnection.v *)
(* Phase G7: Connect SU(2) detail gauge files *)

From Stdlib Require Import QArith.
From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.SU2Characters.
From ToS Require Import gauge.SU2Group.
From ToS Require Import gauge.SU2Lattice.
From ToS Require Import gauge.SU2TransferMatrix.
From ToS Require Import gauge.SU2Synthesis.
From ToS Require Import gauge.ConfinementCorrection.
From ToS Require Import gauge.InstantonEnhanced.
From ToS Require Import gauge.TopologicalObstruction.
From ToS Require Import gauge.PhaseB_Synthesis.
From ToS Require Import gauge.GaugeSynthesis.

Open Scope Q_scope.

(* === SU2Characters connections === *)
(* Chebyshev polynomials as SU(2) characters *)

Definition chebyshev_recurrence_connected :=
  SU2Characters.chebyshev_recurrence.

Definition wm_0_connected :=
  SU2Characters.wm_0.

Definition wm_2_connected :=
  SU2Characters.wm_2.

Definition wm_4_connected :=
  SU2Characters.wm_4.

Definition su2_characters_summary_connected :=
  SU2Characters.su2_characters_summary.

(* Physical: U_n(1) = n+1 (dimension formula) *)
(* Weighted moments: wm_0=4/3, wm_2=4/15, wm_4=4/35 *)

(* === SU2Group connections === *)
(* Quaternion algebra for SU(2) *)

Definition qmul_assoc_connected :=
  SU2Group.qmul_assoc.

Definition qmul_noncommutative_connected :=
  SU2Group.qmul_noncommutative.

Definition unit_closed_connected :=
  SU2Group.unit_closed.

Definition trace_cyclic_connected :=
  SU2Group.trace_cyclic.

Definition su2_group_summary_connected :=
  SU2Group.su2_group_summary.

(* Physical: SU(2) = unit quaternions, non-abelian *)

(* === SU2Lattice connections === *)
(* SU(2) lattice gauge theory *)

Definition su2_gauge_equiv_refl_connected :=
  SU2Lattice.su2_gauge_equiv_refl.

Definition su2_action_scale_beta_connected :=
  SU2Lattice.su2_action_scale_beta.

Definition su2_vs_u1_connected :=
  SU2Lattice.su2_vs_u1.

Definition su2_lattice_summary_connected :=
  SU2Lattice.su2_lattice_summary.

Definition su2_gauge_invariance_main_connected :=
  SU2Lattice.su2_gauge_invariance_main.

(* Physical: lattice gauge theory with SU(2) links *)

(* === SU2TransferMatrix connections === *)
(* Transfer matrix and mass gap *)

Definition su2_mass_gap_positive_connected :=
  SU2TransferMatrix.su2_mass_gap_positive.

Definition su2_gap_vs_u1_connected :=
  SU2TransferMatrix.su2_gap_vs_u1.

Definition su2_transfer_summary_connected :=
  SU2TransferMatrix.su2_transfer_summary.

Definition su2_transfer_main_connected :=
  SU2TransferMatrix.su2_transfer_main.

(* Physical: SU(2) mass gap 3× larger than U(1) *)

(* === SU2Synthesis connections === *)

Definition su2_mass_gap_exists_connected :=
  SU2Synthesis.su2_mass_gap_exists.

Definition su2_synthesis_main_connected :=
  SU2Synthesis.su2_synthesis_main.

(* === ConfinementCorrection connections === *)

Definition confinement_main_connected :=
  ConfinementCorrection.confinement_main.

Definition three_mechanisms_missing_connected :=
  ConfinementCorrection.three_mechanisms_missing.

(* Physical: corrections beyond leading-order confinement *)

(* === InstantonEnhanced connections === *)

Definition instanton_main_connected :=
  InstantonEnhanced.instanton_main.

Definition wall_is_artifact_connected :=
  InstantonEnhanced.wall_is_artifact.

(* Physical: instanton contributions enhance the gap *)

(* === TopologicalObstruction connections === *)

Definition obstruction_summary_connected :=
  TopologicalObstruction.obstruction_summary.

Definition topological_main_connected :=
  TopologicalObstruction.topological_main.

(* Physical: honest limitations of M=0 model *)

(* === PhaseB_Synthesis connections === *)

Definition yang_mills_lattice_gap_PROVED_connected :=
  PhaseB_Synthesis.yang_mills_lattice_gap_PROVED.

Definition phase_b_summary_connected :=
  PhaseB_Synthesis.phase_b_summary.

(* === GaugeSynthesis connections === *)

Definition lattice_gauge_main_connected :=
  GaugeSynthesis.lattice_gauge_main.

Definition mass_gap_eigenvector_theorem_connected :=
  GaugeSynthesis.mass_gap_eigenvector_theorem.

(* === Synthesis === *)

Theorem su2_detail_complete :
  (* 10 SU(2) gauge modules connected *)
  (* Quaternion algebra, characters, confinement corrections *)
  forall beta : Q, 0 < beta -> beta < 8 ->
    0 < SU2TransferMatrix.su2_mass_gap beta.
Proof. exact SU2TransferMatrix.su2_mass_gap_positive. Qed.

Definition g7_theorem_count := 25%nat.
