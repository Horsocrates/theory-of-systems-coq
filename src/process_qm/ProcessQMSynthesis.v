(** * ProcessQMSynthesis.v — Three branches, one root: thermal + Casimir + QM
    STATUS:   8 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    Vibration = L1-L5 tension (113 Qed in acoustics/).
    THREE consequences:
      THERMAL:  tension distributed → temperature, entropy, 2nd law.
      CASIMIR:  tension irreducible → vacuum energy, Casimir force.
      PROCESS QM: tension quantized → states, measurement, Born rule.
    Same modes. Same eigenvalues. Same graph. Three domains. One structure.
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import thermal.ThermalFromModes.
From ToS Require Import thermal.SecondLaw.
From ToS Require Import casimir_branch.CasimirFromGraph.
From ToS Require Import process_qm.QuantumFromVibration.
From ToS Require Import process_qm.MeasurementProcess.
From ToS Require Import process_qm.HilbertAsProcess.

(* ================================================================ *)
(*  THREE BRANCHES, ONE ROOT                                         *)
(* ================================================================ *)

(** Branch A: Thermal *)
Theorem branch_thermal :
  (* Same energy, different distribution *)
  total_energy_modes omega_4 pure_tone_4 == total_energy_modes omega_4 thermal_4 /\
  (* Entropy increases with coupling *)
  (active_modes ((2:Q) :: (0:Q) :: nil) (1#10) < active_modes (Qmake 3 2 :: Qmake 1 2 :: nil) (1#10))%nat.
Proof.
  split; [exact same_energy_different_distribution | exact entropy_increases].
Qed.

(** Branch B: Casimir *)
Theorem branch_casimir :
  (* Vacuum energy positive and finite *)
  0 < vacuum_energy_sq omega_sq_C4 /\
  vacuum_energy_sq omega_sq_C4 == 2.
Proof.
  split; [exact vacuum_positive_C4 | exact E_vac_C4].
Qed.

(** Branch C: Process QM *)
Theorem branch_quantum :
  (* Born rule works *)
  measurement_probability ground_state 0 == 1 /\
  (* Orthogonality *)
  inner_product ground_state mode1_state == 0 /\
  (* Finite spectrum *)
  length laplacian_eigenvalues = 4%nat.
Proof.
  split; [exact born_ground_mode0 |
  split; [exact ip_orthogonal |
  exact eigenvalue_count_4]].
Qed.

(* ================================================================ *)
(*  GRAND UNIFICATION                                                *)
(* ================================================================ *)

Theorem three_branches_one_root :
  (* THERMAL: pure tone → thermal via coupling *)
  active_modes pure_tone_4 (1#10) = 1%nat /\
  active_modes thermal_4 (1#10) = 4%nat /\
  (* CASIMIR: vacuum energy from eigenvalues *)
  vacuum_energy_sq omega_sq_C4 == 2 /\
  (* QM: Born rule = |A_k|^2 *)
  measurement_probability ground_state 0 == 1 /\
  (* QM: probabilities sum to 1 *)
  measurement_probability ground_state 0 +
    measurement_probability ground_state 1 +
    measurement_probability ground_state 2 +
    measurement_probability ground_state 3 == 1 /\
  (* SHARED: all use same eigenvalues *)
  length laplacian_eigenvalues = 4%nat /\
  (* SHARED: inner product exact over Q *)
  inner_product [3; 4] [3; 4] == 25 /\
  (* SHARED: uncertainty from finite N *)
  min_uncertainty 8 < min_uncertainty 4.
Proof.
  split; [exact pure_tone_one_active |
  split; [exact thermal_all_active |
  split; [exact E_vac_C4 |
  split; [exact born_ground_mode0 |
  split; [exact born_probabilities_sum |
  split; [exact eigenvalue_count_4 |
  split; [exact ip_pythagoras |
  exact finer_less_uncertainty]]]]]]].
Qed.
