(** * HeisenbergSynthesis.v — Grand Synthesis: Heisenberg Matrices on Finite Lattice
    Elements: All results from HeisenbergReturn, FiniteSize, Oscillator, Uncertainty
    Roles:    Unified view: [X,P] as Laplacian, finite-size errors, oscillator traces
    Rules:    Commutator = -Laplacian, uncertainty state-dependent, osc > box
    Status:   Stdlib
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessHilbert.
From ToS Require Import stdlib.MatN.
From ToS Require Import stdlib.SpectralFlowTraces.
From ToS Require Import stdlib.HeisenbergReturn.
From ToS Require Import stdlib.HeisenbergFiniteSize.
From ToS Require Import stdlib.OscillatorRational.
From ToS Require Import stdlib.OscillatorComparison.
From ToS Require Import stdlib.HeisenbergUncertainty.
Open Scope Q_scope.

(* ================================================================== *)
(*  PILLAR 1: COMMUTATOR = NEGATIVE LAPLACIAN                          *)
(* ================================================================== *)

Theorem pillar_commutator_is_laplacian :
  (* Off-diagonal entries are -1 (adjacency with sign) *)
  XP_comm 3 0 1 == -(1) /\
  XP_comm 4 1 2 == -(1) /\
  (* Diagonal entries are 0 *)
  XP_comm 3 1 1 == 0 /\
  XP_comm 4 2 2 == 0 /\
  XP_comm 5 3 3 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  PILLAR 2: FINITE-SIZE ERROR GROWS BUT IS STRUCTURED                 *)
(* ================================================================== *)

Theorem pillar_finite_size_error :
  (* Error norm grows: 7 < 10 < 13 *)
  error_norm_sq 3 < error_norm_sq 4 /\
  error_norm_sq 4 < error_norm_sq 5 /\
  (* Error is exactly 3K-2: 7, 10, 13 *)
  error_norm_sq 3 == 7 /\
  error_norm_sq 4 == 10 /\
  error_norm_sq 5 == 13.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  PILLAR 3: OSCILLATOR TRACES AND COMPARISON                          *)
(* ================================================================== *)

Theorem pillar_oscillator_traces :
  (* tr(H^2) = K(K-1) *)
  osc_tr2 3 = (3 * 2)%Z /\
  osc_tr2 5 = (5 * 4)%Z /\
  (* K=3 geometric: tr(H^6) = 3 * tr(H^4) *)
  osc_tr6 3 = (3 * osc_tr4 3)%Z /\
  (* Oscillator exceeds box: osc_tr2(5) - box_tr2(5) = 12 *)
  inject_Z (osc_tr2 5) - traceN 5 (matN_pow 5 (tridiag_box 5) 2) == 12.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  PILLAR 4: DISCRIMINANT SEPARATION                                   *)
(* ================================================================== *)

Theorem pillar_discriminant_gap :
  (* Box disc at K=4: 22 *)
  box_disc_K4 == 22 /\
  (* Osc disc at K=4: 92 *)
  osc_disc_K4 == 92 /\
  (* Gap: 70 *)
  osc_disc_K4 - box_disc_K4 == 70.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  PILLAR 5: UNCERTAINTY IS STATE-DEPENDENT                            *)
(* ================================================================== *)

Theorem pillar_uncertainty :
  (* K=2 uniform: standard 1/2 *)
  uncertainty_bound_K2 == (1#2) /\
  (* K=3 uniform: enhanced 2/3 *)
  uncertainty_bound_K3 == (2#3) /\
  (* Exceeds standard by 1/6 *)
  uncertainty_bound_K3 - (1#2) == (1#6) /\
  (* Localized state: zero *)
  Qabs comm_exp_K3_localized / 2 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  GRAND UNIFIED THEOREM                                               *)
(* ================================================================== *)

Theorem heisenberg_matrices_grand_synthesis :
  (* 1. [X,P] = -Laplacian *)
  XP_comm 4 0 1 == -(1) /\
  XP_comm 4 2 2 == 0 /\
  (* 2. Error grows: 7 < 10 *)
  error_norm_sq 3 < error_norm_sq 4 /\
  (* 3. Oscillator traces: K(K-1) *)
  osc_tr2 5 = 20%Z /\
  osc_tr4 5 = 140%Z /\
  (* 4. Disc separation: 92 - 22 = 70 *)
  osc_disc_K4 - box_disc_K4 == 70 /\
  (* 5. Uncertainty exceeds standard *)
  (1#2) < uncertainty_bound_K3 /\
  (* 6. State dependence *)
  comm_exp_K3_localized == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem heisenberg_state_dependence :
  ~(comm_exp_K3 == comm_exp_K3_localized).
Proof.
  intro H. vm_compute in H. discriminate.
Qed.
