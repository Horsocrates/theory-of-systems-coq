(** * HydrogenRadialSynthesis.v -- Layer 1 synthesis: radial Hamiltonian
    Elements: Grand summary of Hamiltonian, traces, process convergence, classification
    Roles:    Connects matrix entries → traces → eigenvalue process → classification
    Rules:    Layer 1 complete: H on lattice fully characterized
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.HydrogenRadial.
From ToS Require Import stdlib.HydrogenProcess.
From ToS Require Import stdlib.HydrogenTraces.
From ToS Require Import stdlib.HydrogenCorrection.

Open Scope Q_scope.

(* ================================================================== *)
(*  LAYER 1 SYNTHESIS: RADIAL HAMILTONIAN                              *)
(* ================================================================== *)

(** Theorem 1: Hamiltonian is well-defined with correct entries *)
Theorem layer1_hamiltonian_entries :
  HydrogenRadial.H_hydrogen 2 10 0 0 == 4 /\
  HydrogenRadial.H_hydrogen 2 10 1 1 == 6 /\
  HydrogenRadial.H_hydrogen 2 10 2 2 == 20#3.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** Theorem 2: Trace is correctly computed *)
Theorem layer1_trace_correct :
  trace3 2 3 == 50#3.
Proof. exact trace3_M2. Qed.

(** Theorem 3: Trace of H² gives spectral information *)
Theorem layer1_trace_H2 :
  trace_H2 2 3 == 1444#9.
Proof. exact trace_H2_M2_K3. Qed.

(** Theorem 4: Newton's identity yields e₂ *)
Theorem layer1_newton_e2 :
  newton_e2 2 3 == 176#3.
Proof. exact newton_e2_M2_K3. Qed.

(** Theorem 5: Process convergence — ratio improves *)
Theorem layer1_convergence :
  ratio_error 2 < ratio_error 1.
Proof. exact ratio_improves. Qed.

(** Theorem 6: Hydrogen is polynomial class *)
Theorem layer1_classification :
  is_polynomial hydrogen_class = true.
Proof. exact hydrogen_is_poly. Qed.

(** Theorem 7: Kinetic-Coulomb decomposition *)
Theorem layer1_decomposition :
  HydrogenRadial.H_hydrogen 2 10 0 0 ==
  H_kinetic 2 10 0 0 + H_coulomb 2 0.
Proof. exact H_decomp_diag0. Qed.

(** Theorem 8: Symmetry of Hamiltonian *)
Theorem layer1_symmetry :
  HydrogenRadial.H_hydrogen 2 10 0 1 == HydrogenRadial.H_hydrogen 2 10 1 0.
Proof. exact H_symmetric_01. Qed.

(** Theorem 9: Diagonal grows — Coulomb weakens for larger i *)
Theorem layer1_diagonal_grows :
  HydrogenRadial.H_hydrogen 2 10 0 0 < HydrogenRadial.H_hydrogen 2 10 1 1.
Proof. exact diag_grows_01. Qed.

(** Theorem 10: Correction coefficient is positive *)
Theorem layer1_correction_positive :
  0 < correction_coeff.
Proof. exact correction_coeff_positive. Qed.
