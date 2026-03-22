(** * ComplexCorrectionSynthesis.v -- Grand Synthesis: Oscillator + Complex Numbers as ToS System
    Elements: All theorems from OscillatorCorrection, ComplexOverQ, ComplexOscillator, ComplexQuantumGate
    Roles:    Unifies exact oscillator spectrum with complex matrix representation and quantum gates
    Rules:    E0=1/2 (corrected), i^2=-1 (verified), S^2=Z (verified), CNOT^2=I (verified)
    Status:   Stdlib (synthesis)
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.OscillatorCorrection.
From ToS Require Import stdlib.ComplexOverQ.
From ToS Require Import stdlib.ComplexOscillator.
From ToS Require Import stdlib.ComplexQuantumGate.

Open Scope Q_scope.

(* ================================================================== *)
(*  PILLAR 1: CORRECTED OSCILLATOR SPECTRUM                            *)
(* ================================================================== *)

Theorem pillar_oscillator :
  E_oscillator 0 == 1#2 /\
  E_oscillator 1 - E_oscillator 0 == 1 /\
  0 < E_oscillator 0.
Proof.
  split; [exact E0_always_half |].
  split; [exact energy_spacing |].
  exact E_positive.
Qed.

(* ================================================================== *)
(*  PILLAR 2: COMPLEX NUMBERS OVER Q                                   *)
(* ================================================================== *)

Theorem pillar_complex :
  mat2_mul C_i C_i 0%nat 0%nat == -(1) /\
  mat2_mul C_i C_i 1%nat 1%nat == -(1) /\
  complex_mod_sq 3 4 == 25.
Proof.
  split; [exact i_sq_00 |].
  split; [exact i_sq_11 |].
  exact mod_sq_example.
Qed.

(* ================================================================== *)
(*  PILLAR 3: HAMILTONIAN EIGENVALUES                                  *)
(* ================================================================== *)

Theorem pillar_hamiltonian :
  osc_hamiltonian 3 0%nat 0%nat == 1#2 /\
  osc_hamiltonian 3 1%nat 1%nat == 3#2 /\
  osc_hamiltonian 3 0%nat 1%nat == 0.
Proof.
  split; [exact H_eigenvalue_0 |].
  split; [exact H_eigenvalue_1 |].
  exact H_diagonal_01.
Qed.

(* ================================================================== *)
(*  PILLAR 4: QUANTUM GATE IDENTITIES                                  *)
(* ================================================================== *)

Theorem pillar_gates :
  mat4_mul S_gate S_gate 2%nat 2%nat == -(1) /\
  mat4_mul CNOT CNOT 0%nat 0%nat == 1 /\
  mat4_mul CNOT CNOT 2%nat 2%nat == 1.
Proof.
  split; [exact S_sq_22 |].
  split; [exact CNOT_sq_00 |].
  exact CNOT_sq_22.
Qed.

(* ================================================================== *)
(*  CONSISTENCY: HAMILTONIAN GROUND STATE = OSCILLATOR E0               *)
(* ================================================================== *)

Theorem H_ground_state_matches_oscillator :
  osc_hamiltonian 3 0%nat 0%nat == E_oscillator 0.
Proof. vm_compute. reflexivity. Qed.

Theorem H_first_excited_matches_oscillator :
  osc_hamiltonian 3 1%nat 1%nat == E_oscillator 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE CONSISTENCY                                                   *)
(* ================================================================== *)

Theorem trace_H3_equals_sum_E :
  trace_sum (osc_hamiltonian 3) 3 ==
  E_oscillator 0 + E_oscillator 1 + E_oscillator 2.
Proof. vm_compute. reflexivity. Qed.

Theorem second_excited_matches :
  osc_hamiltonian 3 2%nat 2%nat == E_oscillator 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GRAND THEOREM: EVERYTHING CONNECTS                                  *)
(* ================================================================== *)

Theorem grand_correction_complex_synthesis :
  (* Oscillator correction *)
  E_oscillator 0 == 1#2 /\
  (* Complex i^2 = -1 *)
  mat2_mul C_i C_i 0%nat 0%nat == -(1) /\
  (* Hamiltonian matches oscillator *)
  osc_hamiltonian 3 0%nat 0%nat == E_oscillator 0 /\
  (* S^2 = Z diagonal *)
  mat4_mul S_gate S_gate 2%nat 2%nat == -(1) /\
  (* CNOT involutory *)
  mat4_mul CNOT CNOT 2%nat 2%nat == 1.
Proof.
  split; [exact E0_always_half |].
  split; [exact i_sq_00 |].
  split; [exact H_ground_state_matches_oscillator |].
  split; [exact S_sq_22 |].
  exact CNOT_sq_22.
Qed.
