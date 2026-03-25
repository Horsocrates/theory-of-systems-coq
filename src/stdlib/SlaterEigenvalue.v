(** * SlaterEigenvalue.v — Eigenvalue Computation for Hydrogen STO
    Elements: Generalized eigenvalue E = F/S, 1-basis energy, secular equation
    Roles:    Solve F·c = E·S·c for single-basis and two-basis cases
    Rules:    E_1basis = F_11/S_11; E < 0 ↔ bound state; -1 < E < 0
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.

From ToS Require Import stdlib.SlaterBasis.
From ToS Require Import stdlib.SlaterOverlap.
From ToS Require Import stdlib.SlaterKinetic.
From ToS Require Import stdlib.SlaterNuclear.
From ToS Require Import stdlib.SlaterMatrix.

(* ================================================================== *)
(*  1-BASIS EIGENVALUE: E = F_11 / S_11                                *)
(*  For single STO, generalized eigenvalue reduces to ratio            *)
(* ================================================================== *)

Definition E_1basis_M3 : Q :=
  F_11_val / (SlaterOverlap.S_11_raw / 3).

(* Equivalently: E = (T_11 + V_11) * 3 / S_11_raw *)

(* ================================================================== *)
(*  E_1basis IS NEGATIVE (bound state)                                 *)
(* ================================================================== *)

Lemma E_1basis_neg : E_1basis_M3 < 0.
Proof.
  unfold E_1basis_M3, F_11_val, fock_element,
         SlaterOverlap.S_11_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  E_1basis > -1 (not over-bound)                                     *)
(* ================================================================== *)

Lemma E_1basis_gt_m1 : -(1) < E_1basis_M3.
Proof.
  unfold E_1basis_M3, F_11_val, fock_element,
         SlaterOverlap.S_11_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  E_1basis > -1/2 (above exact hydrogen ground state)                *)
(*  Expected: Padé lattice with finite M over-estimates (variational)  *)
(* ================================================================== *)

Lemma E_1basis_above_exact : -(1#2) < E_1basis_M3.
Proof.
  unfold E_1basis_M3, F_11_val, fock_element,
         SlaterOverlap.S_11_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SECULAR EQUATION for 2-basis: det(F - ES) = 0                     *)
(*  (F_11 - E·S_11)(F_22 - E·S_22) - (F_12 - E·S_12)² = 0          *)
(*  For demonstration: evaluate secular determinant at trial E         *)
(* ================================================================== *)

Definition secular_det (E : Q) : Q :=
  (F_11_val - E * SlaterOverlap.S_11_raw / 3) *
  (F_22_val - E * SlaterOverlap.S_22_raw / 3) -
  (F_12_val - E * SlaterOverlap.S_12_raw / 3) *
  (F_12_val - E * SlaterOverlap.S_12_raw / 3).

(* At E=0: secular det < 0 *)
Lemma secular_at_0_neg : secular_det 0 < 0.
Proof.
  unfold secular_det, F_11_val, F_12_val, F_22_val, fock_element,
         SlaterOverlap.S_11_raw, SlaterOverlap.S_12_raw, SlaterOverlap.S_22_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* At E=-1: secular det > 0 (sign change → root exists in (-1, 0)) *)
Lemma secular_at_m1_pos : 0 < secular_det (-(1)).
Proof.
  unfold secular_det, F_11_val, F_12_val, F_22_val, fock_element,
         SlaterOverlap.S_11_raw, SlaterOverlap.S_12_raw, SlaterOverlap.S_22_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  ROOT EXISTENCE: secular det changes sign → eigenvalue exists       *)
(* ================================================================== *)

Lemma eigenvalue_exists_in_interval :
  0 < secular_det (-(1)) /\ secular_det 0 < 0.
Proof.
  split.
  - exact secular_at_m1_pos.
  - exact secular_at_0_neg.
Qed.

(* ================================================================== *)
(*  2-BASIS ENERGY: secular_det(E_1basis) < 0                          *)
(*  This means 2-basis root is more negative than 1-basis energy       *)
(* ================================================================== *)

Lemma two_basis_improves : secular_det E_1basis_M3 < 0.
Proof.
  unfold secular_det, E_1basis_M3,
         F_11_val, F_12_val, F_22_val, fock_element,
         SlaterOverlap.S_11_raw, SlaterOverlap.S_12_raw, SlaterOverlap.S_22_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  F_11_val CONSISTENCY: matches energy_1basis from SlaterMatrix      *)
(* ================================================================== *)

Lemma energy_consistency :
  E_1basis_M3 == energy_1basis.
Proof.
  unfold E_1basis_M3, energy_1basis, F_11_val, fock_element,
         SlaterOverlap.S_11_raw,
         kinetic_element, nuclear_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  VARIATIONAL BOUND: E_1basis >= E_exact for any basis               *)
(*  (stated as: our computed energy is above -1/2)                     *)
(* ================================================================== *)

Lemma variational_principle_concrete : -(1#2) < E_1basis_M3.
Proof. exact E_1basis_above_exact. Qed.

(* ================================================================== *)
(*  ENERGY IN RANGE: -1/2 < E < 0 (correct qualitative behavior)      *)
(* ================================================================== *)

Lemma energy_in_range : -(1#2) < E_1basis_M3 /\ E_1basis_M3 < 0.
Proof. split; [exact E_1basis_above_exact | exact E_1basis_neg]. Qed.
