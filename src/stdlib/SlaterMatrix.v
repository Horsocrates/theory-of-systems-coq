(** * SlaterMatrix.v — Fock Matrix for Hydrogen on Discrete Lattice
    Elements: Fock matrix F = T + V, matrix elements F_11, F_12, F_22
    Roles:    Assemble one-electron Hamiltonian from kinetic and nuclear integrals
    Rules:    F_ab = T_ab + V_ab; F_11 < 0 (bound state); F·c = E·S·c
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

(* ================================================================== *)
(*  FOCK MATRIX ELEMENT: F_ab = T_ab + V_ab                           *)
(*  For hydrogen (Z=1), no electron-electron repulsion                 *)
(* ================================================================== *)

Definition fock_element (phi_a phi_b : nat -> Q) (M : nat) : Q :=
  kinetic_element phi_a phi_b M + nuclear_element 1 phi_a phi_b M.

(* ================================================================== *)
(*  CONCRETE: F_11 for 1s, ζ=1, M=3                                   *)
(* ================================================================== *)

Definition F_11_val : Q := fock_element (sto_1s 1 3) (sto_1s 1 3) 3.

Lemma F_11_eq : F_11_val == T_11_val + V_11_val.
Proof.
  unfold F_11_val, fock_element, T_11_val, V_11_val.
  reflexivity.
Qed.

Lemma F_11_neg : F_11_val < 0.
Proof.
  unfold F_11_val, fock_element, kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  F_12: cross Fock element                                           *)
(* ================================================================== *)

Definition F_12_val : Q := fock_element (sto_1s 1 3) (sto_2s 1 3) 3.

Lemma F_12_neg : F_12_val < 0.
Proof.
  unfold F_12_val, fock_element, kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  F_22: 2s diagonal Fock element                                     *)
(* ================================================================== *)

Definition F_22_val : Q := fock_element (sto_2s 1 3) (sto_2s 1 3) 3.

Lemma F_22_neg : F_22_val < 0.
Proof.
  unfold F_22_val, fock_element, kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  |F_11| > |F_22|: 1s orbital is more deeply bound                  *)
(* ================================================================== *)

Lemma F_11_deeper : F_11_val < F_22_val.
Proof.
  unfold F_11_val, F_22_val, fock_element, kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  FOCK SYMMETRY: F_ab = F_ba                                         *)
(* ================================================================== *)

Lemma fock_symmetric : forall phi_a phi_b M,
  fock_element phi_a phi_b M == fock_element phi_b phi_a M.
Proof.
  intros. unfold fock_element.
  rewrite kinetic_symmetric.
  assert (Hn : nuclear_element 1 phi_a phi_b M == nuclear_element 1 phi_b phi_a M).
  {
    unfold nuclear_element, SlaterNuclear.sum_Q.
    apply Qdiv_comp; [|reflexivity].
    induction M as [|k IH].
    - simpl. reflexivity.
    - simpl. rewrite IH.
      assert (Hmul : -1 * phi_a k * phi_b k == -1 * phi_b k * phi_a k) by ring.
      rewrite Hmul. reflexivity.
  }
  rewrite Hn. reflexivity.
Qed.

(* ================================================================== *)
(*  VIRIAL-LIKE: |V_11| > T_11 (potential dominates for bound state)   *)
(* ================================================================== *)

Lemma potential_dominates : T_11_val < -(V_11_val).
Proof.
  unfold T_11_val, V_11_val, kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  GENERALIZED EIGENVALUE: F·c = E·S·c                                *)
(*  For single basis: E = F_11/S_11                                    *)
(* ================================================================== *)

Definition energy_1basis : Q := F_11_val / SlaterOverlap.S_11_raw * 3.

Lemma energy_1basis_neg : energy_1basis < 0.
Proof.
  unfold energy_1basis, F_11_val, fock_element,
         SlaterOverlap.S_11_raw,
         kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  ENERGY BOUND: E > -1 (not too negative for M=3 approximation)     *)
(* ================================================================== *)

Lemma energy_1basis_bound : -(1) < energy_1basis.
Proof.
  unfold energy_1basis, F_11_val, fock_element,
         SlaterOverlap.S_11_raw,
         kinetic_element, nuclear_element,
         sum_Q, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  FOCK ELEMENT DECOMPOSITION: explicit T+V split                     *)
(* ================================================================== *)

Lemma fock_decomposition : forall phi_a phi_b M,
  fock_element phi_a phi_b M ==
  kinetic_element phi_a phi_b M + nuclear_element 1 phi_a phi_b M.
Proof.
  intros. unfold fock_element. reflexivity.
Qed.
