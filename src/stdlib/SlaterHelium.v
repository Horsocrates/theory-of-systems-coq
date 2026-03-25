(** * SlaterHelium.v — Helium Atom Ground State on Discrete Lattice
    Elements: Z=2 nuclear attraction, electron repulsion J_11, total energy
    Roles:    Compute He ground state energy via STO lattice with e-e repulsion
    Rules:    E_He = 2·E_1e(Z=2) + J_11; J_11 > 0 (repulsion); E_He < 0
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import stdlib.SlaterBasis.
From ToS Require Import stdlib.SlaterOverlap.
From ToS Require Import stdlib.SlaterKinetic.
From ToS Require Import stdlib.SlaterNuclear.

(* ================================================================== *)
(*  HELIUM ONE-ELECTRON FOCK: F_He = T + V(Z=2)                       *)
(* ================================================================== *)

Definition F_11_He : Q :=
  T_11_val + nuclear_element 2 (sto_1s 1 3) (sto_1s 1 3) 3.

Lemma F_11_He_neg : F_11_He < 0.
Proof.
  unfold F_11_He, T_11_val, nuclear_element,
         kinetic_element, SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  ONE-ELECTRON ENERGY: E_1e = F_11_He / S_11                        *)
(* ================================================================== *)

Definition E_1e_He : Q := F_11_He / (SlaterOverlap.S_11_raw / 3).

Lemma E_1e_He_neg : E_1e_He < 0.
Proof.
  unfold E_1e_He, F_11_He, T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  He is more deeply bound than H (Z=2 vs Z=1)                       *)
(* ================================================================== *)

(* He 1e energy more negative than H 1e energy *)
(* H energy = (T_11 + V(Z=1)) / S_11 *)
Definition E_1e_H : Q :=
  (T_11_val + nuclear_element 1 (sto_1s 1 3) (sto_1s 1 3) 3) /
  (SlaterOverlap.S_11_raw / 3).

Lemma He_deeper_than_H : E_1e_He < E_1e_H.
Proof.
  unfold E_1e_He, E_1e_H, F_11_He,
         T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  COULOMB REPULSION: J_11 = Σ_{i,j} φ(i)²·φ(j)² / (M·max(i+1,j+1)) *)
(*  Electron-electron repulsion on lattice                             *)
(* ================================================================== *)

Definition J_11_raw : Q :=
  let phi := sto_1s 1 3 in
  let p0 := phi O in let p1 := phi (S O) in let p2 := phi (S (S O)) in
  (* i=0,j=0: /1; i=0,j=1: /2; i=0,j=2: /3 *)
  (* i=1,j=0: /2; i=1,j=1: /2; i=1,j=2: /3 *)
  (* i=2,j=0: /3; i=2,j=1: /3; i=2,j=2: /3 *)
  (p0*p0*p0*p0 / 1 +
   p0*p0*p1*p1 / 2 +
   p0*p0*p2*p2 / 3 +
   p1*p1*p0*p0 / 2 +
   p1*p1*p1*p1 / 2 +
   p1*p1*p2*p2 / 3 +
   p2*p2*p0*p0 / 3 +
   p2*p2*p1*p1 / 3 +
   p2*p2*p2*p2 / 3) / 3.

Lemma J_11_pos : 0 < J_11_raw.
Proof.
  unfold J_11_raw, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  TOTAL He ENERGY: E = 2·E_1e + J_11                                 *)
(*  (Hartree approximation: no exchange, no correlation)               *)
(* ================================================================== *)

Definition E_He_total : Q := 2 * E_1e_He + J_11_raw.

Lemma E_He_total_neg : E_He_total < 0.
Proof.
  unfold E_He_total, E_1e_He, J_11_raw, F_11_He,
         T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  REPULSION IS SMALL: J_11 < |2·E_1e| (atom is bound)               *)
(* ================================================================== *)

Lemma repulsion_small : J_11_raw < -(2 * E_1e_He).
Proof.
  unfold J_11_raw, E_1e_He, F_11_He, T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  He ENERGY BOUND: E > -4 (not over-bound)                           *)
(* ================================================================== *)

Lemma E_He_bound : -(4) < E_He_total.
Proof.
  unfold E_He_total, E_1e_He, J_11_raw, F_11_He,
         T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  1s^2 CONFIGURATION: both electrons see same one-electron energy    *)
(* ================================================================== *)

Lemma he_config_1s2 :
  E_He_total == E_1e_He + E_1e_He + J_11_raw.
Proof.
  unfold E_He_total. ring.
Qed.

(* ================================================================== *)
(*  IONIZATION ENERGY: IE = E(He+) - E(He) = -E_1e - J_11             *)
(*  IE > 0 (energy required to remove electron)                       *)
(* ================================================================== *)

Definition IE_He : Q := -(E_1e_He) - J_11_raw.

Lemma IE_He_pos : 0 < IE_He.
Proof.
  unfold IE_He, E_1e_He, J_11_raw, F_11_He,
         T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  COULOMB REPULSION IS POSITIVE: sum of positive terms               *)
(* ================================================================== *)

(* ================================================================== *)
(*  He TOTAL ENERGY DECOMPOSITION CHECK                                *)
(* ================================================================== *)

Lemma E_He_H_comparison : E_1e_H < 0.
Proof.
  unfold E_1e_H,
         T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.
