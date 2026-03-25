(** * SlaterLithium.v — Lithium Atom on Discrete Lattice
    Elements: Z=3 nuclear, 1s and 2s orbital energies, Koopmans IP
    Roles:    Compute Li electronic structure via STO lattice (1s^2 2s config)
    Rules:    E_1s(Z=3) < E_2s(Z=3) < 0; IP = -E_2s > 0; Aufbau: 1s fills first
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.

From ToS Require Import stdlib.SlaterBasis.
From ToS Require Import stdlib.SlaterOverlap.
From ToS Require Import stdlib.SlaterKinetic.
From ToS Require Import stdlib.SlaterNuclear.

(* ================================================================== *)
(*  LITHIUM 1s ORBITAL ENERGY: F_1s(Z=3) / S_11                       *)
(* ================================================================== *)

Definition F_1s_Li : Q :=
  T_11_val + nuclear_element 3 (sto_1s 1 3) (sto_1s 1 3) 3.

Definition E_1s_Li : Q := F_1s_Li / (SlaterOverlap.S_11_raw / 3).

Lemma E_1s_Li_neg : E_1s_Li < 0.
Proof.
  unfold E_1s_Li, F_1s_Li, T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  LITHIUM 2s ORBITAL ENERGY: F_2s(Z=3) / S_22                       *)
(* ================================================================== *)

Definition F_2s_Li : Q :=
  T_22_val + nuclear_element 3 (sto_2s 1 3) (sto_2s 1 3) 3.

Definition E_2s_Li : Q := F_2s_Li / (SlaterOverlap.S_22_raw / 3).

Lemma E_2s_Li_neg : E_2s_Li < 0.
Proof.
  unfold E_2s_Li, F_2s_Li, T_22_val,
         SlaterOverlap.S_22_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  AUFBAU: 1s orbital is more deeply bound than 2s                    *)
(* ================================================================== *)

Lemma aufbau_1s_before_2s : E_1s_Li < E_2s_Li.
Proof.
  unfold E_1s_Li, E_2s_Li, F_1s_Li, F_2s_Li, T_11_val, T_22_val,
         SlaterOverlap.S_11_raw, SlaterOverlap.S_22_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  KOOPMANS THEOREM: IP = -E_2s > 0                                   *)
(* ================================================================== *)

Definition IP_Li : Q := -(E_2s_Li).

Lemma IP_Li_pos : 0 < IP_Li.
Proof.
  unfold IP_Li, E_2s_Li, F_2s_Li, T_22_val,
         SlaterOverlap.S_22_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Li 1s DEEPER THAN He 1s (Z=3 vs Z=2)                              *)
(* ================================================================== *)

Lemma Li_1s_deeper_than_He :
  E_1s_Li < (T_11_val + nuclear_element 2 (sto_1s 1 3) (sto_1s 1 3) 3) /
            (SlaterOverlap.S_11_raw / 3).
Proof.
  unfold E_1s_Li, F_1s_Li, T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  TOTAL Li ENERGY ESTIMATE: E = 2·E_1s + E_2s (no e-e repulsion)    *)
(* ================================================================== *)

Definition E_Li_total : Q := 2 * E_1s_Li + E_2s_Li.

Lemma E_Li_total_neg : E_Li_total < 0.
Proof.
  unfold E_Li_total, E_1s_Li, E_2s_Li, F_1s_Li, F_2s_Li,
         T_11_val, T_22_val,
         SlaterOverlap.S_11_raw, SlaterOverlap.S_22_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Li MORE BOUND THAN He (more electrons, higher Z)                   *)
(* ================================================================== *)

Lemma Li_more_bound_than_He :
  E_Li_total < 2 * ((T_11_val + nuclear_element 2 (sto_1s 1 3) (sto_1s 1 3) 3) /
                     (SlaterOverlap.S_11_raw / 3)).
Proof.
  unfold E_Li_total, E_1s_Li, E_2s_Li, F_1s_Li, F_2s_Li,
         T_11_val, T_22_val,
         SlaterOverlap.S_11_raw, SlaterOverlap.S_22_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  E_1s BOUND: -3 < E_1s < 0                                         *)
(* ================================================================== *)

Lemma E_1s_Li_bound : -(3) < E_1s_Li.
Proof.
  unfold E_1s_Li, F_1s_Li, T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.
