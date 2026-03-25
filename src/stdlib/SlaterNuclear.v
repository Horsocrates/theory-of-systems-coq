(** * SlaterNuclear.v — Nuclear Attraction Integrals for Slater Basis
    Elements: Nuclear potential -Z/r, attraction integral V_ab, lattice Coulomb
    Roles:    Compute ⟨φ_a|-Z/r|φ_b⟩ on discrete lattice; always negative
    Rules:    V_ab = -(Z/M) Σ_i φ_a(i)·φ_b(i)/(i+1); V_11 < 0
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import stdlib.SlaterBasis.

(* ================================================================== *)
(*  NUCLEAR ATTRACTION: V_ab = -(Z/M) Σ_i φ_a(i)·φ_b(i)/(i+1)       *)
(*  On lattice, r_i = (i+1)/M, so 1/r_i = M/(i+1)                    *)
(*  V_ab = -(Z) Σ_i φ_a(i)·φ_b(i)/(i+1) / M                         *)
(* ================================================================== *)

Fixpoint sum_Q (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => sum_Q f k + f k
  end.

Definition nuclear_element (Z_nuc : Q) (phi_a phi_b : nat -> Q) (M : nat) : Q :=
  sum_Q (fun i =>
    (- Z_nuc) * phi_a i * phi_b i / inject_Z (Z.of_nat (S i)))
    M / inject_Z (Z.of_nat M).

(* ================================================================== *)
(*  CONCRETE: V_11 for hydrogen (Z=1), ζ=1, M=3                       *)
(*  V_11 = -(1/3)[φ₀²/1 + φ₁²/2 + φ₂²/3]                            *)
(* ================================================================== *)

Definition V_11_val : Q := nuclear_element 1 (sto_1s 1 3) (sto_1s 1 3) 3.

Lemma V_11_neg : V_11_val < 0.
Proof.
  unfold V_11_val, nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  V_22 for 2s orbital: also negative                                 *)
(* ================================================================== *)

Definition V_22_val : Q := nuclear_element 1 (sto_2s 1 3) (sto_2s 1 3) 3.

Lemma V_22_neg : V_22_val < 0.
Proof.
  unfold V_22_val, nuclear_element, sum_Q, sto_2s, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  |V_11| > |V_22|: 1s closer to nucleus, stronger attraction        *)
(* ================================================================== *)

Lemma V_11_stronger : V_11_val < V_22_val.
Proof.
  unfold V_11_val, V_22_val, nuclear_element, sum_Q, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CROSS NUCLEAR V_12                                                 *)
(* ================================================================== *)

Definition V_12_val : Q := nuclear_element 1 (sto_1s 1 3) (sto_2s 1 3) 3.

Lemma V_12_neg : V_12_val < 0.
Proof.
  unfold V_12_val, nuclear_element, sum_Q, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  HELIUM (Z=2): nuclear attraction twice as strong                   *)
(* ================================================================== *)

Definition V_11_He : Q := nuclear_element 2 (sto_1s 1 3) (sto_1s 1 3) 3.

Lemma V_11_He_neg : V_11_He < 0.
Proof.
  unfold V_11_He, nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

Lemma V_He_stronger : V_11_He < V_11_val.
Proof.
  unfold V_11_He, V_11_val, nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  LITHIUM (Z=3): nuclear attraction three times as strong            *)
(* ================================================================== *)

Definition V_11_Li : Q := nuclear_element 3 (sto_1s 1 3) (sto_1s 1 3) 3.

Lemma V_Li_stronger : V_11_Li < V_11_He.
Proof.
  unfold V_11_Li, V_11_He, nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SCALING: V(Z=2) == 2 * V(Z=1)                                     *)
(* ================================================================== *)

Lemma V_He_double : V_11_He == 2 * V_11_val.
Proof.
  unfold V_11_He, V_11_val, nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SCALING: V(Z=3) == 3 * V(Z=1)                                     *)
(* ================================================================== *)

Lemma V_Li_triple : V_11_Li == 3 * V_11_val.
Proof.
  unfold V_11_Li, V_11_val, nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  NUCLEAR FOR ZERO CHARGE: V(Z=0) = 0                                *)
(* ================================================================== *)

Lemma nuclear_Z0 : nuclear_element 0 (sto_1s 1 3) (sto_1s 1 3) 3 == 0.
Proof.
  unfold nuclear_element, sum_Q, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.
