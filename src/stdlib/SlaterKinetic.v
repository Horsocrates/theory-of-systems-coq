(** * SlaterKinetic.v — Kinetic Energy Matrix Elements for Slater Basis
    Elements: Discrete gradient, kinetic integral T_ab, kinetic energy
    Roles:    Compute ⟨φ_a|-½∇²|φ_b⟩ via finite differences on lattice
    Rules:    T_ab = (M/2) Σ_i (Δφ_a)(i)·(Δφ_b)(i); Δφ(i) = φ(i+1) - φ(i);
              T_11 > 0 (kinetic energy non-negative)
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import stdlib.SlaterBasis.

(* ================================================================== *)
(*  DISCRETE GRADIENT: Δφ(i) = φ(i+1) - φ(i)                        *)
(* ================================================================== *)

Definition grad (phi : nat -> Q) (i : nat) : Q := phi (S i) - phi i.

(* ================================================================== *)
(*  KINETIC ENERGY: gradient form                                      *)
(*  T_ab = (M/2) Σ_{i=0}^{M-2} (Δφ_a)(i) · (Δφ_b)(i)               *)
(*  This is the integration-by-parts form of -½∇²                     *)
(* ================================================================== *)

Fixpoint sum_Q (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => sum_Q f k + f k
  end.

Definition kinetic_element (phi_a phi_b : nat -> Q) (M : nat) : Q :=
  inject_Z (Z.of_nat M) / 2 *
  sum_Q (fun i => grad phi_a i * grad phi_b i) (pred M).

(* ================================================================== *)
(*  CONCRETE GRADIENT VALUES for 1s (ζ=1, M=3)                        *)
(*  Δφ(0) = φ(1) - φ(0) = 19/37 - 91/127                             *)
(*  Δφ(1) = φ(2) - φ(1) = 7/19 - 19/37                               *)
(* ================================================================== *)

Lemma grad_1s_0 : grad (sto_1s 1 3) O == (19#37) - (91#127).
Proof. unfold grad, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma grad_1s_1 : grad (sto_1s 1 3) (S O) == (7#19) - (19#37).
Proof. unfold grad, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GRADIENTS ARE NEGATIVE (wavefunction decays)                       *)
(* ================================================================== *)

Lemma grad_1s_0_neg : grad (sto_1s 1 3) O < 0.
Proof. unfold grad, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma grad_1s_1_neg : grad (sto_1s 1 3) (S O) < 0.
Proof. unfold grad, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  KINETIC ENERGY T_11: strictly positive                             *)
(*  T_11 = (3/2)(Δφ₀² + Δφ₁²) > 0                                    *)
(* ================================================================== *)

Definition T_11_val : Q := kinetic_element (sto_1s 1 3) (sto_1s 1 3) 3.

Lemma T_11_pos : 0 < T_11_val.
Proof. unfold T_11_val, kinetic_element, sum_Q, grad, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  KINETIC ENERGY T_22 for 2s: also positive                          *)
(* ================================================================== *)

Definition T_22_val : Q := kinetic_element (sto_2s 1 3) (sto_2s 1 3) 3.

Lemma T_22_pos : 0 < T_22_val.
Proof. unfold T_22_val, kinetic_element, sum_Q, grad, sto_2s, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CROSS KINETIC T_12                                                 *)
(* ================================================================== *)

Definition T_12_val : Q := kinetic_element (sto_1s 1 3) (sto_2s 1 3) 3.

Lemma T_12_neg : T_12_val < 0.
Proof. unfold T_12_val, kinetic_element, sum_Q, grad, sto_2s, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  T_11 > T_22 (1s has larger kinetic energy than 2s)                 *)
(* ================================================================== *)

Lemma T_11_gt_T_22 : T_22_val < T_11_val.
Proof. unfold T_11_val, T_22_val, kinetic_element, sum_Q, grad, sto_1s, sto_2s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  KINETIC SYMMETRY: T_ab = T_ba                                     *)
(* ================================================================== *)

Lemma kinetic_symmetric : forall phi_a phi_b M,
  kinetic_element phi_a phi_b M == kinetic_element phi_b phi_a M.
Proof.
  intros. unfold kinetic_element.
  apply Qmult_comp; [reflexivity|].
  induction (pred M) as [|k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. unfold grad. ring.
Qed.

(* ================================================================== *)
(*  KINETIC ENERGY AT M=1: trivially zero (no gradient)                *)
(* ================================================================== *)

Lemma kinetic_M1 : forall phi_a phi_b,
  kinetic_element phi_a phi_b (S O) == 0.
Proof.
  intros. unfold kinetic_element. simpl. ring.
Qed.

(* ================================================================== *)
(*  GRADIENT SQUARED is non-negative at each site                      *)
(* ================================================================== *)

Lemma grad_sq_nonneg : forall phi i, 0 <= grad phi i * grad phi i.
Proof.
  intros.
  set (g := grad phi i).
  destruct (Qlt_le_dec g 0) as [Hn|Hp].
  - assert (Hnn : 0 < (-g)). { lra. }
    assert (Heq : g * g == (-g) * (-g)). { ring. }
    rewrite Heq.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(* ================================================================== *)
(*  |T_12| < T_11 (Cauchy-Schwarz for kinetic)                        *)
(* ================================================================== *)

Lemma T_12_sq_lt_T_11_T_22 : T_12_val * T_12_val < T_11_val * T_22_val.
Proof.
  unfold T_12_val, T_11_val, T_22_val, kinetic_element, sum_Q, grad,
         sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.
