(** * FiniteSizeOscZ.v — Oscillator Partition Function as Finite Process
    Elements: Geometric partition Z(K), exp approximation, correction terms
    Roles:    Connect oscillator Z to finite-size convergence rate
    Rules:    Z(K) = (1 - e^{-K}) / (1 - e^{-1}), correction ~ e^{-K}
    Status:   Stdlib
    STATUS: 11 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  EXPONENTIAL APPROXIMATION                                          *)
(*  exp(-1) ≈ 24/65 ≈ 0.369...  (actual 0.3679...)                   *)
(* ================================================================== *)

Definition exp_neg1 : Q := 24#65.

Fixpoint qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => x * qpow x k
  end.

(* ================================================================== *)
(*  OSCILLATOR PARTITION FUNCTION                                      *)
(*  Z(K) = (1 - exp_neg1^K) / (1 - exp_neg1)                         *)
(* ================================================================== *)

Definition osc_Z (K : nat) : Q :=
  (1 - qpow exp_neg1 K) / (1 - exp_neg1).

Lemma osc_Z_1 : osc_Z 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma osc_Z_2 : osc_Z 2 == 237185#173225.
Proof. vm_compute. reflexivity. Qed.

Lemma osc_Z_3_val : osc_Z 3 == 16952065#11259625.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FINITE-SIZE CORRECTION                                             *)
(*  correction(K) = exp_neg1^K * (65/41)                              *)
(* ================================================================== *)

Definition osc_correction (K : nat) : Q :=
  qpow exp_neg1 K * (65#41).

Lemma correction_K1 : osc_correction 1 == 1560#2665.
Proof. vm_compute. reflexivity. Qed.

Lemma correction_K2 : osc_correction 2 == 37440#173225.
Proof. vm_compute. reflexivity. Qed.

Lemma correction_K3 : osc_correction 3 == 898560#11259625.
Proof. vm_compute. reflexivity. Qed.

Lemma correction_K5_val : osc_correction 5 == 517570560#47571915625.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONVERGENCE RATE COMPARISON                                        *)
(*  Ising rate ≈ 289/384 ≈ 0.753, Oscillator rate = 24/65 ≈ 0.369   *)
(*  Oscillator converges faster!                                       *)
(* ================================================================== *)

Definition ising_rate : Q := 289#384.
Definition osc_rate : Q := 24#65.

Lemma osc_faster_than_ising : osc_rate < ising_rate.
Proof. unfold osc_rate, ising_rate. lra. Qed.

Lemma rate_K2_comparison :
  qpow osc_rate 2 < qpow ising_rate 2.
Proof. simpl. unfold osc_rate, ising_rate. lra. Qed.

Lemma osc_rate_positive : 0 < osc_rate.
Proof. unfold osc_rate. lra. Qed.

Theorem finite_size_osc_synthesis :
  osc_Z 1 == 1 /\
  osc_rate < ising_rate /\
  0 < osc_rate.
Proof.
  split; [exact osc_Z_1|].
  split; [exact osc_faster_than_ising|].
  exact osc_rate_positive.
Qed.
