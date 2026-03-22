(** * FiniteSizeIsing.v -- Finite-Size Corrections in 1D Ising Model
    Elements: ising_ratio (28/37), ising_correction, free_energy_correction
    Roles:    Exponential decay of finite-size corrections in transfer matrix
    Rules:    Correction = (lambda2/lambda1)^N, converges to 0 as N -> infinity
    Status:   Stdlib
    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
Open Scope Q_scope.

(* ================================================================== *)
(*  ISING RATIO: lambda2/lambda1 at beta=1                            *)
(*  lambda1 = 2*cosh(1) approx, lambda2 = 2*sinh(1) approx           *)
(*  Ratio approx 28/37 (from lattice eigenvalue computation)          *)
(* ================================================================== *)

Definition ising_ratio : Q := 28#37.

Lemma ising_ratio_positive : 0 < ising_ratio.
Proof. unfold ising_ratio. lra. Qed.

Lemma ising_ratio_lt_one : ising_ratio < 1.
Proof. unfold ising_ratio. lra. Qed.

(* ================================================================== *)
(*  ISING CORRECTION: (28/37)^N                                       *)
(* ================================================================== *)

Definition ising_correction (N : nat) : Q := Qpow ising_ratio N.

(** N=1: 28/37 *)
Lemma correction_N1 : ising_correction 1 == 28#37.
Proof. vm_compute. reflexivity. Qed.

(** N=2: (28/37)^2 = 784/1369 *)
Lemma correction_N2 : ising_correction 2 == 784#1369.
Proof. vm_compute. reflexivity. Qed.

(** N=3: (28/37)^3 = 21952/50653 *)
Lemma correction_N3 : ising_correction 3 == 21952#50653.
Proof. vm_compute. reflexivity. Qed.

(** N=4: (28/37)^4 = 614656/1874161 *)
Lemma correction_N4 : ising_correction 4 == 614656#1874161.
Proof. vm_compute. reflexivity. Qed.

(** N=3 correction < 1/2 (about 43%) *)
Lemma correction_N3_lt_half : ising_correction 3 < 1#2.
Proof.
  unfold ising_correction, ising_ratio, Qlt. vm_compute. reflexivity.
Qed.

(** N=4 correction < 1/3 (about 33%) *)
Lemma correction_N4_lt_third : ising_correction 4 < 1#3.
Proof.
  unfold ising_correction, ising_ratio, Qlt. vm_compute. reflexivity.
Qed.

(** Corrections decrease: N=2 < N=1 *)
Lemma correction_decreasing_1_2 : ising_correction 2 < ising_correction 1.
Proof.
  unfold ising_correction, ising_ratio, Qlt. vm_compute. reflexivity.
Qed.

(** Corrections decrease: N=3 < N=2 *)
Lemma correction_decreasing_2_3 : ising_correction 3 < ising_correction 2.
Proof.
  unfold ising_correction, ising_ratio, Qlt. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  FREE ENERGY CORRECTION: -r^N + r^(2N)/2                           *)
(*  Leading finite-size correction to free energy per site             *)
(* ================================================================== *)

Definition free_energy_correction (N : nat) : Q :=
  -(Qpow ising_ratio N) + Qpow ising_ratio N * Qpow ising_ratio N / 2.

(** N=1: -(28/37) + (28/37)^2/2 = -(28/37) + 784/1369/2 = -(28/37) + 392/1369 *)
Lemma free_energy_N1 : free_energy_correction 1 ==
  -(28#37) + (784#1369) / 2.
Proof. unfold free_energy_correction, ising_ratio. vm_compute. reflexivity. Qed.

(** Free energy correction is negative for N=1 *)
Lemma free_energy_N1_negative : free_energy_correction 1 < 0.
Proof.
  unfold free_energy_correction, ising_ratio, Qlt. vm_compute. reflexivity.
Qed.

(** Free energy correction is negative for N=2 *)
Lemma free_energy_N2_negative : free_energy_correction 2 < 0.
Proof.
  unfold free_energy_correction, ising_ratio, Qlt. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem finite_size_ising_synthesis :
  ising_ratio < 1 /\
  ising_correction 3 == 21952#50653 /\
  ising_correction 3 < 1#2 /\
  ising_correction 4 < 1#3 /\
  ising_correction 2 < ising_correction 1 /\
  free_energy_correction 1 < 0.
Proof.
  split; [exact ising_ratio_lt_one|].
  split; [exact correction_N3|].
  split; [exact correction_N3_lt_half|].
  split; [exact correction_N4_lt_third|].
  split; [exact correction_decreasing_1_2|].
  exact free_energy_N1_negative.
Qed.
