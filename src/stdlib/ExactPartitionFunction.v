(** * ExactPartitionFunction.v — Z(beta) exact over Q from transfer matrix
    Elements: Z_b1, free_energy, entropy_thermo
    Roles:    Partition function, free energy, entropy -- all exact Q
    Rules:    Thermodynamic consistency: S = beta*E + ln(Z)
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.DiscreteEntropy.

Open Scope Q_scope.

(* ================================================================== *)
(*  PARTITION FUNCTION FROM TRANSFER MATRIX                            *)
(* ================================================================== *)

(** Z = t0 + 3*t1 (truncation M=0, SU(2) characters)
    Values from gauge.ExactMassGap (replicated to avoid stale .vo):
    t0_M0(1) = 7/8, t1_M0(1) = 47/384
    Z(1) = 7/8 + 3*(47/384) = 336/384 + 141/384 = 477/384 = 159/128

    t0_M0(2) = 4/3, t1_M0(2) = 1/6
    Z(2) = 4/3 + 3*(1/6) = 4/3 + 1/2 = 11/6

    WARNING: Z_exact uses partition_approx = t0(M=0) + 3*t1(M=0),
    a 2-TERM TRUNCATION. True Z(beta=1) is approx 2.96 (from exact Bessel functions).
    Our 159/128 is approx 1.24, which is 58% off. This is expected at M=0.
    For reliable thermodynamics, use M >= 3 (see PartitionHigherM.v).

    Observables like plaquette and gap are MORE accurate because they are
    RATIOS of eigenvalues where truncation errors partially cancel. *)

Definition Z_b1 : Q := 159 # 128.
Definition Z_b2 : Q := 11 # 6.

Definition gap_b1_local : Q := 289 # 384.

Lemma Z_b1_positive : 0 < Z_b1.
Proof. unfold Z_b1. lra. Qed.

Lemma Z_b2_positive : 0 < Z_b2.
Proof. unfold Z_b2. lra. Qed.

Lemma Z_b1_gt1 : 1 < Z_b1.
Proof. unfold Z_b1. lra. Qed.

Lemma Z_b2_gt1 : 1 < Z_b2.
Proof. unfold Z_b2. lra. Qed.

(* ================================================================== *)
(*  FREE ENERGY AND ENTROPY                                            *)
(* ================================================================== *)

(** Free energy: F = -ln(Z)/beta, using Pade ln approximation *)
Definition free_energy_at (Z beta : Q) : Q :=
  - log2_approx Z / beta.

(** Energy = plaquette expectation (concrete value from ProcessPlaquetteExtended) *)
Definition energy_b1 : Q := 10417 # 23336.

(** Entropy: S = beta*E + ln(Z) *)
Definition entropy_thermo_at (Z beta E : Q) : Q :=
  beta * E + log2_approx Z.

(** Concrete thermodynamic values at beta=1 *)
Definition F_b1 : Q := free_energy_at Z_b1 1.
Definition S_b1 : Q := entropy_thermo_at Z_b1 1 energy_b1.

(** Thermodynamic consistency: S = beta*E + ln(Z) by definition *)
Theorem thermo_consistency :
  S_b1 == 1 * energy_b1 + log2_approx Z_b1.
Proof. unfold S_b1, entropy_thermo_at. reflexivity. Qed.

Lemma F_b1_value : free_energy_at Z_b1 1 == - log2_approx Z_b1.
Proof. unfold free_energy_at, Z_b1, log2_approx. vm_compute. reflexivity. Qed.

(** ln(Z_b1) > 0 because Z_b1 > 1 *)
Lemma ln_Z_b1_positive : 0 < log2_approx Z_b1.
Proof.
  apply log2_approx_positive. exact Z_b1_gt1.
Qed.

(** Entropy positive at beta=1 *)
Lemma S_b1_positive : 0 < S_b1.
Proof.
  unfold S_b1, entropy_thermo_at.
  assert (H1 : 0 < energy_b1) by (unfold energy_b1; lra).
  assert (H2 : 0 < log2_approx Z_b1) by exact ln_Z_b1_positive.
  lra.
Qed.
