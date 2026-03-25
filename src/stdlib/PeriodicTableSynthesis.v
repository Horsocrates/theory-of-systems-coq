(** * PeriodicTableSynthesis.v — Grand synthesis of periodic table structure
    Elements: H_full Hamiltonian, kinetic/potential split, atomic_gap, Z-scaling
    Roles:    Unifies tridiagonal structure (File 10) with spectral classification (File 11)
    Rules:    Universal kinetic + Z-dependent potential + decreasing gap = full periodic table
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Qabs Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.PeriodicTableTridiag.
From ToS Require Import stdlib.AtomicClassification.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Hamiltonian + Gap consistency                              *)
(* ================================================================== *)

Lemma synthesis_H_diagonal : H_full 1 3 0 0 == -(3#4).
Proof. exact H_full_H_diag0. Qed.

Lemma synthesis_He_diagonal : H_full 2 3 0 0 == -(7#4).
Proof. exact H_full_He_diag0. Qed.

Lemma synthesis_H_gap : atomic_gap 1 1 == 3#4.
Proof. exact H_gap_12. Qed.

(* ================================================================== *)
(*  Part II: Z-scaling universality                                    *)
(* ================================================================== *)

Lemma synthesis_Z_scaling_gap : atomic_gap 2 1 == 4 * atomic_gap 1 1.
Proof. exact He_H_gap_ratio_12. Qed.

Lemma synthesis_Z_scaling_gap_23 : atomic_gap 2 2 == 4 * atomic_gap 1 2.
Proof. exact He_H_gap_ratio_23. Qed.

(* ================================================================== *)
(*  Part III: Gap decreases — spectral classification                  *)
(* ================================================================== *)

Lemma synthesis_gap_chain :
  atomic_gap 1 1 > atomic_gap 1 2 /\
  atomic_gap 1 2 > atomic_gap 1 3.
Proof.
  split.
  - exact gap_decreases_H_12_23.
  - exact gap_decreases_H_23_34.
Qed.

(* ================================================================== *)
(*  Part IV: Grand synthesis — potential distinguishes atoms            *)
(* ================================================================== *)

Lemma synthesis_atoms_differ :
  ~ (coulomb_potential 1 3 0 == coulomb_potential 2 3 0).
Proof. exact H_He_potential_differ. Qed.

Lemma synthesis_gap_vanishes : atomic_gap 1 10 < 1#100.
Proof. exact gap_vanishes_n10. Qed.
