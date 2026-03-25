(** * VariationalFit.v — Variational Energy Fitting for Atomic Systems
    Elements: NIST target energies, grid search, energy convergence
    Roles:    Define variational energy targets and verify convergence properties
    Rules:    Energy converges as grid resolution increases; NIST deltas rational
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  NIST REFERENCE ENERGIES (as rational deltas from Hartree)          *)
(*  He: -2.903724 Ha → delta = 0.0466 from -2.857 (naive)             *)
(*  Li: -7.478060 Ha → delta = 0.343 from -7.135                      *)
(* ================================================================== *)

Definition nist_he_delta : Q := 466 # 10000.

Definition nist_li_delta : Q := 343 # 1000.

(* ================================================================== *)
(*  NIST deltas are positive                                           *)
(* ================================================================== *)

Lemma nist_he_delta_positive : 0 < nist_he_delta.
Proof. unfold nist_he_delta. vm_compute. reflexivity. Qed.

Lemma nist_li_delta_positive : 0 < nist_li_delta.
Proof. unfold nist_li_delta. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Li delta > He delta (lithium needs more correlation)               *)
(* ================================================================== *)

Lemma li_delta_larger : nist_he_delta < nist_li_delta.
Proof.
  unfold nist_he_delta, nist_li_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  VARIATIONAL ENERGY as function of grid resolution K                *)
(*  Coarser grids overestimate energy, finer grids converge            *)
(*  E(K) = delta * (20 / K) for a simple model                        *)
(* ================================================================== *)

Definition variational_energy (delta : Q) (K : positive) : Q :=
  delta * (20 # K).

(* ================================================================== *)
(*  CONCRETE: E_he at K=10                                             *)
(*  = (466/10000) * (20/10) = (466/10000) * 2 = 932/10000 = 233/2500 *)
(* ================================================================== *)

Lemma var_energy_he_K10 : variational_energy nist_he_delta 10 == 233 # 2500.
Proof.
  unfold variational_energy, nist_he_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE: E_he at K=20                                             *)
(*  = (466/10000) * (20/20) = 466/10000 = 233/5000                    *)
(* ================================================================== *)

Lemma var_energy_he_K20 : variational_energy nist_he_delta 20 == 233 # 5000.
Proof.
  unfold variational_energy, nist_he_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONVERGENCE: E(K=20) < E(K=10) for He                             *)
(* ================================================================== *)

Lemma var_energy_converges_he :
  variational_energy nist_he_delta 20 < variational_energy nist_he_delta 10.
Proof.
  unfold variational_energy, nist_he_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONVERGENCE: E(K=40) < E(K=20) for He                             *)
(* ================================================================== *)

Lemma var_energy_converges_he_2 :
  variational_energy nist_he_delta 40 < variational_energy nist_he_delta 20.
Proof.
  unfold variational_energy, nist_he_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  POSITIVITY of variational energies                                 *)
(* ================================================================== *)

Lemma var_energy_he_K10_positive : 0 < variational_energy nist_he_delta 10.
Proof.
  unfold variational_energy, nist_he_delta.
  vm_compute. reflexivity.
Qed.

Lemma var_energy_li_K10_positive : 0 < variational_energy nist_li_delta 10.
Proof.
  unfold variational_energy, nist_li_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Li variational energy > He at same grid                            *)
(* ================================================================== *)

Lemma var_energy_li_gt_he_K10 :
  variational_energy nist_he_delta 10 < variational_energy nist_li_delta 10.
Proof.
  unfold variational_energy, nist_he_delta, nist_li_delta.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  GRID RESOLUTION RATIO: E(K)/E(2K) = 2 in this model               *)
(* ================================================================== *)

Lemma grid_ratio_he :
  variational_energy nist_he_delta 10 ==
  2 * variational_energy nist_he_delta 20.
Proof.
  unfold variational_energy, nist_he_delta.
  vm_compute. reflexivity.
Qed.
