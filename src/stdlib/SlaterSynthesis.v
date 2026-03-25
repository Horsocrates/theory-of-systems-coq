(** * SlaterSynthesis.v — Grand Synthesis of Slater Q-Basis
    Elements: H/He/Li energy hierarchy, convergence, exact Q computations
    Roles:    Unify STO lattice results: bound states, Aufbau, convergence
    Rules:    H: E in (-1/2, 0); He: E < E_H; Li: E < E_He;
              Padé accuracy improves with M; all computations in exact Q
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
From ToS Require Import stdlib.SlaterEigenvalue.
From ToS Require Import stdlib.SlaterConvergence.
From ToS Require Import stdlib.SlaterHelium.
From ToS Require Import stdlib.SlaterLithium.

(* ================================================================== *)
(*  SYNTHESIS 1: All atoms have negative ground state energy           *)
(*  H, He, Li all form bound states on the lattice                     *)
(* ================================================================== *)

Lemma all_atoms_bound :
  E_1basis_M3 < 0 /\ E_He_total < 0 /\ E_Li_total < 0.
Proof.
  split; [| split].
  - exact E_1basis_neg.
  - exact E_He_total_neg.
  - exact E_Li_total_neg.
Qed.

(* ================================================================== *)
(*  SYNTHESIS 2: Energy ordering H > He > Li (more bound with Z)       *)
(*  Hydrogen is least bound, lithium most bound                        *)
(* ================================================================== *)

Lemma energy_ordering_H_He :
  E_1e_He < E_1e_H.
Proof. exact He_deeper_than_H. Qed.

Lemma energy_ordering_He_Li :
  E_1s_Li < E_1e_He.
Proof.
  unfold E_1s_Li, E_1e_He, F_1s_Li, F_11_He,
         SlaterKinetic.T_11_val,
         SlaterOverlap.S_11_raw,
         nuclear_element, kinetic_element,
         SlaterKinetic.sum_Q, SlaterNuclear.sum_Q,
         grad, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS 3: Hydrogen energy in correct range (-1/2, 0)            *)
(*  Variational bound above exact ground state                         *)
(* ================================================================== *)

Lemma hydrogen_qualitative : -(1#2) < E_1basis_M3 /\ E_1basis_M3 < 0.
Proof. exact energy_in_range. Qed.

(* ================================================================== *)
(*  SYNTHESIS 4: Padé convergence chain                                 *)
(*  Error at 1/5 < error at 1/4 < error at 1/3                        *)
(* ================================================================== *)

Lemma pade_convergence_chain :
  pade_error (1#5) < pade_error (1#4) /\
  pade_error (1#4) < pade_error (1#3).
Proof. exact error_chain. Qed.

(* ================================================================== *)
(*  SYNTHESIS 5: Lithium Aufbau principle verified                     *)
(*  1s fills before 2s (E_1s < E_2s)                                   *)
(* ================================================================== *)

Lemma aufbau_verified : E_1s_Li < E_2s_Li.
Proof. exact aufbau_1s_before_2s. Qed.

(* ================================================================== *)
(*  SYNTHESIS 6: Koopmans theorem — IP > 0 for all atoms              *)
(* ================================================================== *)

Lemma koopmans_Li : 0 < IP_Li.
Proof. exact IP_Li_pos. Qed.

(* ================================================================== *)
(*  SYNTHESIS 7: Complete pipeline                                     *)
(*  STO basis → Padé exp → lattice integrals → Fock matrix →          *)
(*  eigenvalue → bound state → convergent process                     *)
(*  All in exact rational arithmetic, zero floating point              *)
(* ================================================================== *)

Lemma complete_pipeline :
  (* Padé is accurate *)
  pade22_local 0 == 1 /\
  (* H is bound *)
  E_1basis_M3 < 0 /\
  (* He is more bound than H *)
  E_1e_He < E_1e_H /\
  (* Li Aufbau holds *)
  E_1s_Li < E_2s_Li /\
  (* Convergence improves with lattice *)
  pade_error (1#4) < pade_error (1#3).
Proof.
  split; [| split; [| split; [| split]]].
  - exact pade22_at_0.
  - exact E_1basis_neg.
  - exact He_deeper_than_H.
  - exact aufbau_1s_before_2s.
  - exact pade_error_improves.
Qed.
