(** * OscillatorSynthesis.v -- Grand Synthesis of Oscillator Analysis as ToS System
    Elements: Traces, char poly, finite-size energy (all oscillator results)
    Roles:    Unification of spectral trace analysis with zero-point energy
    Rules:    tr(X^2)=K(K-1), e2 grows, E0 < 1/2 for K > 2, hierarchy
    Status:   Stdlib
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.OscillatorTraces.
From ToS Require Import stdlib.OscillatorCharPoly.
From ToS Require Import stdlib.OscillatorFiniteSize.
Open Scope Q_scope.

(* ================================================================== *)
(*  TRACE → CHAR POLY → EIGENVALUES → ENERGY CHAIN                    *)
(* ================================================================== *)

(** Traces provide spectral data *)
Lemma trace_chain_K2 :
  osc_tr_2 2 == 2 /\ elem_sym_e2 2 == 1 /\ E0_K2 == 1#2.
Proof.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  reflexivity.
Qed.

(** K=4: full chain *)
Lemma trace_chain_K4 :
  osc_tr_2 4 == 12 /\ elem_sym_e2 4 == 42 /\ E0_K4_approx < 1#2.
Proof.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  exact zero_point_K4.
Qed.

(* ================================================================== *)
(*  SPECTRAL WIDTH VS ZERO-POINT ENERGY                                *)
(* ================================================================== *)

(** As e2 (spectral width) grows, E0 decreases *)
Lemma width_vs_energy_K2_K4 :
  elem_sym_e2 2 < elem_sym_e2 4 /\ E0_K4_approx < E0_K2.
Proof.
  split. { exact e2_growth_2_3. }
  exact finite_size_K2_max.
Qed.

(** Trace ratio is constant 1/2 for small K *)
Lemma ratio_constancy : trace_ratio 2 == 1#2 /\ trace_ratio 3 == 1#2.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  FINITE → CONTINUUM MESSAGE                                         *)
(* ================================================================== *)

(** The 1/2 zero-point energy is a K=2 artifact *)
Lemma half_is_artifact :
  E0_K2 == 1#2 /\ E0_K4_approx < 1#2 /\ E0_K6_approx < E0_K4_approx.
Proof.
  split. { reflexivity. }
  split. { exact zero_point_K4. }
  exact zero_point_K6.
Qed.

(** Odd K: zero-point energy vanishes *)
Lemma odd_K_vanishes : E0_odd == 0 /\ E0_odd < E0_K4_approx.
Proof.
  split. { reflexivity. }
  exact E0_odd_le_even.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

Theorem oscillator_grand_synthesis :
  (* Trace formula *)
  osc_tr_2 2 == 2 /\ osc_tr_2 5 == 20 /\
  (* Char poly data *)
  elem_sym_e2 2 == 1 /\ elem_sym_e2 3 == 9 /\
  (* Spectral ratio *)
  trace_ratio 2 == 1#2 /\
  (* Finite-size energy *)
  E0_K2 == 1#2 /\ E0_K4_approx < 1#2 /\
  (* Odd K *)
  E0_odd == 0.
Proof.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { reflexivity. }
  split. { exact zero_point_K4. }
  reflexivity.
Qed.
