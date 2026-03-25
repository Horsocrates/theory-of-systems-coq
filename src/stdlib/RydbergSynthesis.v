(** * RydbergSynthesis.v — Grand synthesis of Rydberg process convergence
    Elements: rydberg energies, rydberg_correction, convergence bounds
    Roles:    Unifies energy level structure with finite basis convergence
    Rules:    Correction monotone + bounded + converging = complete picture
    Status:   complete
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Qabs Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.RydbergProcess.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Energy level structure                                     *)
(* ================================================================== *)

Lemma synthesis_ground_state : rydberg 1 == -(1#1).
Proof. exact rydberg_1. Qed.

Lemma synthesis_first_excited : rydberg 2 == -(1#4).
Proof. exact rydberg_2. Qed.

(* ================================================================== *)
(*  Part II: Correction monotonicity                                   *)
(* ================================================================== *)

Lemma synthesis_correction_chain :
  rydberg_correction 1 < rydberg_correction 2 /\
  rydberg_correction 2 < rydberg_correction 3 /\
  rydberg_correction 3 < rydberg_correction 4.
Proof.
  split; [exact correction_improves_1_2 |].
  split; [exact correction_improves_2_3 | exact correction_improves_3_4].
Qed.

(* ================================================================== *)
(*  Part III: Boundedness                                              *)
(* ================================================================== *)

Lemma synthesis_bounded :
  rydberg_correction 1 < 1 /\ rydberg_correction 4 < 1.
Proof.
  split.
  - exact correction_bounded_1.
  - exact correction_bounded_4.
Qed.

(* ================================================================== *)
(*  Part IV: Convergence                                               *)
(* ================================================================== *)

Lemma synthesis_convergence :
  Qabs (rydberg_correction 3 - 1) < 1#10 /\
  Qabs (rydberg_correction 4 - 1) < 1#10.
Proof.
  split.
  - exact convergence_close_3.
  - exact convergence_close_4.
Qed.

(* ================================================================== *)
(*  Part V: Energy ordering                                            *)
(* ================================================================== *)

Lemma synthesis_energy_ordering : rydberg 1 < rydberg 2.
Proof.
  assert (H1 : rydberg 1 == -(1#1)) by (vm_compute; reflexivity).
  assert (H2 : rydberg 2 == -(1#4)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

Lemma synthesis_energy_ordering_23 : rydberg 2 < rydberg 3.
Proof.
  assert (H2 : rydberg 2 == -(1#4)) by (vm_compute; reflexivity).
  assert (H3 : rydberg 3 == -(1#9)) by (vm_compute; reflexivity).
  rewrite H2, H3. lra.
Qed.
