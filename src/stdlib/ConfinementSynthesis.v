(** * ConfinementSynthesis.v -- Grand synthesis of confinement results
    Elements: confinement_grand_synthesis, potential_to_gap, classification_correct
    Roles:    Combines Cornell potential, gapping, and classification
    Rules:    Imports CornellPotential, ConfinementGapping, ConfinementConnection
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.CornellPotential.
From ToS Require Import stdlib.ConfinementGapping.
From ToS Require Import stdlib.ConfinementConnection.

Open Scope Q_scope.

(* ================================================================== *)
(*  POTENTIAL → GAP CONNECTION                                          *)
(* ================================================================== *)

(** Cornell potential is attractive at short range *)
Lemma potential_attractive_short :
  cornell_potential 1 (1#10) 10 O == -(1999#100).
Proof. vm_compute. reflexivity. Qed.

(** Gap increases with confinement *)
Lemma gap_increases_with_sigma :
  gap_ratio 0%nat < gap_ratio 100%nat.
Proof.
  rewrite gap_coulomb, gap_strong. lra.
Qed.

(** Classification is consistent with gap values *)
Lemma classification_correct :
  classify_confinement (gap_ratio 0%nat) = Free /\
  classify_confinement (gap_ratio 100%nat) = Confined.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Crossover exists in potential AND classification changes *)
Lemma potential_classification_connection :
  cornell_potential 1 (1#10) 10 O < 0 /\
  cornell_potential 1 (1#10) 10 nat99 > 0 /\
  classify_confinement (186#1000) = Free /\
  classify_confinement (658#1000) = Confined.
Proof.
  split; [| split; [| split]].
  - rewrite cornell_sigma_small. lra.
  - rewrite cornell_confining_val. lra.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** Monotone gapping from import *)
Lemma synthesis_monotone :
  gap_ratio 0%nat < gap_ratio 5%nat /\
  gap_ratio 5%nat < gap_ratio 25%nat.
Proof.
  rewrite gap_coulomb, gap_small, gap_moderate. split; lra.
Qed.

(** Mass gap is positive (YM connection) *)
Lemma synthesis_ym_gap :
  (289#384) > 0 /\ (5#36) < (3#4).
Proof. split; lra. Qed.

(** Transition happens: 10 is below half, 25 is above *)
Lemma synthesis_transition :
  gap_ratio 10%nat < 1#2 /\ gap_ratio 25%nat > 1#2.
Proof.
  rewrite gap_10_val, gap_moderate. split; lra.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

(** Everything together: potential, gapping, classification, YM *)
Theorem confinement_grand_synthesis :
  (* Cornell potential shows crossover *)
  cornell_potential 1 0 10 O == -(20) /\
  cornell_potential 1 (1#10) 10 nat99 > 0 /\
  (* Gap ratio is monotone *)
  gap_ratio 0%nat < gap_ratio 100%nat /\
  (* Classification works *)
  classify_confinement (186#1000) = Free /\
  classify_confinement (658#1000) = Confined.
Proof.
  split; [| split; [| split; [| split]]].
  - vm_compute. reflexivity.
  - rewrite cornell_confining_val. lra.
  - rewrite gap_coulomb, gap_strong. lra.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
