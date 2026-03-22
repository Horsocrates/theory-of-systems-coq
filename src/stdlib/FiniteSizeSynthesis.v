(** * FiniteSizeSynthesis.v -- Grand Synthesis of Finite-Size Corrections
    Elements: All finite-size correction results combined
    Roles:    Unified view: box, Ising, walk, spacing, process refinement
    Rules:    Finite-size effects are significant, computable, and decrease with K/N
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.FiniteSizeBox.
From ToS Require Import stdlib.FiniteSizeIsing.
From ToS Require Import stdlib.FiniteSizeWalk.
From ToS Require Import stdlib.FiniteSizeSpacing.
From ToS Require Import stdlib.FiniteSizeProcessRefinement.
Open Scope Q_scope.

(* ================================================================== *)
(*  CROSS-DOMAIN COMPARISON                                            *)
(* ================================================================== *)

(** Box correction (6%) is smaller than Ising correction (43% at N=3) *)
Lemma box_smaller_than_ising :
  (79#1296) < (21952#50653).
Proof. unfold Qlt. vm_compute. reflexivity. Qed.

(** Walk P(3) = 5/16 is between box and Ising corrections *)
Lemma walk_between_box_ising :
  (79#1296) < (5#16) /\ (5#16) < (21952#50653).
Proof. split; unfold Qlt; vm_compute; reflexivity. Qed.

(** All corrections exceed the 5% significance threshold *)
Lemma all_corrections_significant :
  (79#1296) > (1#20) /\
  (21952#50653) > (1#20) /\
  (5#16) > (1#20) /\
  (101#560) > (1#20).
Proof.
  split; [exact box_K2_above_threshold|].
  split; [exact ising_N3_above_threshold|].
  split; [exact walk_P3_above_threshold|].
  exact spacing_K5_above_threshold.
Qed.

(* ================================================================== *)
(*  CONVERGENCE PATTERN                                                *)
(* ================================================================== *)

(** Box: corrections decrease with K *)
Lemma box_convergence : correction_scaling 2 < correction_scaling 3.
Proof. exact correction_scaling_decreases. Qed.

(** Ising: corrections decrease with N *)
Lemma ising_convergence : ising_correction 3 < ising_correction 2.
Proof. exact correction_decreasing_2_3. Qed.

(** Walk: return probabilities decrease with K *)
Lemma walk_convergence : P_return 4 < P_return 3.
Proof. exact P_decreasing_3_4. Qed.

(* ================================================================== *)
(*  QUANTITATIVE SUMMARY                                               *)
(* ================================================================== *)

(** Box: correction is exactly -79/1296 *)
Lemma box_exact : correction_K2 == -(79#1296).
Proof. exact correction_K2_value. Qed.

(** Ising: N=3 correction is exactly 21952/50653 *)
Lemma ising_exact : ising_correction 3 == 21952#50653.
Proof. exact correction_N3. Qed.

(** Spacing: deviation is exactly 101/336 *)
Lemma spacing_exact : deviation_K5 == 101#336.
Proof. exact deviation_K5_value. Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                    *)
(* ================================================================== *)

Theorem finite_size_grand_synthesis :
  (* Box: negative correction, bounded *)
  correction_K2 == -(79#1296) /\
  correction_K2 < 0 /\
  (* Ising: exponential decay *)
  ising_correction 3 == 21952#50653 /\
  ising_correction 3 < 1#2 /\
  (* Walk: decreasing return probability *)
  P_return 5 == 63#256 /\
  P_return 3 < P_return 2 /\
  (* Spacing: bounded deviation *)
  deviation_K5 == 101#336 /\
  0 < deviation_K5 /\
  (* Process refinement: all corrections significant *)
  (79#1296) > (1#20) /\
  (21952#50653) > (1#20).
Proof.
  split; [exact correction_K2_value|].
  split; [exact correction_K2_negative|].
  split; [exact correction_N3|].
  split; [exact correction_N3_lt_half|].
  split; [exact P_return_5|].
  split; [exact P_decreasing_2_3|].
  split; [exact deviation_K5_value|].
  split; [exact deviation_K5_positive|].
  split; [exact box_K2_above_threshold|].
  exact ising_N3_above_threshold.
Qed.
