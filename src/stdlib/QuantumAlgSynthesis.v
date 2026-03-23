(** * QuantumAlgSynthesis.v — Quantum Algorithm Grand Synthesis
    Elements: Deutsch, QFT, Grover results unified
    Roles:    Three quantum algorithms as process demonstrations
    Rules:    Each algorithm: classical query count > quantum query count
    Status:   Stdlib
    STATUS: 6 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From ToS Require Import stdlib.DeutschAlgorithm.
From ToS Require Import stdlib.QFT4.
From ToS Require Import stdlib.GroverPhase.
Open Scope Q_scope.

(* ================================================================== *)
(*  DEUTSCH: 1 quantum query vs 2 classical queries                   *)
(* ================================================================== *)

Lemma deutsch_quantum_advantage :
  (* Constant oracle: |01> amplitude = 4 *)
  deutsch_const (S O) == 4 /\
  (* Balanced oracle: |01> amplitude = 0 *)
  deutsch_balanced (S O) == 0.
Proof.
  split; [exact deutsch_const_1|exact deutsch_balanced_1].
Qed.

(* ================================================================== *)
(*  QFT: Phase interference as process                                 *)
(* ================================================================== *)

Lemma qft_interference :
  (* Row 0: constructive interference *)
  qft4_row_sum_real O == 4 /\
  (* Row 1: destructive interference *)
  qft4_row_sum_real (S O) == 0.
Proof.
  split; [exact row0_sum|exact row1_sum].
Qed.

(* ================================================================== *)
(*  GROVER: Amplitude amplification                                    *)
(* ================================================================== *)

Lemma grover_amplification :
  (* Target found with certainty after 1 iteration *)
  grover_result (S (S O)) O == 1 /\
  (* Non-targets have zero amplitude *)
  grover_result O O == 0.
Proof.
  split; [exact grover_target_2|exact grover_target_0].
Qed.

(* ================================================================== *)
(*  CLASSICAL QUERY COUNTS                                             *)
(* ================================================================== *)

Definition deutsch_classical_queries : nat := 2%nat.
Definition deutsch_quantum_queries : nat := 1%nat.
Definition grover_classical_queries (N : nat) : nat := N.
Definition grover_quantum_queries : nat := 1%nat.  (* for N=4, 1 iteration *)

Lemma deutsch_saves_queries :
  (deutsch_quantum_queries < deutsch_classical_queries)%nat.
Proof. unfold deutsch_quantum_queries, deutsch_classical_queries. lia. Qed.

Lemma grover_saves_queries :
  (grover_quantum_queries < grover_classical_queries 4)%nat.
Proof. unfold grover_quantum_queries, grover_classical_queries. lia. Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                    *)
(* ================================================================== *)

Theorem quantum_algorithm_grand_synthesis :
  (* Deutsch distinguishes in 1 query *)
  deutsch_const (S O) == 4 /\
  deutsch_balanced (S O) == 0 /\
  (* QFT produces interference *)
  qft4_row_sum_real O == 4 /\
  (* Grover finds target *)
  grover_result (S (S O)) O == 1.
Proof.
  split; [exact deutsch_const_1|].
  split; [exact deutsch_balanced_1|].
  split; [exact row0_sum|].
  exact grover_target_2.
Qed.
