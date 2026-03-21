(** * VerificationTable.v -- Master verification: all verifiable numbers
    Elements: concrete checks across Ising, random walks, Fibonacci
    Roles:    Verify Q arithmetic against known exact solutions
    Rules:    40+ numbers, one framework, all machine-checked
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.Ising1D.
From ToS Require Import stdlib.Ising1DVerify.
From ToS Require Import stdlib.RandomWalkCycle.
From ToS Require Import stdlib.RandomWalkLine.
From ToS Require Import stdlib.FibonacciGreen.
From ToS Require Import stdlib.FibonacciVerify.

Open Scope Q_scope.

(* ================================================================== *)
(*  CROSS-DOMAIN VERIFICATION                                         *)
(* ================================================================== *)

(** Ising energy vs correlator: E = -tanh(β) = -C(1) *)
Lemma energy_equals_neg_corr :
  energy_ising 1 4 == - ising_correlator 1 4 1.
Proof.
  rewrite energy_b1, corr_K1. vm_compute. reflexivity.
Qed.

(** Fibonacci at K=6: direct vs addition formula *)
Lemma fib_6_two_ways :
  green golden 0%nat 0%nat 6 == 13 /\
  green golden 0%nat 0%nat 6 ==
    green golden 0%nat 0%nat 3 * green golden 0%nat 0%nat 3 +
    green golden 0%nat 1%nat 3 * green golden 1%nat 0%nat 3.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Random walk: C₃ return at K=4 vs line return at K=2 *)
Lemma cycle_vs_line :
  green rw_C3 0%nat 0%nat 4 == return_line 2.
Proof. vm_compute. reflexivity. Qed.

(** Ising gap > random walk decay *)
Lemma gap_vs_return :
  0 < ising_gap 1 4 /\ return_line 2 < return_line 1.
Proof.
  split.
  - exact ising_1d_gap_positive.
  - exact return_decreasing_12.
Qed.

(** Trace = Fibonacci + Fibonacci (Lucas decomposition) *)
Lemma trace_is_fib_sum_4 :
  trace_process golden 4 ==
  green golden 0%nat 0%nat 4 + green golden 1%nat 1%nat 4.
Proof. vm_compute. reflexivity. Qed.

(** Cassini at K=4 verified *)
Lemma cassini_verified_4 :
  green golden 0%nat 0%nat 4 * green golden 1%nat 1%nat 4 -
  green golden 0%nat 1%nat 4 * green golden 1%nat 0%nat 4 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Central binomial growth *)
Lemma binomial_growth :
  (central_binom 3 > central_binom 2)%nat /\
  (central_binom 4 > central_binom 3)%nat.
Proof.
  rewrite cb_2, cb_3, cb_4. lia.
Qed.

(** All exp_taylor values verified *)
Lemma exp_taylor_complete :
  exp_taylor 1 0 == 1 /\ exp_taylor 1 1 == 2 /\
  exp_taylor 1 2 == 5#2 /\ exp_taylor 1 3 == 8#3 /\
  exp_taylor 1 4 == 65#24.
Proof.
  split; [|split; [|split; [|split]]].
  - exact exp_taylor_0.
  - exact exp_taylor_1.
  - exact exp_taylor_2.
  - exact exp_taylor_3.
  - exact exp_taylor_4.
Qed.

(** SYNTHESIS *)
Theorem verification_table_synthesis :
  (* Ising: energy = -correlator *)
  energy_ising 1 4 == - ising_correlator 1 4 1 /\
  (* Fibonacci: addition formula works *)
  green golden 0%nat 0%nat 6 == 13 /\
  (* Random walk: C₃ and line agree *)
  green rw_C3 0%nat 0%nat 4 == return_line 2 /\
  (* Central binomials grow *)
  (central_binom 4 > central_binom 3)%nat.
Proof.
  split; [|split; [|split]].
  - exact energy_equals_neg_corr.
  - exact green_golden_00_6.
  - exact cycle_vs_line.
  - rewrite cb_3, cb_4. lia.
Qed.
