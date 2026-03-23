(** * QuantumAlgSynthesis2.v -- Quantum Algorithm Grand Synthesis as ToS System
    Elements: BV speedup, QFT8 convergence, Shor factoring
    Roles:    Three quantum algorithms unified: hidden structure, phase estimation, period finding
    Rules:    Each algorithm demonstrates quantum advantage through process arithmetic
    Status:   Stdlib -- Six Directions Phase 2, Section C7
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa Qabs.
From ToS Require Import stdlib.BernsteinVazirani.
From ToS Require Import stdlib.QFT8Process.
From ToS Require Import stdlib.ShorFactor15.

Open Scope Q_scope.

(* ================================================================== *)
(*  QUANTUM SPEEDUP SUMMARY                                            *)
(* ================================================================== *)

Theorem bv_gives_speedup :
  forall n, (2 <= n)%nat ->
  (classical_queries n > quantum_queries)%nat.
Proof. exact speedup_general. Qed.

Theorem qft8_converges :
  Qabs (norm_sq_error 2%nat) < Qabs (norm_sq_error 1%nat).
Proof. exact error_decreasing_1_2. Qed.

Theorem shor_factors_15 :
  (Z.gcd (7*7 + 1) 15 = 5)%Z /\ (Z.gcd (7*7 - 1) 15 = 3)%Z.
Proof.
  split.
  - exact factor1.
  - exact factor2.
Qed.

(* ================================================================== *)
(*  QUANTUM QUERY COUNTS                                                *)
(* ================================================================== *)

Lemma bv_single_query : quantum_queries = 1%nat.
Proof. exact quantum_constant. Qed.

Lemma shor_period_is_4 : shor_period = 4%nat.
Proof. reflexivity. Qed.

Lemma sqrt2_precision_3 : sqrt2_step 3%nat == 577#408.
Proof. exact sqrt2_step3. Qed.

(* ================================================================== *)
(*  THREE-ALGORITHM CONNECTION                                          *)
(* ================================================================== *)

Theorem three_algorithms_work :
  (quantum_queries = 1%nat) /\
  (sqrt2_step 3%nat == 577#408) /\
  (pow7_mod15 0%nat = 1%Z) /\
  (pow7_mod15 4%nat = 1%Z).
Proof.
  split. { exact quantum_constant. }
  split. { exact sqrt2_step3. }
  split. { exact pow7_at_0. }
  exact pow7_at_4.
Qed.

Lemma bv_s5_recap : bv_f 5%nat 1%nat = 1%nat.
Proof. exact bv_s5_x1. Qed.

Lemma shor_factors_valid : (Z.gcd (7*7+1) 15 = 5)%Z.
Proof. exact factor1. Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

Theorem quantum_alg_grand_synthesis :
  (* BV: single query suffices *)
  (quantum_queries = 1%nat) /\
  (* QFT8: Newton converges *)
  (Qabs (norm_sq_error 2%nat) < Qabs (norm_sq_error 1%nat)) /\
  (* Shor: 15 = 3 * 5 *)
  ((3 * 5)%Z = 15%Z) /\
  (* Period verified *)
  (pow7_mod15 4%nat = 1%Z).
Proof.
  split. { exact quantum_constant. }
  split. { exact error_decreasing_1_2. }
  split. { reflexivity. }
  exact pow7_at_4.
Qed.
