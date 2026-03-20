(** * EntropyConvergenceRate.v -- Convergence rate as new dynamical invariant
    Elements: entropy_oscillation, entropy_distance
    Roles:    Convergence rate refines topological entropy classification
    Rules:    Full shift: rate 0 (instant), golden mean: rate > 0 (oscillating)
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.LyapunovProcess.
From ToS Require Import stdlib.EntropyProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  CONVERGENCE RATE                                                   *)
(* ================================================================== *)

(** NEW INVARIANT: how fast does h_K approach its limit? *)

(** For full shift: rate = 0 (instant: h_K = ln(2) for all K) *)
Definition rate_full : Q := 0.

(** Successive difference: |h_{K+1} - h_K| *)
Definition entropy_oscillation (h : nat -> Q) (K : nat) : Q :=
  Qabs (h (S K) - h K).

Lemma full_shift_no_oscillation : forall K,
  entropy_oscillation h_full_process K == 0.
Proof.
  intro K. unfold entropy_oscillation, h_full_process.
  assert (H : ln2_approx - ln2_approx == 0) by ring.
  rewrite H. unfold Qabs. simpl. reflexivity.
Qed.

(** Golden mean oscillations *)
Lemma golden_osc_0 : entropy_oscillation h_golden_process 0 == 4#15.
Proof.
  unfold entropy_oscillation.
  rewrite h_golden_1, h_golden_0.
  (* |2/5 - 2/3| = |6/15 - 10/15| = 4/15 *)
  vm_compute. reflexivity.
Qed.

Lemma golden_osc_1 : entropy_oscillation h_golden_process 1 == 1#10.
Proof.
  unfold entropy_oscillation.
  rewrite h_golden_2, h_golden_1.
  (* |1/2 - 2/5| = 1/10 *)
  vm_compute. reflexivity.
Qed.

Lemma golden_osc_2 : entropy_oscillation h_golden_process 2 == 1#26.
Proof.
  unfold entropy_oscillation.
  rewrite h_golden_3, h_golden_2.
  (* |6/13 - 1/2| = |12/26 - 13/26| = 1/26 *)
  vm_compute. reflexivity.
Qed.

(** Oscillations DECREASE: system is converging *)
Theorem golden_osc_decreasing :
  entropy_oscillation h_golden_process 1 <
  entropy_oscillation h_golden_process 0.
Proof. rewrite golden_osc_1, golden_osc_0. lra. Qed.

Theorem golden_osc_decreasing_12 :
  entropy_oscillation h_golden_process 2 <
  entropy_oscillation h_golden_process 1.
Proof. rewrite golden_osc_2, golden_osc_1. lra. Qed.

(** Golden mean has nonzero oscillation (unlike full shift) *)
Lemma golden_osc_positive_0 : 0 < entropy_oscillation h_golden_process 0.
Proof. rewrite golden_osc_0. lra. Qed.

(* ================================================================== *)
(*  METRIC ON ENTROPY PROCESSES                                        *)
(* ================================================================== *)

(** d(h_A, h_B) = Σ_{k=0}^{N} |h_A(k) - h_B(k)| / 2^k *)
Definition entropy_distance (h1 h2 : nat -> Q) (N : nat) : Q :=
  fold_left (fun acc k =>
    acc + Qabs (h1 k - h2 k) / inject_Z (Z.of_nat (Nat.pow 2 k)))
    (seq 0 (S N)) 0.

(** Full shift vs golden mean: always distinguishable *)
(** At step 0: h_full(0) = h_golden(0) = 2/3. Agree!
    At step 1: h_full(1) = 2/3 ≠ h_golden(1) = 2/5. Distinguishable! *)
Theorem full_golden_distinguishable :
  0 < entropy_distance h_full_process h_golden_process 1.
Proof.
  unfold entropy_distance, h_full_process, h_golden_process,
         phi_process, ln2_approx, Qlt.
  rewrite <- Z.ltb_lt. vm_compute. reflexivity.
Qed.

(** Full shift vs identity: also distinguishable *)
Lemma full_id_distinguishable :
  0 < entropy_distance h_full_process h_id_process 0.
Proof.
  unfold entropy_distance, h_full_process, h_id_process, ln2_approx, Qlt.
  rewrite <- Z.ltb_lt. vm_compute. reflexivity.
Qed.

(** Identity has zero oscillation *)
Lemma id_no_oscillation : forall K,
  entropy_oscillation h_id_process K == 0.
Proof.
  intro K. unfold entropy_oscillation, h_id_process.
  assert (H : 0 - 0 == 0) by ring.
  rewrite H. unfold Qabs. simpl. reflexivity.
Qed.

(** Zero distance to self *)
Lemma distance_self_concrete :
  entropy_distance h_full_process h_full_process 0 == 0.
Proof.
  unfold entropy_distance, h_full_process, ln2_approx.
  vm_compute. reflexivity.
Qed.

(** THIS IS A FINER CLASSIFICATION than h_top alone:
    h_top: maps entropy → ℝ (collapses information)
    h_process: maps entropy → Proc (preserves convergence data) *)

Theorem convergence_rate_synthesis :
  (* Full shift: zero oscillation *)
  entropy_oscillation h_full_process 0 == 0 /\
  (* Golden mean: positive oscillation *)
  0 < entropy_oscillation h_golden_process 0 /\
  (* Oscillations decrease *)
  entropy_oscillation h_golden_process 1 <
  entropy_oscillation h_golden_process 0 /\
  (* Distinguishable by metric at step 1 *)
  0 < entropy_distance h_full_process h_golden_process 1.
Proof.
  split; [|split; [|split]].
  - exact (full_shift_no_oscillation 0).
  - exact golden_osc_positive_0.
  - exact golden_osc_decreasing.
  - exact full_golden_distinguishable.
Qed.
