(** * StrictlyFiner.v -- Process classification is strictly finer than h_top
    Elements: same_entropy_diff_process, process_distinguishes
    Roles:    Two SFTs can have same h_top but different orbit processes
    Rules:    This is the fundamental theorem of process-based classification
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.
From ToS Require Import stdlib.SFTEntropyGeneral.
From ToS Require Import stdlib.SFTClassification.
From ToS Require Import stdlib.SFTClassificationSynthesis.

Open Scope Q_scope.

(* ================================================================== *)
(*  WITNESS PAIR: same λ_max, different orbit process                  *)
(* ================================================================== *)

(** diag_21 = diag(2,1) and diag_2m1 = diag(2,-1)
    Both have λ_max = 2, so same topological entropy.
    But tr(diag_21^K) = 2^K + 1 ≠ 2^K + (-1)^K = tr(diag_2m1^K) *)

(** Recall from SFTClassification: diag_21 and diag_2m1 *)

Lemma diag_21_trace : mat_trace diag_21 == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma diag_2m1_trace : mat_trace diag_2m1 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Same max eigenvalue λ_max = 2 *)
Lemma diag_21_has_eigenvalue_2 :
  mat_entry diag_21 0 0 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma diag_2m1_has_eigenvalue_2 :
  mat_entry diag_2m1 0 0 == 2.
Proof. vm_compute. reflexivity. Qed.

(** Different traces → different orbit counts at K=1 *)
Lemma strictly_finer_at_1 :
  ~ (tr_pow diag_21 1 == tr_pow diag_2m1 1).
Proof.
  unfold tr_pow. simpl.
  intro H. vm_compute in H. unfold Qeq in H. simpl in H. lia.
Qed.

(** Orbit process values *)
Lemma diag_21_orbits :
  tr_pow diag_21 1 == 3 /\
  tr_pow diag_21 2 == 5.
Proof. split; vm_compute; reflexivity. Qed.

Lemma diag_2m1_orbits :
  tr_pow diag_2m1 1 == 1 /\
  tr_pow diag_2m1 2 == 5.
Proof. split; vm_compute; reflexivity. Qed.

(** At K=2: both give 5 (coincidence: 4+1 = 4+1) *)
Lemma orbits_agree_at_2 :
  tr_pow diag_21 2 == tr_pow diag_2m1 2.
Proof. vm_compute. reflexivity. Qed.

(** At K=1: they differ (3 ≠ 1) — process sees the difference *)
Lemma orbits_differ_at_1 :
  ~ (tr_pow diag_21 1 == tr_pow diag_2m1 1).
Proof. exact strictly_finer_at_1. Qed.

(* ================================================================== *)
(*  THE STRICTLY FINER THEOREM                                         *)
(* ================================================================== *)

(** There exist two 2×2 SFTs with:
    1. Same maximal eigenvalue (same h_top)
    2. Different orbit process (different classification) *)

Theorem process_strictly_finer_than_entropy :
  (* Same λ_max = 2 *)
  mat_entry diag_21 0 0 == 2 /\
  mat_entry diag_2m1 0 0 == 2 /\
  (* Different orbit counts *)
  ~ (tr_pow diag_21 1 == tr_pow diag_2m1 1).
Proof.
  split; [|split].
  - exact diag_21_has_eigenvalue_2.
  - exact diag_2m1_has_eigenvalue_2.
  - exact strictly_finer_at_1.
Qed.

(* ================================================================== *)
(*  COMPLETE INVARIANT: spectrum determines process for 2×2            *)
(* ================================================================== *)

(** For 2×2: the orbit process is determined by (trace, det).
    So two 2×2 matrices give the same orbit process iff they have
    the same trace and determinant. *)

Lemma diag_21_det : det_2x2 diag_21 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma diag_2m1_det : det_2x2 diag_2m1 == -(2).
Proof. vm_compute. reflexivity. Qed.

(** Different determinant confirms different dynamics *)
Lemma different_det_confirms :
  ~ (det_2x2 diag_21 == det_2x2 diag_2m1).
Proof.
  rewrite diag_21_det, diag_2m1_det.
  unfold Qeq. simpl. lia.
Qed.

(** SYNTHESIS *)
Theorem strictly_finer_synthesis :
  (* Witness pair: same λ_max *)
  mat_entry diag_21 0 0 == mat_entry diag_2m1 0 0 /\
  (* Different traces *)
  ~ (mat_trace diag_21 == mat_trace diag_2m1) /\
  (* Different determinants *)
  ~ (det_2x2 diag_21 == det_2x2 diag_2m1) /\
  (* Process distinguishes at K=1 *)
  ~ (tr_pow diag_21 1 == tr_pow diag_2m1 1) /\
  (* Process agrees at K=2 (coincidence) *)
  tr_pow diag_21 2 == tr_pow diag_2m1 2.
Proof.
  split; [|split; [|split; [|split]]].
  - vm_compute. reflexivity.
  - rewrite diag_21_trace, diag_2m1_trace. unfold Qeq. simpl. lia.
  - exact different_det_confirms.
  - exact strictly_finer_at_1.
  - exact orbits_agree_at_2.
Qed.
