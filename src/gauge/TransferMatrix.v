(* ========================================================================= *)
(*        TRANSFER MATRIX — Eigenvalue Gap for Lattice Gauge Theory          *)
(*                                                                            *)
(*  Transfer matrix: propagator between spatial slices.                      *)
(*  Concrete 2×2 case: 1+1D U(1) with K=2 discretization.                  *)
(*  Eigenvalues: λ₀ = 2 - β/8 (ground), λ₁ = β/8 (excited).              *)
(*  Mass gap: Δ = λ₀ - λ₁ = 2 - β/4 > 0 for 0 < β < 8.                  *)
(*                                                                            *)
(*  STATUS: ~25 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                              *)
(*  Author: Horsocrates | Date: March 2026                                    *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.QState.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.
From ToS Require Import linalg.PowerMethod.
From ToS Require Import gauge.LatticeStructure.
From ToS Require Import gauge.GaugeField.
From ToS Require Import gauge.WilsonAction.

(* ========================================================================= *)
(*  PART I: Transfer action and elements                                      *)
(* ========================================================================= *)

(** Transfer action between two spatial angle configs *)
Definition transfer_action_1d (beta theta1 theta2 : Q) : Q :=
  beta * (1 # 2) * (theta1 - theta2) * (theta1 - theta2).

(** Transfer matrix element: 1st-order Boltzmann *)
Definition transfer_element_1d (beta theta1 theta2 : Q) : Q :=
  1 - transfer_action_1d beta theta1 theta2.

Lemma transfer_action_zero_same : forall beta t,
  transfer_action_1d beta t t == 0.
Proof.
  intros beta t. unfold transfer_action_1d. lra.
Qed.

Lemma transfer_element_at_same : forall beta t,
  transfer_element_1d beta t t == 1.
Proof.
  intros beta t. unfold transfer_element_1d.
  rewrite transfer_action_zero_same. lra.
Qed.

(* ========================================================================= *)
(*  PART II: Concrete 2×2 transfer matrix                                    *)
(* ========================================================================= *)

(** ★ 2×2 transfer matrix for 1+1D U(1), K=2 discretization ★
    Angles: {0, 1/2}. T_{ij} = 1 - β/2·(θ_i - θ_j)².
    T_{00} = T_{11} = 1 (same angle), T_{01} = T_{10} = 1 - β/8 *)
Definition transfer_2x2 (beta : Q) : QMat 2 2 :=
  qmat2x2 1 (1 - beta * (1#8)) (1 - beta * (1#8)) 1.

(** Eigenvalue definitions — use *(1#8) to avoid Qdiv issues with lra *)
Definition transfer_eigenvalue_0 (beta : Q) : Q := 2 - beta * (1 # 8).
Definition transfer_eigenvalue_1 (beta : Q) : Q := beta * (1 # 8).

(** ★ Mass gap: difference of eigenvalues ★ *)
Definition mass_gap_2x2 (beta : Q) : Q :=
  transfer_eigenvalue_0 beta - transfer_eigenvalue_1 beta.

(** Transfer matrix is symmetric *)
Lemma transfer_2x2_symmetric : forall beta,
  is_symmetric (transfer_2x2 beta).
Proof.
  intros beta i j Hi Hj.
  destruct i as [| [| i']]; try lia;
  destruct j as [| [| j']]; try lia;
  unfold transfer_2x2, qmat2x2, mat_entry, mat_row, qvec2; simpl;
  unfold Qeq; simpl; lia.
Qed.

(** Transfer matrix trace = 2 *)
Lemma transfer_2x2_trace : forall beta,
  mat_trace (transfer_2x2 beta) == 2.
Proof.
  intros beta.
  unfold mat_trace, transfer_2x2, qmat2x2, sum_Q, mat_entry, mat_row, qvec2, qv_nth, qv_data, Qdiv.
  simpl. lra.
Qed.

(** Transfer matrix determinant *)
Lemma transfer_2x2_det : forall beta,
  det_2x2 (transfer_2x2 beta) == 1 - (1 - beta * (1#8)) * (1 - beta * (1#8)).
Proof.
  intros beta.
  unfold det_2x2, transfer_2x2, qmat2x2, mat_entry, mat_row, qvec2, qv_nth, qv_data, Qdiv.
  simpl. lra.
Qed.

(* ========================================================================= *)
(*  PART III: Eigenvalues of transfer matrix                                  *)
(* ========================================================================= *)

(** ★ Ground state eigenvalue: λ₀ = 2 - β/8, eigenvector (1,1) ★ *)
Theorem transfer_2x2_eigenvalue_0 : forall beta,
  is_eigenvalue (transfer_2x2 beta) (2 - beta * (1 # 8)).
Proof.
  intros beta.
  exists (qvec2 1 1). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, transfer_2x2, qmat2x2, qvec2, qv_nth, qv_data, Qdiv;
    simpl; lra.
Qed.

(** ★ Excited state eigenvalue: λ₁ = β/8, eigenvector (1,-1) ★ *)
Theorem transfer_2x2_eigenvalue_1 : forall beta,
  is_eigenvalue (transfer_2x2 beta) (beta * (1 # 8)).
Proof.
  intros beta.
  exists (qvec2 1 (-(1))). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, transfer_2x2, qmat2x2, qvec2, qv_nth, qv_data, Qdiv;
    simpl; lra.
Qed.

(** Ground state eigenvalue is positive for β < 16 *)
Lemma eigenvalue_0_positive : forall beta,
  0 < beta -> beta < 16 -> 0 < transfer_eigenvalue_0 beta.
Proof.
  intros beta H1 H2. unfold transfer_eigenvalue_0. lra.
Qed.

(** Excited state eigenvalue is positive for β > 0 *)
Lemma eigenvalue_1_positive : forall beta,
  0 < beta -> 0 < transfer_eigenvalue_1 beta.
Proof.
  intros beta H. unfold transfer_eigenvalue_1. lra.
Qed.

(** ★ Ground state dominates for 0 < β < 8 ★ *)
Theorem eigenvalue_0_dominates : forall beta,
  0 < beta -> beta < 8 ->
  transfer_eigenvalue_1 beta < transfer_eigenvalue_0 beta.
Proof.
  intros beta H1 H2. unfold transfer_eigenvalue_0, transfer_eigenvalue_1. lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Mass gap                                                         *)
(* ========================================================================= *)

(** Mass gap formula: Δ = 2 - β/4 *)
Lemma mass_gap_2x2_formula : forall beta,
  mass_gap_2x2 beta == 2 - beta * (1 # 4).
Proof.
  intros beta. unfold mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1. lra.
Qed.

(** ★ THE MASS GAP THEOREM: gap > 0 for 0 < β < 8 ★ *)
Theorem mass_gap_2x2_positive : forall beta,
  0 < beta -> beta < 8 -> 0 < mass_gap_2x2 beta.
Proof.
  intros beta H1 H2. unfold mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1. lra.
Qed.

(** Concrete: gap at β = 1 is 7/4 *)
Lemma mass_gap_at_beta_1 : mass_gap_2x2 1 == 7 # 4.
Proof.
  unfold mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1.
  unfold Qeq; simpl; lia.
Qed.

(** Gap vanishes at β = 8 *)
Lemma gap_vanishes_at_8 : mass_gap_2x2 8 == 0.
Proof.
  unfold mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1.
  unfold Qeq; simpl; lia.
Qed.

(** Eigenvalue sum = trace *)
Lemma eigenvalue_sum_trace : forall beta,
  transfer_eigenvalue_0 beta + transfer_eigenvalue_1 beta ==
  mat_trace (transfer_2x2 beta).
Proof.
  intros beta.
  unfold transfer_eigenvalue_0, transfer_eigenvalue_1.
  unfold mat_trace, transfer_2x2, qmat2x2, sum_Q, mat_entry, mat_row, qvec2, qv_nth, qv_data, Qdiv.
  simpl. lra.
Qed.

(** Eigenvectors are orthogonal *)
Lemma eigenvectors_orthogonal :
  dot_product (qvec2 1 1) (qvec2 1 (-(1))) == 0.
Proof.
  unfold dot_product, qvec2, qv_nth, qv_data. simpl. lra.
Qed.

(* ========================================================================= *)
(*  PART V: Gap monotonicity and Rayleigh                                     *)
(* ========================================================================= *)

(** Gap decreases with β *)
Lemma gap_monotone_beta : forall beta1 beta2,
  0 < beta1 -> beta1 < beta2 -> beta2 < 8 ->
  mass_gap_2x2 beta2 < mass_gap_2x2 beta1.
Proof.
  intros beta1 beta2 H1 H12 H2.
  unfold mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1. lra.
Qed.

(** Positive entries for β in range *)
Lemma transfer_positive_entries : forall beta,
  0 < beta -> beta < 8 ->
  0 < mat_entry (transfer_2x2 beta) 0 0 /\
  0 < mat_entry (transfer_2x2 beta) 0 1 /\
  0 < mat_entry (transfer_2x2 beta) 1 0 /\
  0 < mat_entry (transfer_2x2 beta) 1 1.
Proof.
  intros beta H1 H2.
  unfold transfer_2x2, qmat2x2, mat_entry, mat_row, qvec2, qv_nth, qv_data, Qdiv.
  simpl. repeat split; lra.
Qed.

(** Rayleigh quotient for ground state *)
Lemma rayleigh_ground_state : forall beta,
  norm_sq (qvec2 1 1) > 0 ->
  rayleigh_quotient (transfer_2x2 beta) (qvec2 1 1) == 2 - beta * (1 # 8).
Proof.
  intros beta Hns.
  apply rayleigh_eigenvalue.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, transfer_2x2, qmat2x2, qvec2, qv_nth, qv_data, Qdiv;
    simpl; lra.
  - exact Hns.
Qed.

(** Rayleigh quotient for excited state *)
Lemma rayleigh_excited_state : forall beta,
  norm_sq (qvec2 1 (-(1))) > 0 ->
  rayleigh_quotient (transfer_2x2 beta) (qvec2 1 (-(1))) == beta * (1 # 8).
Proof.
  intros beta Hns.
  apply rayleigh_eigenvalue.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, transfer_2x2, qmat2x2, qvec2, qv_nth, qv_data, Qdiv;
    simpl; lra.
  - exact Hns.
Qed.

(* ========================================================================= *)
(*  PART VI: Summary                                                          *)
(* ========================================================================= *)

Theorem transfer_matrix_summary :
  (* Symmetric *)
  (forall beta, is_symmetric (transfer_2x2 beta)) /\
  (* Two eigenvalues *)
  (forall beta, is_eigenvalue (transfer_2x2 beta) (2 - beta * (1#8))) /\
  (forall beta, is_eigenvalue (transfer_2x2 beta) (beta * (1#8))) /\
  (* Gap positive *)
  (forall beta, 0 < beta -> beta < 8 -> 0 < mass_gap_2x2 beta) /\
  (* Eigenvectors orthogonal *)
  (dot_product (qvec2 1 1) (qvec2 1 (-(1))) == 0).
Proof.
  split; [exact transfer_2x2_symmetric |].
  split; [exact transfer_2x2_eigenvalue_0 |].
  split; [exact transfer_2x2_eigenvalue_1 |].
  split; [exact mass_gap_2x2_positive |].
  exact eigenvectors_orthogonal.
Qed.

(** THE transfer matrix theorem *)
Theorem transfer_matrix_main :
  (forall beta, is_symmetric (transfer_2x2 beta)) /\
  (forall beta, is_eigenvalue (transfer_2x2 beta) (2 - beta * (1#8))) /\
  (forall beta, is_eigenvalue (transfer_2x2 beta) (beta * (1#8))) /\
  (forall beta, 0 < beta -> beta < 8 -> 0 < mass_gap_2x2 beta).
Proof.
  split; [exact transfer_2x2_symmetric |].
  split; [exact transfer_2x2_eigenvalue_0 |].
  split; [exact transfer_2x2_eigenvalue_1 |].
  exact mass_gap_2x2_positive.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~25 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part I: transfer_action_zero_same, transfer_element_at_same (2)          *)
(*  Part II: transfer_2x2_symmetric, transfer_2x2_trace,                     *)
(*           transfer_2x2_det (3)                                            *)
(*  Part III: transfer_2x2_eigenvalue_0, transfer_2x2_eigenvalue_1,          *)
(*            eigenvalue_0_positive, eigenvalue_1_positive,                  *)
(*            eigenvalue_0_dominates (5)                                     *)
(*  Part IV: mass_gap_2x2_formula, mass_gap_2x2_positive,                   *)
(*           mass_gap_at_beta_1, gap_vanishes_at_8,                          *)
(*           eigenvalue_sum_trace, eigenvectors_orthogonal (6)              *)
(*  Part V: gap_monotone_beta, transfer_positive_entries,                    *)
(*          rayleigh_ground_state, rayleigh_excited_state (4)               *)
(*  Part VI: transfer_matrix_summary, transfer_matrix_main,                  *)
(*           total_count (3)                                                *)
(* ========================================================================= *)
