(* ========================================================================= *)
(*        QUBIT — Concrete Single-Qubit Quantum Mechanics                   *)
(*                                                                          *)
(*  Part of: Theory of Systems — Concrete Quantum Systems (Phase 3E)        *)
(*                                                                          *)
(*  Defines qubit states |0⟩, |1⟩, |+⟩, |−⟩, Pauli-Z and Pauli-X         *)
(*  observables, Born probabilities, and expectation values — all with     *)
(*  verified concrete numerical results.                                    *)
(*                                                                          *)
(*  KEY RESULT: qubit_equal_superposition — measuring |0⟩ in state |+⟩    *)
(*  gives probability exactly 1/2.                                         *)
(*                                                                          *)
(*  STATUS: 42 Qed, 0 Admitted                                             *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.BornRule.
From ToS Require Import physics.SpectralDichotomy.

(* ========================================================================= *)
(*  PART I: QUBIT STATES + HELPERS                                          *)
(* ========================================================================= *)

(** Standard qubit basis states *)
Definition qubit_0 : QState 2 := basis_state 2 0.
Definition qubit_1 : QState 2 := basis_state 2 1.

(** Superposition states *)
Definition qubit_plus : QState 2 := state_add qubit_0 qubit_1.
Definition qubit_minus : QState 2 := state_add qubit_0 (state_scale (-(1)) qubit_1).

(** Component access for qubit_0 *)
Lemma qubit_0_component_0 : forall k,
  qv_nth (state_at qubit_0 k) 0 == 1.
Proof.
  intros k. unfold qubit_0. rewrite basis_state_at.
  apply basis_vec_same. lia.
Qed.

Lemma qubit_0_component_1 : forall k,
  qv_nth (state_at qubit_0 k) 1 == 0.
Proof.
  intros k. unfold qubit_0. rewrite basis_state_at.
  apply basis_vec_diff; lia.
Qed.

(** Component access for qubit_1 *)
Lemma qubit_1_component_0 : forall k,
  qv_nth (state_at qubit_1 k) 0 == 0.
Proof.
  intros k. unfold qubit_1. rewrite basis_state_at.
  apply basis_vec_diff; lia.
Qed.

Lemma qubit_1_component_1 : forall k,
  qv_nth (state_at qubit_1 k) 1 == 1.
Proof.
  intros k. unfold qubit_1. rewrite basis_state_at.
  apply basis_vec_same. lia.
Qed.

(** Component access for qubit_plus = |0⟩ + |1⟩ *)
Lemma qubit_plus_component_0 : forall k,
  qv_nth (state_at qubit_plus k) 0 == 1.
Proof.
  intros k. unfold qubit_plus.
  change (state_at (state_add qubit_0 qubit_1) k)
    with (qv_add (state_at qubit_0 k) (state_at qubit_1 k)).
  rewrite qv_add_nth; [| lia].
  rewrite qubit_0_component_0, qubit_1_component_0. ring.
Qed.

Lemma qubit_plus_component_1 : forall k,
  qv_nth (state_at qubit_plus k) 1 == 1.
Proof.
  intros k. unfold qubit_plus.
  change (state_at (state_add qubit_0 qubit_1) k)
    with (qv_add (state_at qubit_0 k) (state_at qubit_1 k)).
  rewrite qv_add_nth; [| lia].
  rewrite qubit_0_component_1, qubit_1_component_1. ring.
Qed.

(** Component access for qubit_minus = |0⟩ - |1⟩ *)
Lemma qubit_minus_component_0 : forall k,
  qv_nth (state_at qubit_minus k) 0 == 1.
Proof.
  intros k. unfold qubit_minus.
  change (state_at (state_add qubit_0 (state_scale (-(1)) qubit_1)) k)
    with (qv_add (state_at qubit_0 k) (qv_scale (-(1)) (state_at qubit_1 k))).
  rewrite qv_add_nth; [| lia].
  rewrite qv_scale_nth; [| lia].
  rewrite qubit_0_component_0, qubit_1_component_0. ring.
Qed.

Lemma qubit_minus_component_1 : forall k,
  qv_nth (state_at qubit_minus k) 1 == -(1).
Proof.
  intros k. unfold qubit_minus.
  change (state_at (state_add qubit_0 (state_scale (-(1)) qubit_1)) k)
    with (qv_add (state_at qubit_0 k) (qv_scale (-(1)) (state_at qubit_1 k))).
  rewrite qv_add_nth; [| lia].
  rewrite qv_scale_nth; [| lia].
  rewrite qubit_0_component_1, qubit_1_component_1. ring.
Qed.

(** Helper: dot_product for dim=2 vectors *)
Lemma dot_product_2 : forall (v w : QVec 2),
  dot_product v w == qv_nth v 0 * qv_nth w 0 + qv_nth v 1 * qv_nth w 1.
Proof.
  intros v w.
  unfold dot_product, qv_nth.
  destruct v as [vd Hvlen]. destruct w as [wd Hwlen]. simpl in *.
  destruct vd as [| v0 [| v1 [| v2 vrest]]]; simpl in Hvlen; try lia.
  destruct wd as [| w0 [| w1 [| w2 wrest]]]; simpl in Hwlen; try lia.
  simpl. ring.
Qed.

(** Eigenstate eigenvalue compatibility:
    if l1 == l2 and A|ψ⟩ → l1|ψ⟩, then A|ψ⟩ → l2|ψ⟩ *)
Lemma eigenstate_eigenvalue_compat : forall {dim} (A : QObservable dim)
  (psi : QState dim) (l1 l2 : Q),
  l1 == l2 -> is_eigenstate A psi l1 -> is_eigenstate A psi l2.
Proof.
  intros dim A psi l1 l2 Heq H1 i Hi eps Heps.
  destruct (H1 i Hi eps Heps) as [N HN].
  exists N. intros k Hk.
  specialize (HN k Hk).
  assert (Hdiff : qv_nth (obs_action_at A psi k) i - l2 * qv_nth (state_at psi k) i ==
                  qv_nth (obs_action_at A psi k) i - l1 * qv_nth (state_at psi k) i).
  { rewrite Heq. reflexivity. }
  assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs. exact HN.
Qed.

(* ========================================================================= *)
(*  PART II: PAULI-Z (DIAGONAL)                                             *)
(* ========================================================================= *)

(** Pauli-Z eigenvalues: +1, -1 *)
Definition pauli_z_eigenvals : QVec 2 :=
  mkQVec [1; -(1)] eq_refl.

(** Pauli-Z observable *)
Definition pauli_z : QObservable 2 := diag_observable pauli_z_eigenvals.

(** Pauli-Z eigenvalue access *)
Lemma pauli_z_eigenval_0 : qv_nth pauli_z_eigenvals 0 == 1.
Proof. unfold qv_nth, pauli_z_eigenvals. simpl. reflexivity. Qed.

Lemma pauli_z_eigenval_1 : qv_nth pauli_z_eigenvals 1 == -(1).
Proof. unfold qv_nth, pauli_z_eigenvals. simpl. reflexivity. Qed.

(** |0⟩ is eigenstate of σ_z with eigenvalue +1 *)
Theorem pauli_z_eigenstate_0 : is_eigenstate pauli_z qubit_0 1.
Proof.
  apply (eigenstate_eigenvalue_compat pauli_z qubit_0
    (qv_nth pauli_z_eigenvals 0) 1 pauli_z_eigenval_0).
  unfold pauli_z, qubit_0.
  apply diag_eigenstate. lia.
Qed.

(** |1⟩ is eigenstate of σ_z with eigenvalue -1 *)
Theorem pauli_z_eigenstate_1 : is_eigenstate pauli_z qubit_1 (-(1)).
Proof.
  apply (eigenstate_eigenvalue_compat pauli_z qubit_1
    (qv_nth pauli_z_eigenvals 1) (-(1)) pauli_z_eigenval_1).
  unfold pauli_z, qubit_1.
  apply diag_eigenstate. lia.
Qed.

(** ⟨0|σ_z|0⟩ = 1 *)
Lemma expectation_z_0 : forall k,
  born_expectation_at pauli_z qubit_0 k == 1.
Proof.
  intros k. unfold pauli_z, qubit_0.
  rewrite expectation_diag_basis; [| lia].
  apply pauli_z_eigenval_0.
Qed.

(** ⟨1|σ_z|1⟩ = -1 *)
Lemma expectation_z_1 : forall k,
  born_expectation_at pauli_z qubit_1 k == -(1).
Proof.
  intros k. unfold pauli_z, qubit_1.
  rewrite expectation_diag_basis; [| lia].
  apply pauli_z_eigenval_1.
Qed.

(* ========================================================================= *)
(*  PART III: PAULI-X (NON-DIAGONAL)                                        *)
(* ========================================================================= *)

(** Sigma_x matrix rows *)
Definition sigma_x_row_0 : QVec 2 := mkQVec [0; 1] eq_refl.
Definition sigma_x_row_1 : QVec 2 := mkQVec [1; 0] eq_refl.

(** Sigma_x matrix *)
Definition sigma_x_mat : QMat 2 2 :=
  mkQMat [sigma_x_row_0; sigma_x_row_1] eq_refl.

(** Entry lemmas *)
Lemma sigma_x_entry_00 : mat_entry sigma_x_mat 0 0 == 0.
Proof. unfold mat_entry, mat_row, sigma_x_mat, sigma_x_row_0. simpl. reflexivity. Qed.

Lemma sigma_x_entry_01 : mat_entry sigma_x_mat 0 1 == 1.
Proof. unfold mat_entry, mat_row, sigma_x_mat, sigma_x_row_0. simpl. reflexivity. Qed.

Lemma sigma_x_entry_10 : mat_entry sigma_x_mat 1 0 == 1.
Proof. unfold mat_entry, mat_row, sigma_x_mat, sigma_x_row_1. simpl. reflexivity. Qed.

Lemma sigma_x_entry_11 : mat_entry sigma_x_mat 1 1 == 0.
Proof. unfold mat_entry, mat_row, sigma_x_mat, sigma_x_row_1. simpl. reflexivity. Qed.

(** Sigma_x is symmetric *)
Lemma sigma_x_symmetric : is_symmetric sigma_x_mat.
Proof.
  intros i j Hi Hj.
  destruct i as [| [| ?]]; [| | lia];
  destruct j as [| [| ?]]; try lia.
  - reflexivity.
  - rewrite sigma_x_entry_01, sigma_x_entry_10. reflexivity.
  - rewrite sigma_x_entry_10, sigma_x_entry_01. reflexivity.
  - reflexivity.
Qed.

(** Pauli-X observable *)
Definition pauli_x : QObservable 2.
Proof.
  refine (mkQObservable 2 (fun _ => sigma_x_mat) _ _).
  - intro k. exact sigma_x_symmetric.
  - intros i j Hi Hj eps Heps.
    exists 0%nat. intros m p _ _.
    setoid_replace (mat_entry sigma_x_mat i j - mat_entry sigma_x_mat i j)
      with 0 by ring.
    rewrite Qabs_pos; lra.
Defined.

(** Pauli-X action on |0⟩ gives |1⟩ *)
Lemma pauli_x_action_0 : forall k i,
  (i < 2)%nat ->
  qv_nth (obs_action_at pauli_x qubit_0 k) i ==
  qv_nth (state_at qubit_1 k) i.
Proof.
  intros k i Hi.
  unfold obs_action_at.
  change (obs_at pauli_x k) with sigma_x_mat.
  change (state_at qubit_0 k) with (basis_vec 2 0).
  change (state_at qubit_1 k) with (basis_vec 2 1).
  rewrite mat_vec_mul_nth; [| exact Hi].
  destruct i as [| [| ?]]; [| | lia].
  - (* i = 0: dot(row0, bv0) == bv1[0] *)
    change (mat_row sigma_x_mat 0) with sigma_x_row_0.
    rewrite dot_product_2.
    change (qv_nth sigma_x_row_0 0) with 0.
    change (qv_nth sigma_x_row_0 1) with 1.
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    ring.
  - (* i = 1: dot(row1, bv0) == bv1[1] *)
    change (mat_row sigma_x_mat 1) with sigma_x_row_1.
    rewrite dot_product_2.
    change (qv_nth sigma_x_row_1 0) with 1.
    change (qv_nth sigma_x_row_1 1) with 0.
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    ring.
Qed.

(** Pauli-X action on |1⟩ gives |0⟩ *)
Lemma pauli_x_action_1 : forall k i,
  (i < 2)%nat ->
  qv_nth (obs_action_at pauli_x qubit_1 k) i ==
  qv_nth (state_at qubit_0 k) i.
Proof.
  intros k i Hi.
  unfold obs_action_at.
  change (obs_at pauli_x k) with sigma_x_mat.
  change (state_at qubit_1 k) with (basis_vec 2 1).
  change (state_at qubit_0 k) with (basis_vec 2 0).
  rewrite mat_vec_mul_nth; [| exact Hi].
  destruct i as [| [| ?]]; [| | lia].
  - (* i = 0: dot(row0, bv1) == bv0[0] *)
    change (mat_row sigma_x_mat 0) with sigma_x_row_0.
    rewrite dot_product_2.
    change (qv_nth sigma_x_row_0 0) with 0.
    change (qv_nth sigma_x_row_0 1) with 1.
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    rewrite (basis_vec_same 2 0); [| lia].
    ring.
  - (* i = 1: dot(row1, bv1) == bv0[1] *)
    change (mat_row sigma_x_mat 1) with sigma_x_row_1.
    rewrite dot_product_2.
    change (qv_nth sigma_x_row_1 0) with 1.
    change (qv_nth sigma_x_row_1 1) with 0.
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    ring.
Qed.

(** |+⟩ is eigenstate of σ_x with eigenvalue +1 *)
Theorem pauli_x_eigenstate_plus : is_eigenstate pauli_x qubit_plus 1.
Proof.
  intros i Hi eps Heps.
  exists 0%nat. intros k _.
  unfold obs_action_at.
  change (obs_at pauli_x k) with sigma_x_mat.
  unfold qubit_plus.
  change (state_at (state_add qubit_0 qubit_1) k)
    with (qv_add (state_at qubit_0 k) (state_at qubit_1 k)).
  change (state_at qubit_0 k) with (basis_vec 2 0).
  change (state_at qubit_1 k) with (basis_vec 2 1).
  rewrite mat_vec_mul_nth; [| exact Hi].
  rewrite dot_product_add_r.
  destruct i as [| [| ?]]; [| | lia].
  - (* i = 0 *)
    change (mat_row sigma_x_mat 0) with sigma_x_row_0.
    rewrite !dot_product_2.
    change (qv_nth sigma_x_row_0 0) with 0.
    change (qv_nth sigma_x_row_0 1) with 1.
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    rewrite qv_add_nth; [| lia].
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    assert (H : 0 * 1 + 1 * 0 + (0 * 0 + 1 * 1) - 1 * (1 + 0) == 0) by ring.
    qabs_rw H. rewrite Qabs_pos; lra.
  - (* i = 1 *)
    change (mat_row sigma_x_mat 1) with sigma_x_row_1.
    rewrite !dot_product_2.
    change (qv_nth sigma_x_row_1 0) with 1.
    change (qv_nth sigma_x_row_1 1) with 0.
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    rewrite qv_add_nth; [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    assert (H : 1 * 1 + 0 * 0 + (1 * 0 + 0 * 1) - 1 * (0 + 1) == 0) by ring.
    qabs_rw H. rewrite Qabs_pos; lra.
Qed.

(** |−⟩ is eigenstate of σ_x with eigenvalue -1 *)
Theorem pauli_x_eigenstate_minus : is_eigenstate pauli_x qubit_minus (-(1)).
Proof.
  intros i Hi eps Heps.
  exists 0%nat. intros k _.
  unfold obs_action_at.
  change (obs_at pauli_x k) with sigma_x_mat.
  unfold qubit_minus.
  change (state_at (state_add qubit_0 (state_scale (-(1)) qubit_1)) k)
    with (qv_add (state_at qubit_0 k) (qv_scale (-(1)) (state_at qubit_1 k))).
  change (state_at qubit_0 k) with (basis_vec 2 0).
  change (state_at qubit_1 k) with (basis_vec 2 1).
  rewrite mat_vec_mul_nth; [| exact Hi].
  rewrite dot_product_add_r.
  rewrite dot_product_scale_r.
  destruct i as [| [| ?]]; [| | lia].
  - (* i = 0 *)
    change (mat_row sigma_x_mat 0) with sigma_x_row_0.
    rewrite !dot_product_2.
    change (qv_nth sigma_x_row_0 0) with 0.
    change (qv_nth sigma_x_row_0 1) with 1.
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    rewrite qv_add_nth; [| lia].
    rewrite qv_scale_nth; [| lia].
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    assert (H : 0 * 1 + 1 * 0 + -(1) * (0 * 0 + 1 * 1) -
      -(1) * (1 + -(1) * 0) == 0) by ring.
    qabs_rw H. rewrite Qabs_pos; lra.
  - (* i = 1 *)
    change (mat_row sigma_x_mat 1) with sigma_x_row_1.
    rewrite !dot_product_2.
    change (qv_nth sigma_x_row_1 0) with 1.
    change (qv_nth sigma_x_row_1 1) with 0.
    rewrite (basis_vec_same 2 0); [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_diff 2 0 1); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    rewrite qv_add_nth; [| lia].
    rewrite qv_scale_nth; [| lia].
    rewrite (basis_vec_diff 2 1 0); [| lia | lia].
    rewrite (basis_vec_same 2 1); [| lia].
    assert (H : 1 * 1 + 0 * 0 + -(1) * (1 * 0 + 0 * 1) -
      -(1) * (0 + -(1) * 1) == 0) by ring.
    qabs_rw H. rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(*  PART IV: BORN PROBABILITIES                                             *)
(* ========================================================================= *)

(** Normalized Born probability: P(psi→phi) = |⟨psi|phi⟩|² / ⟨phi|phi⟩ *)
Definition normalized_prob {dim} (psi phi : QState dim) (k : nat) : Q :=
  born_prob_at psi phi k / state_ip_at phi phi k.

(** |+⟩ norm squared = 2 *)
Lemma qubit_plus_norm_sq : forall k,
  state_ip_at qubit_plus qubit_plus k == 2.
Proof.
  intros k. unfold state_ip_at.
  rewrite dot_product_2.
  rewrite qubit_plus_component_0, qubit_plus_component_1.
  ring.
Qed.

(** |−⟩ norm squared = 2 *)
Lemma qubit_minus_norm_sq : forall k,
  state_ip_at qubit_minus qubit_minus k == 2.
Proof.
  intros k. unfold state_ip_at.
  rewrite dot_product_2.
  rewrite qubit_minus_component_0, qubit_minus_component_1.
  ring.
Qed.

(** ⟨0|+⟩ = 1 *)
Lemma ip_0_plus : forall k,
  state_ip_at qubit_0 qubit_plus k == 1.
Proof.
  intros k. unfold state_ip_at.
  rewrite dot_product_2.
  rewrite qubit_0_component_0, qubit_0_component_1.
  rewrite qubit_plus_component_0, qubit_plus_component_1.
  ring.
Qed.

(** ⟨1|+⟩ = 1 *)
Lemma ip_1_plus : forall k,
  state_ip_at qubit_1 qubit_plus k == 1.
Proof.
  intros k. unfold state_ip_at.
  rewrite dot_product_2.
  rewrite qubit_1_component_0, qubit_1_component_1.
  rewrite qubit_plus_component_0, qubit_plus_component_1.
  ring.
Qed.

(** Self-probability: P(|0⟩ → |0⟩) = 1 *)
Lemma born_self_qubit_0 : forall k,
  born_prob_at qubit_0 qubit_0 k == 1.
Proof.
  intros k. unfold qubit_0. apply born_self_basis. lia.
Qed.

(** Orthogonal probability: P(|0⟩ → |1⟩) = 0 *)
Lemma born_orthogonal_01 : forall k,
  born_prob_at qubit_0 qubit_1 k == 0.
Proof.
  intros k. unfold qubit_0, qubit_1. apply born_orthogonal_at; lia.
Qed.

(** ★★★ THE KEY RESULT: Equal superposition probability ★★★
    Probability of measuring |0⟩ in |+⟩ = 1/2 *)
Theorem qubit_equal_superposition : forall k,
  normalized_prob qubit_0 qubit_plus k == (1#2).
Proof.
  intros k. unfold normalized_prob.
  unfold born_prob_at.
  rewrite ip_0_plus, qubit_plus_norm_sq.
  field.
Qed.

(** Probability of measuring |1⟩ in |+⟩ = 1/2 *)
Theorem qubit_equal_superposition_1 : forall k,
  normalized_prob qubit_1 qubit_plus k == (1#2).
Proof.
  intros k. unfold normalized_prob.
  unfold born_prob_at.
  rewrite ip_1_plus, qubit_plus_norm_sq.
  field.
Qed.

(** Probabilities sum to 1 *)
Theorem qubit_prob_sum : forall k,
  normalized_prob qubit_0 qubit_plus k +
  normalized_prob qubit_1 qubit_plus k == 1.
Proof.
  intros k. rewrite qubit_equal_superposition, qubit_equal_superposition_1.
  ring.
Qed.

(* ========================================================================= *)
(*  PART V: EXPECTATION VALUES                                              *)
(* ========================================================================= *)

(** Helper: reduce diagonal matrix entries to concrete values *)
Lemma pauli_z_mat_entry_00 :
  qv_nth (mat_row (diag_mat pauli_z_eigenvals) 0) 0 == 1.
Proof.
  change (mat_entry (diag_mat pauli_z_eigenvals) 0 0 == 1).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 0 0); [| congruence]. apply pauli_z_eigenval_0.
Qed.

Lemma pauli_z_mat_entry_01 :
  qv_nth (mat_row (diag_mat pauli_z_eigenvals) 0) 1 == 0.
Proof.
  change (mat_entry (diag_mat pauli_z_eigenvals) 0 1 == 0).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 0 1); [lia |]. reflexivity.
Qed.

Lemma pauli_z_mat_entry_10 :
  qv_nth (mat_row (diag_mat pauli_z_eigenvals) 1) 0 == 0.
Proof.
  change (mat_entry (diag_mat pauli_z_eigenvals) 1 0 == 0).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 1 0); [lia |]. reflexivity.
Qed.

Lemma pauli_z_mat_entry_11 :
  qv_nth (mat_row (diag_mat pauli_z_eigenvals) 1) 1 == -(1).
Proof.
  change (mat_entry (diag_mat pauli_z_eigenvals) 1 1 == -(1)).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 1 1); [| congruence]. apply pauli_z_eigenval_1.
Qed.

(** ⟨+|σ_z|+⟩ = 0 — maximally uncertain *)
Theorem expectation_z_plus : forall k,
  born_expectation_at pauli_z qubit_plus k == 0.
Proof.
  intros k. unfold born_expectation_at, obs_action_at.
  rewrite dot_product_2.
  rewrite qubit_plus_component_0, qubit_plus_component_1.
  change (obs_at pauli_z k) with (diag_mat pauli_z_eigenvals).
  set (Mz := diag_mat pauli_z_eigenvals).
  rewrite !mat_vec_mul_nth; try lia.
  rewrite !dot_product_2.
  rewrite !qubit_plus_component_0, !qubit_plus_component_1.
  subst Mz.
  rewrite pauli_z_mat_entry_00, pauli_z_mat_entry_01,
          pauli_z_mat_entry_10, pauli_z_mat_entry_11.
  ring.
Qed.

(** ⟨−|σ_z|−⟩ = 0 — also maximally uncertain *)
Theorem expectation_z_minus : forall k,
  born_expectation_at pauli_z qubit_minus k == 0.
Proof.
  intros k. unfold born_expectation_at, obs_action_at.
  rewrite dot_product_2.
  rewrite qubit_minus_component_0, qubit_minus_component_1.
  change (obs_at pauli_z k) with (diag_mat pauli_z_eigenvals).
  set (Mz := diag_mat pauli_z_eigenvals).
  rewrite !mat_vec_mul_nth; try lia.
  rewrite !dot_product_2.
  rewrite !qubit_minus_component_0, !qubit_minus_component_1.
  subst Mz.
  rewrite pauli_z_mat_entry_00, pauli_z_mat_entry_01,
          pauli_z_mat_entry_10, pauli_z_mat_entry_11.
  ring.
Qed.

(** Complementarity: Z-basis measurement is certain, X-expectation is 0 *)
Theorem complementarity_z_x : forall k,
  born_expectation_at pauli_z qubit_0 k == 1 /\
  born_expectation_at pauli_z qubit_plus k == 0.
Proof.
  intros k. split.
  - apply expectation_z_0.
  - apply expectation_z_plus.
Qed.

(** Basis measurement completeness: |0⟩ and |1⟩ are the only eigenstates *)
Theorem z_basis_measurement_complete : forall k,
  normalized_prob qubit_0 qubit_plus k +
  normalized_prob qubit_1 qubit_plus k == 1 /\
  born_expectation_at pauli_z qubit_plus k == 0.
Proof.
  intros k. split.
  - apply qubit_prob_sum.
  - apply expectation_z_plus.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

(** Summary:
    Qubit.v: Concrete single-qubit quantum mechanics.

    Part I: States + Helpers
    - qubit_0, qubit_1, qubit_plus, qubit_minus
    - Component lemmas (8)
    - dot_product_2, eigenstate_eigenvalue_compat

    Part II: Pauli-Z (diagonal)
    - pauli_z_eigenvals, pauli_z, eigenvalue access
    - pauli_z_eigenstate_0/1, expectation_z_0/1

    Part III: Pauli-X (non-diagonal)
    - sigma_x_mat, sigma_x_symmetric, pauli_x
    - pauli_x_action_0/1
    - pauli_x_eigenstate_plus (+1), pauli_x_eigenstate_minus (-1)

    Part IV: Born Probabilities
    - normalized_prob, qubit_plus/minus_norm_sq
    - ★ qubit_equal_superposition: P(|0⟩→|+⟩) = 1/2
    - qubit_prob_sum: probabilities sum to 1

    Part V: Expectation Values
    - expectation_z_plus/minus = 0 (maximally uncertain)
    - complementarity_z_x, z_basis_measurement_complete
*)
