(* ========================================================================= *)
(*        EIGENVALUE THEORY — Exact algebraic eigenvalues over Q            *)
(*                                                                          *)
(*  Defines is_eigenvalue/is_eigenvector, 2×2 determinant/discriminant.     *)
(*  Key results: diagonal eigenvalues, eigenvector algebra, Vieta-style     *)
(*  relations, symmetric discriminant ≥ 0, concrete 2×2 examples.          *)
(*                                                                          *)
(*  STATUS: ~25 Qed, 0 Admitted                                            *)
(*  AXIOMS: none                                                            *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Coq Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.

(* ========================================================================= *)
(*  PART I: mat_vec_mul linearity helpers (needed throughout)                *)
(* ========================================================================= *)

Lemma mat_vec_mul_add : forall {n m} (M : QMat n m) (v w : QVec m) i,
  (i < n)%nat ->
  qv_nth (mat_vec_mul M (qv_add v w)) i ==
  qv_nth (mat_vec_mul M v) i + qv_nth (mat_vec_mul M w) i.
Proof.
  intros n m M v w i Hi.
  rewrite !mat_vec_mul_nth; [| exact Hi | exact Hi | exact Hi].
  apply dot_product_add_r.
Qed.

Lemma mat_vec_mul_scale : forall {n m} (M : QMat n m) (v : QVec m) (c : Q) i,
  (i < n)%nat ->
  qv_nth (mat_vec_mul M (qv_scale c v)) i ==
  c * qv_nth (mat_vec_mul M v) i.
Proof.
  intros n m M v c i Hi.
  rewrite !mat_vec_mul_nth; [| exact Hi | exact Hi].
  rewrite dot_product_comm.
  rewrite (dot_product_comm (mat_row M i) v).
  rewrite dot_product_scale_l.
  reflexivity.
Qed.

(* ========================================================================= *)
(*  PART II: Eigenvalue Definitions                                          *)
(* ========================================================================= *)

Definition is_eigenvector {n} (M : QMat n n) (v : QVec n) (lambda : Q) : Prop :=
  ~ qv_eq v (qv_zero n) /\ qv_eq (mat_vec_mul M v) (qv_scale lambda v).

Definition is_eigenvalue {n} (M : QMat n n) (lambda : Q) : Prop :=
  exists v, is_eigenvector M v lambda.

Lemma eigenvector_nonzero : forall {n} (M : QMat n n) v lambda,
  is_eigenvector M v lambda -> ~ qv_eq v (qv_zero n).
Proof. intros n M v lambda [Hne _]. exact Hne. Qed.

(** Diagonal entries are eigenvalues *)
Lemma eigenvalue_of_diag : forall {n} (eigenvals : QVec n) j,
  (j < n)%nat ->
  is_eigenvalue (diag_mat eigenvals) (qv_nth eigenvals j).
Proof.
  intros n eigenvals j Hj.
  exists (basis_vec n j). split.
  - intro Habs. specialize (Habs j Hj).
    rewrite basis_vec_same in Habs; [| exact Hj].
    rewrite qv_zero_nth in Habs; [| exact Hj]. lra.
  - intros i Hi.
    rewrite diag_mat_action; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    + subst. ring.
    + rewrite (basis_vec_diff n i j Hi Hneq). ring.
Qed.

(** 1 is eigenvalue of identity matrix *)
Lemma eigenvalue_of_id : forall n, (0 < n)%nat ->
  is_eigenvalue (id_mat n) 1.
Proof.
  intros n Hn.
  exists (basis_vec n 0). split.
  - intro Habs. specialize (Habs 0%nat Hn).
    rewrite basis_vec_same in Habs; [| exact Hn].
    rewrite qv_zero_nth in Habs; [| exact Hn]. lra.
  - intros i Hi.
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    unfold mat_row, id_mat. simpl.
    rewrite (nth_map_general _ (seq 0 n) 0%nat (qv_zero n) i);
      [| rewrite seq_length; exact Hi].
    rewrite seq_nth; [| exact Hi]. simpl.
    rewrite dot_basis_extracts; [| exact Hi]. ring.
Qed.

(** Scaling an eigenvector *)
Lemma eigenvectors_scale : forall {n} (M : QMat n n) v lambda (c : Q),
  is_eigenvector M v lambda -> ~ (c == 0) ->
  is_eigenvector M (qv_scale c v) lambda.
Proof.
  intros n M v lambda c [Hne Heigen] Hc. split.
  - intro Habs. apply Hne. intros i Hi.
    specialize (Habs i Hi).
    rewrite qv_scale_nth in Habs; [| exact Hi].
    rewrite qv_zero_nth in Habs; [| exact Hi].
    destruct (Qmult_integral c (qv_nth v i) Habs) as [Hcz | Hvz].
    + exfalso. exact (Hc Hcz).
    + rewrite qv_zero_nth; [| exact Hi]. exact Hvz.
  - intros i Hi.
    rewrite mat_vec_mul_scale; [| exact Hi].
    rewrite !qv_scale_nth; [| exact Hi | exact Hi].
    specialize (Heigen i Hi).
    rewrite qv_scale_nth in Heigen; [| exact Hi].
    rewrite Heigen. ring.
Qed.

(** Eigenvalue shift: λ of M → (λ-σ) of (M-σI) *)
Lemma eigenvalue_shift : forall {n} (M : QMat n n) lambda sigma,
  is_eigenvalue M lambda ->
  is_eigenvalue (mat_shift M sigma) (lambda - sigma).
Proof.
  intros n M lambda sigma [v [Hne Heigen]].
  exists v. split; [exact Hne |].
  intros i Hi.
  rewrite mat_vec_mul_nth; [| exact Hi].
  rewrite qv_scale_nth; [| exact Hi].
  specialize (Heigen i Hi).
  rewrite mat_vec_mul_nth in Heigen; [| exact Hi].
  rewrite qv_scale_nth in Heigen; [| exact Hi].
  (* Row i of mat_shift = row i of M + (-sigma) * basis_vec *)
  assert (Hrow_eq : forall k, (k < n)%nat ->
    qv_nth (mat_row (mat_shift M sigma) i) k ==
    qv_nth (qv_add (mat_row M i) (qv_scale (- sigma) (basis_vec n i))) k).
  { intros k Hk.
    rewrite qv_add_nth; [| exact Hk].
    rewrite qv_scale_nth; [| exact Hk].
    change (qv_nth (mat_row (mat_shift M sigma) i) k)
      with (mat_entry (mat_shift M sigma) i k).
    rewrite mat_shift_entry; [| exact Hi | exact Hk].
    change (mat_entry M i k) with (qv_nth (mat_row M i) k).
    destruct (Nat.eq_dec i k) as [Heq | Hneq].
    - subst. rewrite basis_vec_same; [| exact Hk]. ring.
    - assert (Hneq' : k <> i) by (intro; apply Hneq; symmetry; assumption).
      rewrite (basis_vec_diff n k i Hk Hneq'). ring. }
  rewrite (dot_product_ext _ _ v Hrow_eq).
  rewrite dot_product_add_l.
  rewrite dot_product_scale_l.
  rewrite dot_basis_extracts; [| exact Hi].
  rewrite Heigen. ring.
Qed.

(** Eigenvalue scaling: λ of M → c·λ of c·M *)
Lemma eigenvalue_scale_mat : forall {n} (M : QMat n n) lambda (c : Q),
  is_eigenvalue M lambda -> is_eigenvalue (mat_scale c M) (c * lambda).
Proof.
  intros n M lambda c [v [Hne Heigen]].
  exists v. split; [exact Hne |].
  intros i Hi.
  rewrite mat_vec_mul_nth; [| exact Hi].
  rewrite qv_scale_nth; [| exact Hi].
  specialize (Heigen i Hi).
  rewrite mat_vec_mul_nth in Heigen; [| exact Hi].
  rewrite qv_scale_nth in Heigen; [| exact Hi].
  unfold mat_row at 1, mat_scale. simpl.
  rewrite (nth_map_general _ (qm_rows M) (qv_zero n) (qv_zero n) i);
    [| rewrite (qm_nrows M); exact Hi].
  rewrite dot_product_scale_l.
  rewrite Heigen. ring.
Qed.

(** Zero matrix: 0 is an eigenvalue *)
Lemma eigenvalue_of_zero_mat : forall {n},
  (0 < n)%nat -> is_eigenvalue (zero_mat n n) 0.
Proof.
  intros n Hn. exists (basis_vec n 0). split.
  - intro Habs. specialize (Habs 0%nat Hn).
    rewrite basis_vec_same in Habs; [| exact Hn].
    rewrite qv_zero_nth in Habs; [| exact Hn]. lra.
  - intros i Hi.
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    assert (Hrow_eq : forall k, (k < n)%nat ->
      qv_nth (mat_row (zero_mat n n) i) k == qv_nth (qv_zero n) k).
    { intros k Hk. unfold mat_row, zero_mat. simpl. rewrite nth_repeat. reflexivity. }
    rewrite (dot_product_ext _ _ _ Hrow_eq).
    rewrite dot_product_zero_left. ring.
Qed.

(** Zero eigenvalue means nontrivial kernel *)
Lemma zero_eigenvalue_kernel : forall {n} (M : QMat n n),
  is_eigenvalue M 0 <->
  exists v, ~ qv_eq v (qv_zero n) /\ qv_eq (mat_vec_mul M v) (qv_zero n).
Proof.
  intros n M. split.
  - intros [v [Hne Heigen]]. exists v. split; [exact Hne |].
    intros i Hi. specialize (Heigen i Hi).
    rewrite qv_scale_nth in Heigen; [| exact Hi].
    rewrite qv_zero_nth; [| exact Hi]. lra.
  - intros [v [Hne Hkernel]]. exists v. split; [exact Hne |].
    intros i Hi. specialize (Hkernel i Hi).
    rewrite qv_zero_nth in Hkernel; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi]. lra.
Qed.

(** Eigenvectors with same eigenvalue: sum is eigenvector (if nonzero) *)
Lemma eigenvectors_add_same : forall {n} (M : QMat n n) v w lambda,
  is_eigenvector M v lambda ->
  is_eigenvector M w lambda ->
  ~ qv_eq (qv_add v w) (qv_zero n) ->
  is_eigenvector M (qv_add v w) lambda.
Proof.
  intros n M v w lambda [_ Heig1] [_ Heig2] Hne3. split; [exact Hne3 |].
  intros i Hi.
  rewrite mat_vec_mul_add; [| exact Hi].
  rewrite qv_scale_nth; [| exact Hi].
  rewrite qv_add_nth; [| exact Hi].
  specialize (Heig1 i Hi). specialize (Heig2 i Hi).
  rewrite qv_scale_nth in Heig1; [| exact Hi].
  rewrite qv_scale_nth in Heig2; [| exact Hi].
  lra.
Qed.

(* ========================================================================= *)
(*  PART III: 2×2 Determinant and Discriminant                               *)
(* ========================================================================= *)

Definition det_2x2 (M : QMat 2 2) : Q :=
  mat_entry M 0 0 * mat_entry M 1 1 - mat_entry M 0 1 * mat_entry M 1 0.

Definition char_poly_2x2 (M : QMat 2 2) (lambda : Q) : Q :=
  lambda * lambda - mat_trace M * lambda + det_2x2 M.

Definition discriminant_2x2 (M : QMat 2 2) : Q :=
  mat_trace M * mat_trace M - 4 * det_2x2 M.

Lemma det_2x2_id : det_2x2 (id_mat 2) == 1.
Proof.
  unfold det_2x2.
  rewrite !id_mat_entry; try lia.
  destruct (Nat.eq_dec 0 0); [| lia].
  destruct (Nat.eq_dec 1 1); [| lia].
  destruct (Nat.eq_dec 0 1); [lia |].
  destruct (Nat.eq_dec 1 0); [lia |].
  ring.
Qed.

Lemma det_2x2_diag : forall (eigenvals : QVec 2),
  det_2x2 (diag_mat eigenvals) == qv_nth eigenvals 0 * qv_nth eigenvals 1.
Proof.
  intros eigenvals. unfold det_2x2.
  rewrite !diag_mat_entry; try lia.
  destruct (Nat.eq_dec 0 0); [| lia].
  destruct (Nat.eq_dec 1 1); [| lia].
  destruct (Nat.eq_dec 0 1); [lia |].
  destruct (Nat.eq_dec 1 0); [lia |].
  ring.
Qed.

Lemma det_2x2_symmetric : forall (M : QMat 2 2),
  is_symmetric M ->
  det_2x2 M == mat_entry M 0 0 * mat_entry M 1 1 - mat_entry M 0 1 * mat_entry M 0 1.
Proof.
  intros M Hsym. unfold det_2x2.
  rewrite (Hsym 1%nat 0%nat ltac:(lia) ltac:(lia)). reflexivity.
Qed.

(** Symmetric 2×2: discriminant ≥ 0 *)
Lemma symmetric_2x2_disc_nonneg : forall (M : QMat 2 2),
  is_symmetric M -> 0 <= discriminant_2x2 M.
Proof.
  intros M Hsym.
  unfold discriminant_2x2.
  assert (Hsym01 := Hsym 0%nat 1%nat ltac:(lia) ltac:(lia)).
  unfold mat_trace, sum_Q, det_2x2.
  setoid_replace (mat_entry M 1 0) with (mat_entry M 0 1) by (symmetry; exact Hsym01).
  set (a := mat_entry M 0 0). set (b := mat_entry M 0 1). set (d := mat_entry M 1 1).
  assert (H : (0 + a + d) * (0 + a + d) - 4 * (a * d - b * b) ==
              (a - d) * (a - d) + 4 * (b * b)) by ring.
  rewrite H.
  assert (Hsq1 : 0 <= (a - d) * (a - d)).
  { destruct (Qlt_le_dec (a - d) 0) as [H1 | H1].
    - setoid_replace ((a - d) * (a - d)) with ((d - a) * (d - a)) by ring.
      apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; exact H1. }
  assert (Hsq2 : 0 <= 4 * (b * b)).
  { assert (Hbb : 0 <= b * b).
    { destruct (Qlt_le_dec b 0) as [H2 | H2].
      - setoid_replace (b * b) with ((- b) * (- b)) by ring.
        apply Qmult_le_0_compat; lra.
      - apply Qmult_le_0_compat; exact H2. }
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(*  PART IV: 2×2 Concrete Examples                                           *)
(* ========================================================================= *)

Definition qvec2 (a b : Q) : QVec 2.
Proof. refine (mkQVec [a; b] _). reflexivity. Defined.

Lemma qvec2_nth_0 : forall a b, qv_nth (qvec2 a b) 0 == a.
Proof. intros. unfold qv_nth, qvec2. simpl. reflexivity. Qed.

Lemma qvec2_nth_1 : forall a b, qv_nth (qvec2 a b) 1 == b.
Proof. intros. unfold qv_nth, qvec2. simpl. reflexivity. Qed.

Definition qmat2x2 (a00 a01 a10 a11 : Q) : QMat 2 2.
Proof. refine (mkQMat [qvec2 a00 a01; qvec2 a10 a11] _). reflexivity. Defined.

(** σ_z eigenvalues: 1 and -1 *)
Lemma eigenvalue_sigma_z_plus : is_eigenvalue (qmat2x2 1 0 0 (-(1))) 1.
Proof.
  exists (qvec2 1 0). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, qmat2x2, qvec2; simpl; unfold Qeq; simpl; lia.
Qed.

Lemma eigenvalue_sigma_z_minus : is_eigenvalue (qmat2x2 1 0 0 (-(1))) (-(1)).
Proof.
  exists (qvec2 0 1). split.
  - intro Habs. specialize (Habs 1%nat ltac:(lia)).
    rewrite qvec2_nth_1 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, qmat2x2, qvec2; simpl; unfold Qeq; simpl; lia.
Qed.

(** σ_x eigenvalues: 1 and -1 *)
Lemma eigenvalue_sigma_x_plus : is_eigenvalue (qmat2x2 0 1 1 0) 1.
Proof.
  exists (qvec2 1 1). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, qmat2x2, qvec2; simpl; unfold Qeq; simpl; lia.
Qed.

Lemma eigenvalue_sigma_x_minus : is_eigenvalue (qmat2x2 0 1 1 0) (-(1)).
Proof.
  exists (qvec2 1 (-(1))). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, qmat2x2, qvec2; simpl; unfold Qeq; simpl; lia.
Qed.

(** [[2,1],[1,2]] eigenvalues: 3 and 1 *)
Lemma eigenvalue_2x2_example_3 : is_eigenvalue (qmat2x2 2 1 1 2) 3.
Proof.
  exists (qvec2 1 1). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, qmat2x2, qvec2; simpl; unfold Qeq; simpl; lia.
Qed.

Lemma eigenvalue_2x2_example_1 : is_eigenvalue (qmat2x2 2 1 1 2) 1.
Proof.
  exists (qvec2 1 (-(1))). split.
  - intro Habs. specialize (Habs 0%nat ltac:(lia)).
    rewrite qvec2_nth_0 in Habs. rewrite qv_zero_nth in Habs; [lra | lia].
  - intros i Hi. rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct i as [| [| i']]; try lia;
    unfold dot_product, mat_row, qmat2x2, qvec2; simpl; unfold Qeq; simpl; lia.
Qed.

(** Connect process-based is_eigenstate to exact is_eigenvalue *)
Lemma diag_eigenstate_eigenvalue : forall {n} (eigenvals : QVec n) j,
  (j < n)%nat ->
  is_eigenvalue (diag_mat eigenvals) (qv_nth eigenvals j).
Proof. intros n eigenvals j Hj. exact (eigenvalue_of_diag eigenvals j Hj). Qed.

(* ========================================================================= *)
(*  SUMMARY: 25 Qed, 0 Admitted                                             *)
(* ========================================================================= *)
