(* ========================================================================= *)
(*        QOBSERVABLE — Quantum Observables as Symmetric Matrix Processes   *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                 *)
(*                                                                          *)
(*  An observable is a process (nat → QMat dim dim) of symmetric matrices   *)
(*  whose entries are component-wise Cauchy.  This models self-adjoint      *)
(*  operators on finite-dimensional Hilbert spaces, discretized over Q.     *)
(*                                                                          *)
(*  Elements: QObservable, matrix entry access, identity/diagonal matrices  *)
(*  Roles:    observable → measurable quantity in quantum mechanics         *)
(*  Rules:    symmetry (self-adjoint), entry-wise Cauchy convergence        *)
(*  Status:   diagonal observable | identity observable | general           *)
(*                                                                          *)
(*  STATUS: ~20 Qed, 0 Admitted                                            *)
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

(* ========================================================================= *)
(*  SECTION 1: Matrix Entry Access                                          *)
(* ========================================================================= *)

(** Access row i of a matrix *)
Definition mat_row {r c} (M : QMat r c) (i : nat) : QVec c :=
  nth i (qm_rows M) (qv_zero c).

(** Access entry (i,j) of a matrix *)
Definition mat_entry {r c} (M : QMat r c) (i j : nat) : Q :=
  qv_nth (mat_row M i) j.

(** mat_vec_mul row access *)
(** General nth-map lemma: nth of map for any types *)
Lemma nth_map_general : forall {A B : Type} (f : A -> B) (l : list A)
    (dA : A) (dB : B) (i : nat),
  (i < length l)%nat -> nth i (map f l) dB = f (nth i l dA).
Proof.
  intros A B f l dA dB. induction l as [| x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i; [reflexivity | apply IH; lia].
Qed.

Lemma nth_map_vec_Q : forall {c} (f : QVec c -> Q) (l : list (QVec c)) (i : nat),
  (i < length l)%nat ->
  nth i (map f l) 0 = f (nth i l (qv_zero c)).
Proof.
  intros c f l. induction l as [| x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i; [reflexivity | apply IH; lia].
Qed.

Lemma mat_vec_mul_nth : forall {r c} (M : QMat r c) (v : QVec c) (i : nat),
  (i < r)%nat ->
  qv_nth (mat_vec_mul M v) i == dot_product (mat_row M i) v.
Proof.
  intros r c M v i Hi.
  unfold qv_nth, mat_row.
  change (qv_data (mat_vec_mul M v)) with
    (map (fun row : QVec c => dot_product row v) (qm_rows M)).
  rewrite nth_map_vec_Q.
  - reflexivity.
  - rewrite (qm_nrows M). exact Hi.
Qed.

(* ========================================================================= *)
(*  SECTION 2: Symmetric Matrices                                           *)
(* ========================================================================= *)

(** A matrix is symmetric if M[i,j] == M[j,i] *)
Definition is_symmetric {n} (M : QMat n n) : Prop :=
  forall i j, (i < n)%nat -> (j < n)%nat -> mat_entry M i j == mat_entry M j i.

(* ========================================================================= *)
(*  SECTION 3: Observable Definition                                        *)
(* ========================================================================= *)

(** A quantum observable of dimension dim: a process of symmetric matrices
    whose entries converge (entry-wise Cauchy) *)
Record QObservable (dim : nat) := mkQObservable {
  obs_seq : nat -> QMat dim dim;
  obs_symmetric : forall k, is_symmetric (obs_seq k);
  obs_cauchy : forall i j, (i < dim)%nat -> (j < dim)%nat ->
    is_cauchy (fun k => mat_entry (obs_seq k) i j)
}.

(** Access observable matrix at step k *)
Definition obs_at {dim} (A : QObservable dim) (k : nat) : QMat dim dim :=
  obs_seq dim A k.

(** Observable action on a state vector at step k *)
Definition obs_action_at {dim} (A : QObservable dim) (s : QState dim) (k : nat) : QVec dim :=
  mat_vec_mul (obs_at A k) (state_at s k).

(** Observable symmetry at each step *)
Lemma obs_symmetric_at : forall {dim} (A : QObservable dim) k i j,
  (i < dim)%nat -> (j < dim)%nat ->
  mat_entry (obs_at A k) i j == mat_entry (obs_at A k) j i.
Proof.
  intros dim A k i j Hi Hj. unfold obs_at.
  apply (obs_symmetric dim A k). exact Hi. exact Hj.
Qed.

(* ========================================================================= *)
(*  SECTION 4: Identity Observable                                          *)
(* ========================================================================= *)

(** Identity matrix: diagonal with all 1s *)
Definition id_mat (n : nat) : QMat n n.
Proof.
  refine (mkQMat (map (fun i => basis_vec n i) (seq 0 n)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

(** Identity matrix entry *)
Lemma id_mat_entry : forall n i j,
  (i < n)%nat -> (j < n)%nat ->
  mat_entry (id_mat n) i j == (if Nat.eq_dec i j then 1 else 0).
Proof.
  intros n i j Hi Hj. unfold mat_entry, mat_row, id_mat. simpl.
  rewrite (nth_map_general (fun i => basis_vec n i) (seq 0 n) 0%nat (qv_zero n));
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  - subst i. apply basis_vec_same. exact Hj.
  - apply basis_vec_diff; [exact Hj | auto].
Qed.

(** Identity matrix is symmetric *)
Lemma id_mat_symmetric : forall n, is_symmetric (id_mat n).
Proof.
  intros n i j Hi Hj.
  rewrite !id_mat_entry; try assumption.
  destruct (Nat.eq_dec i j); destruct (Nat.eq_dec j i); try reflexivity;
    try (exfalso; lia).
Qed.

(** Identity observable: constant process of identity matrix *)
Definition id_observable (dim : nat) : QObservable dim.
Proof.
  refine (mkQObservable dim (fun _ => id_mat dim) _ _).
  - intro k. exact (id_mat_symmetric dim).
  - intros i j Hi Hj. intros eps Heps.
    exists 0%nat. intros m p _ _.
    setoid_replace (mat_entry (id_mat dim) i j - mat_entry (id_mat dim) i j)
      with 0 by ring.
    rewrite Qabs_pos; lra.
Defined.

(** Helper: sum of a list with exactly one nonzero term at position j *)
Lemma fold_left_Qplus_single_val : forall (l : list Q) (j : nat) (val : Q),
  (j < length l)%nat ->
  (forall idx, (idx < length l)%nat ->
    nth idx l 0 == (if Nat.eq_dec idx j then val else 0)) ->
  fold_left Qplus l 0 == val.
Proof.
  intros l. induction l as [| x xs IH]; intros j val Hj Hterms.
  - exfalso. change (length (@nil Q)) with 0%nat in Hj.
    exact (PeanoNat.Nat.nlt_0_r j Hj).
  - simpl. rewrite fold_left_Qplus_init_shift.
    assert (Hx : x == if Nat.eq_dec 0 j then val else 0).
    { specialize (Hterms 0%nat ltac:(simpl; lia)). simpl in Hterms. exact Hterms. }
    destruct (Nat.eq_dec 0 j) as [H0j | H0j].
    + subst j. rewrite Hx.
      assert (Hrest : fold_left Qplus xs 0 == 0).
      { apply fold_left_Qplus_zero_terms. intros idx Hidx.
        assert (Hs := Hterms (S idx) ltac:(simpl; lia)).
        simpl in Hs. destruct (Nat.eq_dec (S idx) 0); [lia | exact Hs]. }
      rewrite Hrest. ring.
    + rewrite Hx. ring_simplify.
      assert (Hpred_j : (j - 1 < length xs)%nat) by (simpl in Hj; lia).
      apply (IH (j - 1)%nat val Hpred_j).
      intros idx Hidx.
      assert (Hs := Hterms (S idx) ltac:(simpl; lia)).
      change (nth (S idx) (x :: xs) 0) with (nth idx xs 0) in Hs.
      destruct (Nat.eq_dec (S idx) j) as [HSj | HnSj];
        simpl in Hs;
        destruct (Nat.eq_dec idx (j - 1)) as [Hjm | Hnjm].
      * exact Hs.
      * exfalso. apply Hnjm. lia.
      * exfalso. apply HnSj. lia.
      * exact Hs.
Qed.

(** Dot product of basis vector extracts the i-th component *)
Lemma dot_basis_extracts : forall n (v : QVec n) i,
  (i < n)%nat -> dot_product (basis_vec n i) v == qv_nth v i.
Proof.
  intros n v i Hi. unfold dot_product.
  set (bv := qv_data (basis_vec n i)).
  set (vd := qv_data v).
  assert (Hblen : length bv = n) by (unfold bv; exact (qv_length (basis_vec n i))).
  assert (Hvlen : length vd = n) by (unfold vd; exact (qv_length v)).
  assert (Hlen : length bv = length vd) by (rewrite Hblen, Hvlen; reflexivity).
  set (prods := map2 Qmult bv vd).
  assert (Hplen : length prods = n)
    by (unfold prods; rewrite map2_length; [exact Hblen | exact Hlen]).
  apply (fold_left_Qplus_single_val prods i (qv_nth v i)).
  - rewrite Hplen. exact Hi.
  - intros idx Hidx. rewrite Hplen in Hidx.
    unfold prods.
    assert (Hidx_b : (idx < length bv)%nat) by (rewrite Hblen; exact Hidx).
    rewrite nth_map2_Qeq; [| exact Hidx_b | exact Hlen].
    unfold bv. change (nth idx (qv_data (basis_vec n i)) 0) with
      (qv_nth (basis_vec n i) idx).
    unfold vd. change (nth idx (qv_data v) 0) with (qv_nth v idx).
    destruct (Nat.eq_dec idx i) as [Heq | Hneq].
    + subst idx. rewrite basis_vec_same; [ring | exact Hi].
    + rewrite basis_vec_diff; [ring | exact Hidx | exact Hneq].
Qed.

(** Identity acts as identity — using dot_basis_extracts *)
Lemma id_action_identity : forall dim (s : QState dim) k i,
  (i < dim)%nat ->
  qv_nth (obs_action_at (id_observable dim) s k) i ==
  qv_nth (state_at s k) i.
Proof.
  intros dim s k i Hi.
  unfold obs_action_at, obs_at. simpl.
  rewrite mat_vec_mul_nth; [| exact Hi].
  unfold mat_row, id_mat. simpl.
  rewrite (nth_map_general _ (seq 0 _) 0%nat _ i); [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  apply dot_basis_extracts. exact Hi.
Qed.

(* ========================================================================= *)
(*  SECTION 5: Diagonal Observable                                          *)
(* ========================================================================= *)

(** Diagonal matrix from eigenvalue list *)
Definition diag_mat {n} (eigenvals : QVec n) : QMat n n.
Proof.
  refine (mkQMat
    (map (fun i => qv_scale (qv_nth eigenvals i) (basis_vec n i))
         (seq 0 n)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

(** Diagonal matrix entry *)
Lemma diag_mat_entry : forall {n} (eigenvals : QVec n) i j,
  (i < n)%nat -> (j < n)%nat ->
  mat_entry (diag_mat eigenvals) i j ==
    (if Nat.eq_dec i j then qv_nth eigenvals i else 0).
Proof.
  intros n eigenvals i j Hi Hj.
  unfold mat_entry, mat_row, diag_mat. simpl.
  rewrite (nth_map_general _ (seq 0 _) 0%nat _ i); [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  (* Goal: qv_nth (qv_scale (qv_nth eigenvals i) (basis_vec n i)) j == ... *)
  rewrite qv_scale_nth; [| exact Hj].
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  - subst i. rewrite basis_vec_same; [ring | exact Hj].
  - rewrite basis_vec_diff; [ring | exact Hj | auto].
Qed.

(** Diagonal matrix is symmetric *)
Lemma diag_mat_symmetric : forall {n} (eigenvals : QVec n),
  is_symmetric (diag_mat eigenvals).
Proof.
  intros n eigenvals i j Hi Hj.
  rewrite !diag_mat_entry; try assumption.
  destruct (Nat.eq_dec i j) as [Heq | Hneq];
    destruct (Nat.eq_dec j i) as [Heq' | Hneq'].
  - subst. reflexivity.
  - exfalso. apply Hneq'. lia.
  - exfalso. apply Hneq. lia.
  - reflexivity.
Qed.

(** Diagonal observable: constant process of diagonal matrix *)
Definition diag_observable {dim} (eigenvals : QVec dim) : QObservable dim.
Proof.
  refine (mkQObservable dim (fun _ => diag_mat eigenvals) _ _).
  - intro k. exact (diag_mat_symmetric eigenvals).
  - intros i j Hi Hj. intros eps Heps.
    exists 0%nat. intros m p _ _.
    setoid_replace (mat_entry (diag_mat eigenvals) i j -
                    mat_entry (diag_mat eigenvals) i j)
      with 0 by ring.
    rewrite Qabs_pos; lra.
Defined.

(** Diagonal observable action on basis state *)
Lemma diag_action_basis : forall {dim} (eigenvals : QVec dim) j k i,
  (j < dim)%nat -> (i < dim)%nat ->
  qv_nth (obs_action_at (diag_observable eigenvals) (basis_state dim j) k) i ==
  (if Nat.eq_dec i j then qv_nth eigenvals j else 0).
Proof.
  intros dim eigenvals j k i Hj Hi.
  unfold obs_action_at, obs_at. simpl.
  rewrite mat_vec_mul_nth; [| exact Hi].
  (* dot_product (mat_row (diag_mat eigenvals) i) (basis_vec dim j) *)
  rewrite dot_product_comm.
  (* dot_product (basis_vec dim j) (mat_row (diag_mat eigenvals) i) *)
  rewrite dot_basis_extracts; [| exact Hj].
  unfold mat_row, diag_mat. simpl.
  rewrite (nth_map_general _ (seq 0 _) 0%nat _ i); [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  (* qv_nth (qv_scale (qv_nth eigenvals i) (basis_vec dim i)) j *)
  rewrite qv_scale_nth; [| exact Hj].
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  - subst i. rewrite basis_vec_same; [ring | exact Hj].
  - rewrite basis_vec_diff; [ring | exact Hj | auto].
Qed.

(* ========================================================================= *)
(*  SECTION 6: Eigenstates                                                  *)
(* ========================================================================= *)

(** An eigenstate of observable A with eigenvalue lambda:
    A·ψ converges to λ·ψ component-wise *)
Definition is_eigenstate {dim} (A : QObservable dim) (psi : QState dim) (lambda : Q) : Prop :=
  forall i, (i < dim)%nat ->
    forall eps, 0 < eps ->
      exists N, forall k, (N <= k)%nat ->
        Qabs (qv_nth (obs_action_at A psi k) i - lambda * qv_nth (state_at psi k) i) < eps.

(** Basis state is eigenstate of diagonal observable *)
Theorem diag_eigenstate : forall {dim} (eigenvals : QVec dim) j,
  (j < dim)%nat ->
  is_eigenstate (diag_observable eigenvals) (basis_state dim j) (qv_nth eigenvals j).
Proof.
  intros dim eigenvals j Hj i Hi eps Heps.
  exists 0%nat. intros k _.
  rewrite diag_action_basis; [| exact Hj | exact Hi].
  rewrite basis_state_at.
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  - subst i. rewrite basis_vec_same; [| exact Hj].
    setoid_replace (qv_nth eigenvals j - qv_nth eigenvals j * 1) with 0 by ring.
    rewrite Qabs_pos; lra.
  - rewrite basis_vec_diff; [| exact Hi | exact Hneq].
    setoid_replace (0 - qv_nth eigenvals j * 0) with 0 by ring.
    rewrite Qabs_pos; lra.
Qed.


(* ========================================================================= *)
(*  SECTION 7: Observable Equivalence                                       *)
(* ========================================================================= *)

(** Two observables are equivalent if their entries converge to the same limits *)
Definition obs_equiv {dim} (A B : QObservable dim) : Prop :=
  forall i j, (i < dim)%nat -> (j < dim)%nat ->
    forall eps, 0 < eps ->
      exists N, forall k, (N <= k)%nat ->
        Qabs (mat_entry (obs_at A k) i j - mat_entry (obs_at B k) i j) < eps.

Lemma obs_equiv_refl : forall {dim} (A : QObservable dim),
  obs_equiv A A.
Proof.
  intros dim A i j Hi Hj eps Heps.
  exists 0%nat. intros k _.
  setoid_replace (mat_entry (obs_at A k) i j - mat_entry (obs_at A k) i j)
    with 0 by ring.
  rewrite Qabs_pos; lra.
Qed.

Lemma obs_equiv_sym : forall {dim} (A B : QObservable dim),
  obs_equiv A B -> obs_equiv B A.
Proof.
  intros dim A B HAB i j Hi Hj eps Heps.
  destruct (HAB i j Hi Hj eps Heps) as [N HN].
  exists N. intros k Hk.
  specialize (HN k Hk).
  set (a := mat_entry (obs_at A k) i j) in *.
  set (b := mat_entry (obs_at B k) i j) in *.
  assert (Hopp : b - a == -(a - b)) by ring.
  assert (Habs := Qabs_wd _ _ Hopp). rewrite Habs.
  rewrite Qabs_opp. exact HN.
Qed.

Lemma obs_equiv_trans : forall {dim} (A B C : QObservable dim),
  obs_equiv A B -> obs_equiv B C -> obs_equiv A C.
Proof.
  intros dim A B C HAB HBC i j Hi Hj eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (HAB i j Hi Hj _ Heps2) as [N1 HN1].
  destruct (HBC i j Hi Hj _ Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros k Hk.
  apply Qle_lt_trans with
    (Qabs (mat_entry (obs_at A k) i j - mat_entry (obs_at B k) i j) +
     Qabs (mat_entry (obs_at B k) i j - mat_entry (obs_at C k) i j)).
  - apply Qle_trans with
      (Qabs ((mat_entry (obs_at A k) i j - mat_entry (obs_at B k) i j) +
             (mat_entry (obs_at B k) i j - mat_entry (obs_at C k) i j))).
    + apply Qeq_Qle. apply Qabs_wd.
      set (a := mat_entry (obs_at A k) i j).
      set (b := mat_entry (obs_at B k) i j).
      set (c := mat_entry (obs_at C k) i j). ring.
    + apply Qabs_triangle.
  - specialize (HN1 k ltac:(lia)). specialize (HN2 k ltac:(lia)). lra.
Qed.

(** Summary:
    QObservable: quantum observables as symmetric matrix processes.
    - Matrix access: mat_row, mat_entry, mat_vec_mul_nth
    - Symmetry: is_symmetric, obs_symmetric_at
    - Identity: id_mat, id_mat_symmetric, id_observable, id_action_identity
    - Diagonal: diag_mat, diag_mat_symmetric, diag_observable, diag_action_basis
    - Eigenstates: is_eigenstate, diag_eigenstate
    - Equivalence: obs_equiv_refl, obs_equiv_sym, obs_equiv_trans
    - Key tool: dot_basis_extracts
*)
