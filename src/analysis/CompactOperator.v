(** * CompactOperator.v — Finite-Rank Linear Operators on Q^n

    Theory of Systems — Analysis / Spectral Theory Step 3

    Linear operators represented as matrices (list of rows), with
    application, self-adjointness, eigenvalues, and trace.
    Finite-rank = compact in finite dimension.

    Elements: LinOp (matrix), vectors (list Q), eigenvalues, trace
    Roles:    apply_op -> linear map, is_self_adjoint -> symmetry,
              is_eigenpair -> spectral data, mat_trace -> scalar invariant
    Rules:    eigenvalue orthogonality for distinct eigenvalues of
              self-adjoint operators (L5: verified concretely)
    Status:   verified | concrete_checked

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 0: REPLICATED FROM L2Space.v                                      *)
(* ========================================================================= *)

Fixpoint l2_inner (u v : list Q) : Q :=
  match u, v with
  | [], _ | _, [] => 0
  | a :: us, b :: vs => a * b + l2_inner us vs
  end.

Definition l2_norm_sq (u : list Q) : Q := l2_inner u u.

Fixpoint vec_scale (c : Q) (u : list Q) : list Q :=
  match u with
  | [] => []
  | x :: xs => (c * x) :: vec_scale c xs
  end.

Fixpoint vec_add (u v : list Q) : list Q :=
  match u, v with
  | [], _ | _, [] => []
  | a :: us, b :: vs => (a + b) :: vec_add us vs
  end.

Lemma l2_inner_nil_r : forall u, l2_inner u [] == 0.
Proof. induction u as [| x xs IH]; simpl; lra. Qed.

Lemma l2_inner_comm : forall u v, l2_inner u v == l2_inner v u.
Proof.
  induction u as [| x xs IH]; intro v.
  - simpl. assert (H := l2_inner_nil_r v). lra.
  - destruct v as [| y ys].
    + simpl. assert (H := l2_inner_nil_r (x :: xs)). simpl in H. lra.
    + simpl. specialize (IH ys). rewrite IH. ring.
Qed.

Lemma nth_nil_default : forall n, nth n (@nil Q) 0 == 0.
Proof. induction n; simpl; lra. Qed.

(* ========================================================================= *)
(* SECTION 1: OPERATOR DEFINITIONS                                           *)
(* ========================================================================= *)

(** Linear operator on Q^n: matrix as list of rows *)
Definition LinOp := list (list Q).

(** Apply operator to vector: M·v = [row_i · v] *)
Definition apply_op (M : LinOp) (v : list Q) : list Q :=
  map (fun row => l2_inner row v) M.

(** Matrix entry access *)
Definition mat_entry (M : LinOp) (i j : nat) : Q :=
  nth j (nth i M []) 0.

(** Trace: sum of diagonal entries *)
Fixpoint trace_aux (M : LinOp) (i : nat) : Q :=
  match M with
  | [] => 0
  | row :: rest => nth i row 0 + trace_aux rest (S i)
  end.

Definition mat_trace (M : LinOp) : Q := trace_aux M O.

(** Determinant for 2x2 *)
Definition det_2x2 (M : LinOp) : Q :=
  match M with
  | [r1; r2] =>
    match r1, r2 with
    | [a; b], [c; d] => a * d - b * c
    | _, _ => 0
    end
  | _ => 0
  end.

(** Self-adjoint: M_ij = M_ji *)
Definition is_self_adjoint (M : LinOp) : Prop :=
  forall i j, mat_entry M i j == mat_entry M j i.

(** Eigenvalue: ⟨row_i, v⟩ = λ · v_i for all i *)
Definition is_eigenpair_q (M : LinOp) (lam : Q) (v : list Q) : Prop :=
  forall i, nth i (apply_op M v) 0 == lam * nth i v 0.

(* ========================================================================= *)
(* SECTION 2: BASIC OPERATOR PROPERTIES                                      *)
(* ========================================================================= *)

(* 1: Identity application (concrete) *)
Lemma apply_identity_2x2_concrete :
  forall i, nth i (apply_op [[1;0];[0;1]] [3;5]) 0 ==
            nth i [3;5] 0.
Proof.
  intro i.
  destruct i as [| [| n]]; simpl; try ring; lra.
Qed.

(* 2: Trace of 2x2 *)
Lemma trace_2x2 : forall a b c d : Q,
  mat_trace [[a;b];[c;d]] == a + d.
Proof.
  intros. unfold mat_trace. simpl. lra.
Qed.

(* 3: Det of 2x2 *)
Lemma det_2x2_compute : forall a b c d : Q,
  det_2x2 [[a;b];[c;d]] == a * d - b * c.
Proof.
  intros. unfold det_2x2. lra.
Qed.

(* 4: Diagonal matrix is self-adjoint *)
Lemma diagonal_self_adjoint : forall lam1 lam2 : Q,
  is_self_adjoint [[lam1;0];[0;lam2]].
Proof.
  intros lam1 lam2. unfold is_self_adjoint, mat_entry.
  intros i j.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* 5: Symmetric matrix is self-adjoint *)
Lemma symmetric_self_adjoint : forall a b c : Q,
  is_self_adjoint [[a;b];[b;c]].
Proof.
  intros a b c. unfold is_self_adjoint, mat_entry.
  intros i j.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: EIGENVALUE PROPERTIES                                          *)
(* ========================================================================= *)

(* 6: Eigenvalue of diagonal matrix — first eigenvector *)
Lemma eigenvalue_diagonal_1 : forall lam1 lam2 : Q,
  is_eigenpair_q [[lam1;0];[0;lam2]] lam1 [1;0].
Proof.
  intros lam1 lam2. unfold is_eigenpair_q.
  intro i. destruct i as [| [| n]]; unfold apply_op; simpl; try ring.
  assert (Hn : nth n (@nil Q) 0 == 0) by apply nth_nil_default.
  rewrite Hn. ring.
Qed.

(* 7: Eigenvalue of diagonal matrix — second eigenvector *)
Lemma eigenvalue_diagonal_2 : forall lam1 lam2 : Q,
  is_eigenpair_q [[lam1;0];[0;lam2]] lam2 [0;1].
Proof.
  intros lam1 lam2. unfold is_eigenpair_q.
  intro i. destruct i as [| [| n]]; unfold apply_op; simpl; try ring.
  assert (Hn : nth n (@nil Q) 0 == 0) by apply nth_nil_default.
  rewrite Hn. ring.
Qed.

(* 8: Eigenvectors of diagonal with distinct eigenvalues are orthogonal *)
Lemma eigenvectors_orthogonal_diagonal :
  l2_inner [1;0] [0;1] == 0.
Proof. vm_compute. reflexivity. Qed.

(* 9: Eigenvalue sum = trace (concrete) *)
Lemma eigenvalue_sum_trace :
  forall lam1 lam2 : Q,
  mat_trace [[lam1;0];[0;lam2]] == lam1 + lam2.
Proof.
  intros. unfold mat_trace. simpl. lra.
Qed.

(* 10: Eigenvalue product = determinant (concrete) *)
Lemma eigenvalue_prod_det :
  forall lam1 lam2 : Q,
  det_2x2 [[lam1;0];[0;lam2]] == lam1 * lam2.
Proof.
  intros. unfold det_2x2. ring.
Qed.

(* ========================================================================= *)
(* SECTION 4: CONCRETE EXAMPLES                                              *)
(* ========================================================================= *)

(* 11: Rotation by 90 degrees maps [1,0] to [0,1] *)
Lemma rotation_90_apply :
  forall i, nth i (apply_op [[0;-(1)];[1;0]] [1;0]) 0 ==
            nth i [0;1] 0.
Proof.
  intro i. destruct i as [| [| n]]; simpl; try ring; lra.
Qed.

(* 12: Projection onto x-axis *)
Lemma projection_x_apply :
  forall i, nth i (apply_op [[1;0];[0;0]] [3;4]) 0 ==
            nth i [3;0] 0.
Proof.
  intro i. destruct i as [| [| n]]; simpl; try ring; lra.
Qed.

(* Helper: for concrete 2-element eigenpair checks *)
Lemma eigenpair_tail_q : forall lam n,
  nth n (@nil Q) 0 == lam * nth n (@nil Q) 0.
Proof.
  intros. rewrite nth_nil_default. ring.
Qed.

(* 13: [[2,1],[1,2]] has eigenvector [1,1] with eigenvalue 3 *)
Lemma eigenpair_symmetric_3 :
  is_eigenpair_q [[2;1];[1;2]] 3 [1;1].
Proof.
  unfold is_eigenpair_q, apply_op.
  intro i. destruct i as [| [| n]].
  - simpl. ring.
  - simpl. ring.
  - simpl. apply eigenpair_tail_q.
Qed.

(* 14: [[2,1],[1,2]] has eigenvector [1,-1] with eigenvalue 1 *)
Lemma eigenpair_symmetric_1 :
  is_eigenpair_q [[2;1];[1;2]] 1 [1;-(1)].
Proof.
  unfold is_eigenpair_q, apply_op.
  intro i. destruct i as [| [| n]].
  - simpl. ring.
  - simpl. ring.
  - simpl. apply eigenpair_tail_q.
Qed.

(* 15: Those eigenvectors are orthogonal *)
Lemma eigenvectors_orthogonal_symmetric :
  l2_inner [1;1] [1;-(1)] == 0.
Proof. vm_compute. reflexivity. Qed.

(* 16: Trace and det verify: trace([[2,1],[1,2]])=3, det=3,
        eigenvalues 3,1 satisfy λ₁+λ₂=4=trace, λ₁·λ₂=3=det *)
Lemma trace_det_eigenvalues :
  mat_trace [[2;1];[1;2]] == 4 /\
  det_2x2 [[2;1];[1;2]] == 3.
Proof.
  split.
  - unfold mat_trace. simpl. lra.
  - unfold det_2x2. ring.
Qed.
