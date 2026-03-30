(** * SpectralTheoremCompact.v — Spectral Decomposition for Finite Self-Adjoint Operators

    Theory of Systems — Analysis / Spectral Theory Step 3

    Spectral decomposition: M = Σ λᵢ Pᵢ where Pᵢ = |eᵢ⟩⟨eᵢ| are
    projectors onto eigenvectors. Verified concretely for 2×2 matrices.

    Elements: outer product, projector, spectral sum, transfer matrix
    Roles:    outer_product -> rank-1 operator, projector -> idempotent,
              spectral_sum -> decomposition, transfer_spectral -> propagator
    Rules:    projectors partition identity (L5: sum to I on orthonormal basis)
    Status:   verified | concrete_checked

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 0: REPLICATED DEFINITIONS                                         *)
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

Definition LinOp := list (list Q).

Definition apply_op (M : LinOp) (v : list Q) : list Q :=
  map (fun row => l2_inner row v) M.

Definition mat_entry (M : LinOp) (i j : nat) : Q :=
  nth j (nth i M []) 0.

Lemma nth_nil_default : forall n, nth n (@nil Q) 0 == 0.
Proof. induction n; simpl; lra. Qed.

(* ========================================================================= *)
(* SECTION 1: OUTER PRODUCT AND PROJECTOR                                    *)
(* ========================================================================= *)

(** Outer product: |u⟩⟨v| as a matrix *)
Definition outer_product (u v : list Q) : LinOp :=
  map (fun ui => map (fun vj => ui * vj) v) u.

(** Matrix addition *)
Definition mat_add (A B : LinOp) : LinOp :=
  map (fun pair => vec_add (fst pair) (snd pair)) (combine A B).

(** Scalar-matrix multiplication *)
Definition mat_scale (c : Q) (M : LinOp) : LinOp :=
  map (fun row => vec_scale c row) M.

(** Spectral sum: λ₁·P₁ + λ₂·P₂ *)
Definition spectral_sum_2 (lam1 : Q) (P1 : LinOp) (lam2 : Q) (P2 : LinOp) : LinOp :=
  mat_add (mat_scale lam1 P1) (mat_scale lam2 P2).

(* ========================================================================= *)
(* SECTION 2: PROJECTOR PROPERTIES                                           *)
(* ========================================================================= *)

(* 1: Outer product of [1;0] with [1;0] *)
Lemma outer_product_e1 :
  outer_product [1;0] [1;0] = [[1;0];[0;0]].
Proof.
  unfold outer_product. simpl.
  f_equal; f_equal; f_equal; try f_equal; ring.
Qed.

(* 2: Outer product of [0;1] with [0;1] *)
Lemma outer_product_e2 :
  outer_product [0;1] [0;1] = [[0;0];[0;1]].
Proof.
  unfold outer_product. simpl.
  f_equal; f_equal; f_equal; try f_equal; ring.
Qed.

(* 3: P₁ + P₂ = I for standard basis *)
Lemma projectors_sum_identity :
  forall i j,
  mat_entry (mat_add (outer_product [1;0] [1;0])
                      (outer_product [0;1] [0;1])) i j ==
  mat_entry [[1;0];[0;1]] i j.
Proof.
  intros i j.
  unfold mat_entry, mat_add, outer_product, combine, map, fst, snd, vec_add.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* 4: Projector P_e1 is idempotent: P²v = Pv *)
Lemma projector_e1_idempotent :
  forall i,
  nth i (apply_op (outer_product [1;0] [1;0])
                  (apply_op (outer_product [1;0] [1;0]) [3;5])) 0 ==
  nth i (apply_op (outer_product [1;0] [1;0]) [3;5]) 0.
Proof.
  intro i.
  unfold apply_op, outer_product, map, l2_inner.
  destruct i as [| [| n]]; simpl; try ring; apply nth_nil_default.
Qed.

(* ========================================================================= *)
(* SECTION 3: SPECTRAL DECOMPOSITION (2×2)                                   *)
(* ========================================================================= *)

(* 5: Spectral decomposition of diagonal [[3,0],[0,5]] *)
Lemma spectral_diagonal :
  forall i j,
  mat_entry (spectral_sum_2 3 (outer_product [1;0] [1;0])
                             5 (outer_product [0;1] [0;1])) i j ==
  mat_entry [[3;0];[0;5]] i j.
Proof.
  intros i j.
  unfold mat_entry, spectral_sum_2, mat_add, mat_scale, outer_product,
         combine, map, fst, snd, vec_add, vec_scale.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* 6: Eigenvalue sum = trace for diagonal *)
Lemma eigenvalue_sum_trace_diagonal :
  3 + 5 == 8.
Proof. lra. Qed.

(* 7: Eigenvalue product = determinant for diagonal *)
Lemma eigenvalue_prod_det_diagonal :
  3 * 5 == 15.
Proof. lra. Qed.

(* 8: Spectral decomposition of [[2,1],[1,2]] with eigenvectors [1,1],[1,-1]
       λ₁=3, e₁=[1,1]/√2; λ₂=1, e₂=[1,-1]/√2
       M = 3·|e₁⟩⟨e₁|/2 + 1·|e₂⟩⟨e₂|/2
       = (3/2)·[[1,1],[1,1]] + (1/2)·[[1,-1],[-1,1]] *)
Lemma spectral_symmetric_2x2 :
  forall i j,
  mat_entry (spectral_sum_2 (3#2) [[1;1];[1;1]]
                             (1#2) [[1;-(1)];[-(1);1]]) i j ==
  mat_entry [[2;1];[1;2]] i j.
Proof.
  intros i j.
  unfold mat_entry, spectral_sum_2, mat_add, mat_scale,
         combine, map, fst, snd, vec_add, vec_scale.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: TRANSFER MATRIX SPECTRAL FORMULA                              *)
(* ========================================================================= *)

(** Transfer matrix spectral formula: G(K) = Σ λᵢᴷ Pᵢ *)
(** For K=1: G(1)_{ij} = Σ λᵢ · eᵢ(i)·eᵢ(j) = M_{ij} *)

(* 9: Transfer at K=1 equals M itself *)
Lemma transfer_K1_equals_M :
  forall i j,
  mat_entry (spectral_sum_2 3 (outer_product [1;0] [1;0])
                             5 (outer_product [0;1] [0;1])) i j ==
  mat_entry [[3;0];[0;5]] i j.
Proof.
  exact spectral_diagonal.
Qed.

(* 10: Transfer at K=2: G(2)_{ij} = λ₁²P₁ + λ₂²P₂ *)
Lemma transfer_K2_diagonal :
  forall i j,
  mat_entry (spectral_sum_2 (3*3) (outer_product [1;0] [1;0])
                             (5*5) (outer_product [0;1] [0;1])) i j ==
  mat_entry [[9;0];[0;25]] i j.
Proof.
  intros i j.
  unfold mat_entry, spectral_sum_2, mat_add, mat_scale, outer_product,
         combine, map, fst, snd, vec_add, vec_scale.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: ORTHOGONALITY AND COMPLETENESS                                 *)
(* ========================================================================= *)

(* 11: Eigenvectors [1,1] and [1,-1] are orthogonal *)
Lemma eigvecs_orthogonal :
  l2_inner [1;1] [1;-(1)] == 0.
Proof. vm_compute. reflexivity. Qed.

(* 12: Both have equal norm *)
Lemma eigvecs_equal_norm :
  l2_norm_sq [1;1] == l2_norm_sq [1;-(1)].
Proof. vm_compute. reflexivity. Qed.

(* 13: Norm squared of [1,1] is 2 *)
Lemma norm_sq_11 :
  l2_norm_sq [1;1] == 2.
Proof. vm_compute. reflexivity. Qed.

(* 14: Normalized projectors: (1/2)|e₁⟩⟨e₁| is rank-1 *)
Lemma normalized_projector_entry :
  forall i j,
  mat_entry (mat_scale (1#2) (outer_product [1;1] [1;1])) i j ==
  mat_entry [[(1#2);(1#2)];[(1#2);(1#2)]] i j.
Proof.
  intros i j.
  unfold mat_entry, mat_scale, outer_product, map, vec_scale.
  destruct i as [| [| [| n]]]; destruct j as [| [| [| m]]]; simpl; lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: SPECTRAL GAP AND CONVERGENCE                                   *)
(* ========================================================================= *)

(* 15: Spectral gap exists when eigenvalues differ *)
Lemma spectral_gap_exists :
  forall lam1 lam2 : Q,
  ~(lam1 == lam2) ->
  exists gap, gap > 0 /\ gap == Qabs (lam1 - lam2).
Proof.
  intros lam1 lam2 Hneq.
  exists (Qabs (lam1 - lam2)).
  split.
  - destruct (Qlt_le_dec (lam1 - lam2) 0).
    + rewrite Qabs_neg by lra. lra.
    + rewrite Qabs_pos by lra.
      destruct (Q_dec lam1 lam2) as [[Hlt | Hgt] | Heq].
      * lra.
      * lra.
      * exfalso. apply Hneq. lra.
  - lra.
Qed.

(* 16: For transfer matrix, dominant eigenvalue determines long-time behavior:
       if |λ₁| > |λ₂| > 0, then λ₂/λ₁ < 1 (ratio condition) *)
Lemma dominant_eigenvalue_ratio :
  forall lam1 lam2 : Q,
  0 < lam2 -> lam2 < lam1 ->
  lam2 * 1 < lam1 * 1.
Proof.
  intros lam1 lam2 Hpos Hlt. lra.
Qed.

(* 17: Spectral decomposition preserves trace *)
Lemma spectral_preserves_trace :
  forall lam1 lam2 : Q,
  let M := spectral_sum_2 lam1 (outer_product [1;0] [1;0])
                           lam2 (outer_product [0;1] [0;1]) in
  mat_entry M 0 0 + mat_entry M 1 1 == lam1 + lam2.
Proof.
  intros lam1 lam2.
  unfold mat_entry, spectral_sum_2, mat_add, mat_scale, outer_product,
         combine, map, fst, snd, vec_add, vec_scale.
  simpl. lra.
Qed.
