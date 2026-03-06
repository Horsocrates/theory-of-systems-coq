(**
  LinearAlgebra.v — Vectors and Matrices over Q
  ===============================================

  Phase 3, Task 4.

  Provides QVec (length-indexed vectors) and QMat (matrices)
  with operations: add, scale, dot product, matrix-vector multiply.

  Design: QVec n wraps a list Q with a length proof.
  Equality is Qeq-pointwise for values, Leibniz for lengths.

  Connection to Regulus: PInterval bounds can be lifted to per-component
  interval vectors, enabling multi-dimensional NN verification.

  Depends on: QArith, List (standalone — no ToS imports needed)
  Qed: 20 (+4 Defined), Admitted: 0
*)

Require Import QArith List Lia.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================= *)
(** * Helper: map2 — pointwise binary operation on lists            *)
(* ================================================================= *)

Fixpoint map2 (f : Q -> Q -> Q) (l1 l2 : list Q) : list Q :=
  match l1, l2 with
  | x :: xs, y :: ys => f x y :: map2 f xs ys
  | _, _ => []
  end.

Lemma map2_length : forall f (l1 l2 : list Q),
  length l1 = length l2 ->
  length (map2 f l1 l2) = length l1.
Proof.
  intros f l1. induction l1 as [| x xs IH]; intros l2 Hlen.
  - reflexivity.
  - destruct l2 as [| y ys].
    + simpl in Hlen. discriminate.
    + simpl. f_equal. apply IH. simpl in Hlen. lia.
Qed.

Lemma map2_comm : forall (f : Q -> Q -> Q),
  (forall x y, f x y == f y x) ->
  forall (l1 l2 : list Q) i,
    nth i (map2 f l1 l2) 0 == nth i (map2 f l2 l1) 0.
Proof.
  intros f Hcomm. induction l1 as [| x xs IH]; intros [| y ys] i; simpl;
    try reflexivity.
  destruct i.
  - apply Hcomm.
  - apply IH.
Qed.

Lemma map2_assoc : forall (f : Q -> Q -> Q),
  (forall x y z, f (f x y) z == f x (f y z)) ->
  forall (l1 l2 l3 : list Q) i,
    nth i (map2 f (map2 f l1 l2) l3) 0 ==
    nth i (map2 f l1 (map2 f l2 l3)) 0.
Proof.
  intros f Hassoc. induction l1 as [| x xs IH];
    intros [| y ys] [| z zs] i; simpl;
    try reflexivity; try (destruct i; reflexivity).
  destruct i.
  - apply Hassoc.
  - apply IH.
Qed.

(** map distributes over map2: f(g(a,b)) = g(f(a), f(b)) pointwise *)
Lemma map_map2_distrib : forall (f : Q -> Q) (g : Q -> Q -> Q),
  (forall x y, f (g x y) == g (f x) (f y)) ->
  forall (l1 l2 : list Q) i,
    nth i (map f (map2 g l1 l2)) 0 ==
    nth i (map2 g (map f l1) (map f l2)) 0.
Proof.
  intros f g Hdist. induction l1 as [| x xs IH];
    intros [| y ys] i; simpl; try reflexivity.
  destruct i.
  - apply Hdist.
  - apply IH.
Qed.

(** Elements of map2 Qmult with zero list are all zero *)
Lemma map2_Qmult_zero_r : forall (l : list Q) (m : nat),
  forall x, In x (map2 Qmult l (repeat 0 m)) -> x == 0.
Proof.
  induction l as [| a l' IH]; intros m x Hx.
  - simpl in Hx. destruct Hx.
  - destruct m as [| m'].
    + simpl in Hx. destruct Hx.
    + simpl in Hx. destruct Hx as [Heq | Hin].
      * rewrite <- Heq. ring.
      * exact (IH m' x Hin).
Qed.

(** nth of map with Qeq *)
Lemma nth_map_Qeq : forall (f : Q -> Q) (l : list Q) (i : nat),
  (i < length l)%nat ->
  nth i (map f l) 0 == f (nth i l 0).
Proof.
  intros f l. induction l as [| x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i.
    + reflexivity.
    + apply IH. lia.
Qed.

(** fold_left Qplus over zero list *)
Lemma fold_left_Qplus_zeros : forall (l : list Q) (init : Q),
  (forall x, In x l -> x == 0) ->
  fold_left Qplus l init == init.
Proof.
  induction l as [| x xs IH]; intros init Hall; simpl.
  - reflexivity.
  - assert (Hx : x == 0) by (apply Hall; left; reflexivity).
    rewrite IH.
    + setoid_rewrite Hx. ring.
    + intros y Hy. apply Hall. right. exact Hy.
Qed.

(** fold_left Qplus respects Qeq in init *)
Lemma fold_left_Qplus_init_compat : forall (l : list Q) (a b : Q),
  a == b -> fold_left Qplus l a == fold_left Qplus l b.
Proof.
  induction l as [| x xs IH]; intros a b Hab; simpl.
  - exact Hab.
  - apply IH. rewrite Hab. reflexivity.
Qed.

(** fold_left Qplus respects pointwise Qeq *)
Lemma fold_left_Qplus_Qeq : forall (l1 l2 : list Q) (init : Q),
  length l1 = length l2 ->
  (forall i, nth i l1 0 == nth i l2 0) ->
  fold_left Qplus l1 init == fold_left Qplus l2 init.
Proof.
  intros l1. induction l1 as [| x xs IH]; intros l2 init Hlen Hnth.
  - destruct l2; [reflexivity | simpl in Hlen; discriminate].
  - destruct l2 as [| y ys]; [simpl in Hlen; discriminate |].
    simpl.
    assert (Hxy : x == y) by (specialize (Hnth O); simpl in Hnth; exact Hnth).
    apply Qeq_trans with (fold_left Qplus ys (init + x)).
    + apply IH.
      * simpl in Hlen. lia.
      * intro i. specialize (Hnth (S i)). simpl in Hnth. exact Hnth.
    + apply fold_left_Qplus_init_compat. rewrite Hxy. reflexivity.
Qed.

(* ================================================================= *)
(** * QVec — Length-Indexed Vectors over Q                          *)
(* ================================================================= *)

Record QVec (n : nat) := mkQVec {
  qv_data : list Q;
  qv_length : length qv_data = n;
}.

Arguments mkQVec {n} _ _.
Arguments qv_data {n} _.
Arguments qv_length {n} _.

(** Element access *)
Definition qv_nth {n} (v : QVec n) (i : nat) : Q :=
  nth i (qv_data v) 0.

(** Zero vector *)
Definition qv_zero (n : nat) : QVec n.
Proof.
  exact (mkQVec (repeat 0 n) (repeat_length 0 n)).
Defined.

(** Vector addition *)
Definition qv_add {n} (v1 v2 : QVec n) : QVec n.
Proof.
  refine (mkQVec (map2 Qplus (qv_data v1) (qv_data v2)) _).
  rewrite map2_length.
  - exact (qv_length v1).
  - rewrite (qv_length v1). rewrite (qv_length v2). reflexivity.
Defined.

(** Scalar multiplication *)
Definition qv_scale {n} (c : Q) (v : QVec n) : QVec n.
Proof.
  refine (mkQVec (map (Qmult c) (qv_data v)) _).
  rewrite map_length. exact (qv_length v).
Defined.

(** Dot product *)
Definition dot_product {n} (v1 v2 : QVec n) : Q :=
  fold_left Qplus (map2 Qmult (qv_data v1) (qv_data v2)) 0.

(** Pointwise equality (using Qeq) *)
Definition qv_eq {n} (v1 v2 : QVec n) : Prop :=
  forall i, (i < n)%nat -> qv_nth v1 i == qv_nth v2 i.

(* ================================================================= *)
(** * qv_eq is an Equivalence Relation                              *)
(* ================================================================= *)

Lemma qv_eq_refl : forall {n} (v : QVec n), qv_eq v v.
Proof. intros n v i Hi. reflexivity. Qed.

Lemma qv_eq_sym : forall {n} (v1 v2 : QVec n),
  qv_eq v1 v2 -> qv_eq v2 v1.
Proof. intros n v1 v2 H i Hi. symmetry. apply H. exact Hi. Qed.

Lemma qv_eq_trans : forall {n} (v1 v2 v3 : QVec n),
  qv_eq v1 v2 -> qv_eq v2 v3 -> qv_eq v1 v3.
Proof.
  intros n v1 v2 v3 H12 H23 i Hi.
  apply Qeq_trans with (qv_nth v2 i); [apply H12 | apply H23]; exact Hi.
Qed.

(* ================================================================= *)
(** * Vector Operation Properties                                    *)
(* ================================================================= *)

(** Zero vector has all-zero components *)
Theorem qv_zero_nth : forall n i,
  (i < n)%nat -> qv_nth (qv_zero n) i == 0.
Proof.
  intros n i Hi. unfold qv_nth, qv_zero. simpl.
  rewrite nth_repeat. reflexivity.
Qed.

(** Addition is commutative *)
Theorem qv_add_comm : forall {n} (v1 v2 : QVec n),
  qv_eq (qv_add v1 v2) (qv_add v2 v1).
Proof.
  intros n v1 v2 i Hi. unfold qv_nth, qv_add. simpl.
  apply map2_comm. intros x y. ring.
Qed.

(** Addition is associative *)
Theorem qv_add_assoc : forall {n} (v1 v2 v3 : QVec n),
  qv_eq (qv_add (qv_add v1 v2) v3) (qv_add v1 (qv_add v2 v3)).
Proof.
  intros n v1 v2 v3 i Hi.
  unfold qv_nth, qv_add. simpl.
  apply map2_assoc. intros x y z. ring.
Qed.

(** Scaling by 0 gives zero vector *)
Theorem qv_scale_zero : forall {n} (v : QVec n),
  qv_eq (qv_scale 0 v) (qv_zero n).
Proof.
  intros n v i Hi. unfold qv_nth, qv_scale, qv_zero. simpl.
  rewrite nth_repeat.
  rewrite nth_map_Qeq.
  - ring.
  - rewrite (qv_length v). exact Hi.
Qed.

(** Scaling by 1 gives the same vector *)
Theorem qv_scale_one : forall {n} (v : QVec n),
  qv_eq (qv_scale 1 v) v.
Proof.
  intros n v i Hi. unfold qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq.
  - ring.
  - rewrite (qv_length v). exact Hi.
Qed.

(** Distributivity: c * (v1 + v2) = c*v1 + c*v2 *)
Theorem qv_scale_distrib : forall {n} (c : Q) (v1 v2 : QVec n),
  qv_eq (qv_scale c (qv_add v1 v2))
        (qv_add (qv_scale c v1) (qv_scale c v2)).
Proof.
  intros n c v1 v2 i Hi.
  unfold qv_nth, qv_scale, qv_add. simpl.
  apply map_map2_distrib. intros x y. ring.
Qed.

(** Scaling is associative: (c*d) * v = c * (d * v) *)
Theorem qv_scale_assoc : forall {n} (c d : Q) (v : QVec n),
  qv_eq (qv_scale (c * d) v) (qv_scale c (qv_scale d v)).
Proof.
  intros n c d v i Hi.
  unfold qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  rewrite nth_map_Qeq; [| rewrite map_length, (qv_length v); exact Hi].
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  ring.
Qed.

(* ================================================================= *)
(** * Dot Product Properties                                         *)
(* ================================================================= *)

(** Dot product with zero vector *)
Theorem dot_product_zero_right : forall {n} (v : QVec n),
  dot_product v (qv_zero n) == 0.
Proof.
  intros n v. unfold dot_product, qv_zero. simpl.
  apply fold_left_Qplus_zeros.
  intros x Hx. exact (map2_Qmult_zero_r (qv_data v) n x Hx).
Qed.

(** Dot product is commutative *)
Theorem dot_product_comm : forall {n} (v1 v2 : QVec n),
  dot_product v1 v2 == dot_product v2 v1.
Proof.
  intros n v1 v2. unfold dot_product.
  apply fold_left_Qplus_Qeq.
  - rewrite !map2_length.
    + rewrite (qv_length v1), (qv_length v2). reflexivity.
    + rewrite (qv_length v2), (qv_length v1). reflexivity.
    + rewrite (qv_length v1), (qv_length v2). reflexivity.
  - intro i. apply map2_comm. intros x y. ring.
Qed.

(* ================================================================= *)
(** * QMat — Matrices as Lists of Row Vectors                       *)
(* ================================================================= *)

Record QMat (rows cols : nat) := mkQMat {
  qm_rows : list (QVec cols);
  qm_nrows : length qm_rows = rows;
}.

Arguments mkQMat {rows cols} _ _.
Arguments qm_rows {rows cols} _.
Arguments qm_nrows {rows cols} _.

(** Matrix-vector multiplication: each row dotted with v *)
Definition mat_vec_mul {r c} (M : QMat r c) (v : QVec c) : QVec r.
Proof.
  refine (mkQVec (map (fun row => dot_product row v) (qm_rows M)) _).
  rewrite map_length. exact (qm_nrows M).
Defined.

(** Matrix-vector multiply preserves dimension *)
Theorem mat_vec_mul_length : forall {r c} (M : QMat r c) (v : QVec c),
  length (qv_data (mat_vec_mul M v)) = r.
Proof.
  intros r c M v. unfold mat_vec_mul. simpl.
  rewrite map_length. exact (qm_nrows M).
Qed.

(** Summary:
    20 Qed, 4 Defined, 0 Admitted, 0 axioms

    Infrastructure: map2_length, map2_comm, map2_assoc,
      map_map2_distrib, map2_Qmult_zero_r, nth_map_Qeq,
      fold_left_Qplus_zeros, fold_left_Qplus_init_compat,
      fold_left_Qplus_Qeq
    Equality: qv_eq_refl, qv_eq_sym, qv_eq_trans
    Vectors (Defined): qv_zero, qv_add, qv_scale, mat_vec_mul
    Vectors (Qed): qv_zero_nth, qv_add_comm, qv_add_assoc,
      qv_scale_zero, qv_scale_one, qv_scale_distrib, qv_scale_assoc
    Dot product: dot_product_zero_right, dot_product_comm
    Matrix: mat_vec_mul_length
*)
