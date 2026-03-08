(** * Tensor.v -- Tensor Operations over Q

    Theory of Systems -- Verified Standard Library (Batch 5)

    Elements: 2D tensors (matrices), outer products
    Roles:    tensor_product -> BilinearMap, trace -> ScalarInvariant
    Rules:    linearity, trace properties
    Status:   valid_tensor | zero_tensor | identity_tensor

    Connection: LinearAlgebra.v -- QMat/QVec foundation
    Connection: VectorSpace.v -- vectors as VS elements

    STATUS: 39 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import LinearAlgebra.

(* ================================================================= *)
(** * Raw list-of-lists operations                                    *)
(* ================================================================= *)

(** Diagonal extraction: starting at column [i], take one element
    per row, advancing the column index each row. *)
Fixpoint diag_raw (rows : list (list Q)) (i : nat) : list Q :=
  match rows with
  | nil => nil
  | r :: rs => nth i r 0 :: diag_raw rs (S i)
  end.

(** Trace: sum of diagonal elements (starting at column 0). *)
Definition trace_raw (rows : list (list Q)) : Q :=
  fold_left Qplus (diag_raw rows 0%nat) 0.

(** Sum of squares in a single row. *)
Definition row_sq_sum (r : list Q) : Q :=
  fold_left (fun acc x => acc + x * x) r 0.

(** Frobenius norm squared: sum of row_sq_sum over all rows. *)
Definition frobenius_sq_raw (rows : list (list Q)) : Q :=
  fold_left (fun acc r => acc + row_sq_sum r) rows 0.

(** Scale every element in a list of lists by [c]. *)
Definition scale_rows (c : Q) (rows : list (list Q)) : list (list Q) :=
  map (map (Qmult c)) rows.

(** Pointwise addition of two lists of lists. *)
Fixpoint add_rows (A B : list (list Q)) : list (list Q) :=
  match A, B with
  | ra :: as_, rb :: bs_ => map2 Qplus ra rb :: add_rows as_ bs_
  | _, _ => nil
  end.

(** Outer product of two lists: v (x) w = [[v0*w0, v0*w1, ...], ...]. *)
Definition outer_raw (v w : list Q) : list (list Q) :=
  map (fun vi => map (Qmult vi) w) v.

(** Zero matrix as list of lists. *)
Fixpoint zero_rows (m n : nat) : list (list Q) :=
  match m with
  | O => nil
  | S m' => repeat 0 n :: zero_rows m' n
  end.

(** Generalized trace: sum diagonal starting at column [i]. *)
Definition gen_trace (rows : list (list Q)) (i : nat) : Q :=
  fold_left Qplus (diag_raw rows i) 0.

(* ================================================================= *)
(** * fold_left init-compatibility helpers                            *)
(* ================================================================= *)

Lemma fold_left_Qplus_acc_t : forall (l : list Q) (a b : Q),
  fold_left Qplus l (a + b) == fold_left Qplus l a + b.
Proof.
  induction l as [| x xs IH]; intros a b; simpl.
  - reflexivity.
  - apply Qeq_trans with (fold_left Qplus xs ((a + x) + b)).
    + apply fold_left_Qplus_init_compat. ring.
    + apply IH.
Qed.

Lemma fold_left_Qplus_start_0_t : forall (l : list Q) (a : Q),
  fold_left Qplus l a == fold_left Qplus l 0 + a.
Proof.
  intros l a.
  apply Qeq_trans with (fold_left Qplus l (0 + a)).
  - apply fold_left_Qplus_init_compat. ring.
  - apply fold_left_Qplus_acc_t.
Qed.

(** Generic init-compat for the row_sq_sum accumulator. *)
Lemma sq_fold_init_compat : forall (l : list Q) (a b : Q),
  a == b ->
  fold_left (fun acc x => acc + x * x) l a ==
  fold_left (fun acc x => acc + x * x) l b.
Proof.
  induction l as [| x xs IH]; intros a b Hab; simpl.
  - exact Hab.
  - apply IH. rewrite Hab. reflexivity.
Qed.

Lemma row_sq_sum_acc : forall (l : list Q) (a b : Q),
  fold_left (fun acc x => acc + x * x) l (a + b) ==
  fold_left (fun acc x => acc + x * x) l a + b.
Proof.
  induction l as [| x xs IH]; intros a b; simpl.
  - reflexivity.
  - apply Qeq_trans with (fold_left (fun acc y => acc + y * y) xs ((a + x * x) + b)).
    + apply sq_fold_init_compat. ring.
    + apply IH.
Qed.

(** Generic init-compat for the frobenius accumulator. *)
Lemma frob_fold_init_compat : forall (rows : list (list Q)) (a b : Q),
  a == b ->
  fold_left (fun acc r => acc + row_sq_sum r) rows a ==
  fold_left (fun acc r => acc + row_sq_sum r) rows b.
Proof.
  induction rows as [| r rs IH]; intros a b Hab; simpl.
  - exact Hab.
  - apply IH. rewrite Hab. reflexivity.
Qed.

Lemma frobenius_acc : forall (rows : list (list Q)) (a b : Q),
  fold_left (fun acc r => acc + row_sq_sum r) rows (a + b) ==
  fold_left (fun acc r => acc + row_sq_sum r) rows a + b.
Proof.
  induction rows as [| r rs IH]; intros a b; simpl.
  - reflexivity.
  - apply Qeq_trans with (fold_left (fun acc rv => acc + row_sq_sum rv) rs ((a + row_sq_sum r) + b)).
    + apply frob_fold_init_compat. ring.
    + apply IH.
Qed.

(* ================================================================= *)
(** * Trace basic theorems                                            *)
(* ================================================================= *)

Theorem trace_nil : trace_raw nil = 0.
Proof. reflexivity. Qed.

Theorem trace_singleton : forall x, trace_raw [[x]] == x.
Proof. intros x. unfold trace_raw. simpl. ring. Qed.

Theorem trace_2x2 : forall a b c d,
  trace_raw [[a; b]; [c; d]] == a + d.
Proof. intros. unfold trace_raw. simpl. ring. Qed.

(* ================================================================= *)
(** * Diagonal theorems                                               *)
(* ================================================================= *)

Theorem diag_raw_nil : forall i, diag_raw nil i = nil.
Proof. reflexivity. Qed.

Theorem diag_raw_length : forall rows i,
  length (diag_raw rows i) = length rows.
Proof.
  induction rows as [| r rs IH]; intros i; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(** Every element of diag of zero_rows is 0. *)
Lemma diag_zero_rows_In : forall m n i x,
  In x (diag_raw (zero_rows m n) i) -> x == 0.
Proof.
  induction m as [| m' IH]; intros n i x Hx; simpl in Hx.
  - destruct Hx.
  - destruct Hx as [Heq | Hin].
    + rewrite <- Heq. rewrite nth_repeat. reflexivity.
    + exact (IH n (S i) x Hin).
Qed.

(** Trace of zero rows is 0. *)
Theorem tensor_zero_trace : forall m n,
  trace_raw (zero_rows m n) == 0.
Proof.
  intros m n. unfold trace_raw.
  apply fold_left_Qplus_zeros.
  intros x Hx. exact (diag_zero_rows_In m n 0%nat x Hx).
Qed.

(* ================================================================= *)
(** * gen_trace lemmas                                                *)
(* ================================================================= *)

Lemma gen_trace_nil : forall i, gen_trace nil i = 0.
Proof. reflexivity. Qed.

Lemma gen_trace_cons : forall r rs i,
  gen_trace (r :: rs) i == nth i r 0 + gen_trace rs (S i).
Proof.
  intros r rs i. unfold gen_trace. simpl.
  apply Qeq_trans with (fold_left Qplus (diag_raw rs (S i)) (nth i r 0)).
  - apply fold_left_Qplus_init_compat. ring.
  - apply Qeq_trans with (fold_left Qplus (diag_raw rs (S i)) 0 + nth i r 0).
    + apply fold_left_Qplus_start_0_t.
    + ring.
Qed.

(* ================================================================= *)
(** * Row square sum theorems                                         *)
(* ================================================================= *)

Theorem row_sq_sum_nil : row_sq_sum nil = 0.
Proof. reflexivity. Qed.

Theorem row_sq_sum_cons : forall x xs,
  row_sq_sum (x :: xs) == row_sq_sum xs + x * x.
Proof.
  intros x xs. unfold row_sq_sum at 1. simpl.
  apply Qeq_trans with (fold_left (fun acc y => acc + y * y) xs (x * x)).
  - apply sq_fold_init_compat. ring.
  - apply Qeq_trans with (fold_left (fun acc y => acc + y * y) xs (0 + x * x)).
    + apply sq_fold_init_compat. ring.
    + apply row_sq_sum_acc.
Qed.

Theorem row_sq_sum_singleton : forall x, row_sq_sum [x] == x * x.
Proof.
  intros x. unfold row_sq_sum. simpl. ring.
Qed.

(* ================================================================= *)
(** * Frobenius norm squared theorems                                 *)
(* ================================================================= *)

Theorem frobenius_nil : frobenius_sq_raw nil = 0.
Proof. reflexivity. Qed.

Theorem frobenius_singleton : forall x,
  frobenius_sq_raw [[x]] == x * x.
Proof.
  intros x. unfold frobenius_sq_raw. simpl.
  unfold row_sq_sum. simpl. ring.
Qed.

Theorem frobenius_cons : forall r rs,
  frobenius_sq_raw (r :: rs) == frobenius_sq_raw rs + row_sq_sum r.
Proof.
  intros r rs. unfold frobenius_sq_raw at 1. simpl.
  apply Qeq_trans with (fold_left (fun acc rv => acc + row_sq_sum rv) rs (row_sq_sum r)).
  - apply frob_fold_init_compat. ring.
  - apply Qeq_trans with (fold_left (fun acc rv => acc + row_sq_sum rv) rs (0 + row_sq_sum r)).
    + apply frob_fold_init_compat. ring.
    + apply frobenius_acc.
Qed.

Theorem frobenius_1x2 : forall a b,
  frobenius_sq_raw [[a; b]] == a * a + b * b.
Proof.
  intros a b. unfold frobenius_sq_raw. simpl.
  unfold row_sq_sum. simpl. ring.
Qed.

(* ================================================================= *)
(** * Non-negativity                                                  *)
(* ================================================================= *)

Lemma Q_sq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intros x.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - assert (Heq : x * x == (-x) * (-x)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma row_sq_sum_nonneg : forall r, 0 <= row_sq_sum r.
Proof.
  induction r as [| x xs IH].
  - unfold row_sq_sum. simpl. lra.
  - rewrite row_sq_sum_cons.
    assert (Hx : 0 <= x * x) by apply Q_sq_nonneg.
    lra.
Qed.

Theorem frobenius_nonneg : forall rows, 0 <= frobenius_sq_raw rows.
Proof.
  induction rows as [| r rs IH].
  - unfold frobenius_sq_raw. simpl. lra.
  - rewrite frobenius_cons.
    assert (Hr : 0 <= row_sq_sum r) by apply row_sq_sum_nonneg.
    lra.
Qed.

Theorem frobenius_nonneg_singleton : forall x,
  0 <= frobenius_sq_raw [[x]].
Proof. intros x. apply frobenius_nonneg. Qed.

(* ================================================================= *)
(** * Scale and addition on raw rows                                  *)
(* ================================================================= *)

Theorem scale_rows_nil : forall c, scale_rows c nil = nil.
Proof. reflexivity. Qed.

Theorem add_rows_nil : add_rows nil nil = nil.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** * Outer product theorems                                          *)
(* ================================================================= *)

Theorem outer_raw_nil_l : forall w, outer_raw nil w = nil.
Proof. reflexivity. Qed.

Theorem outer_raw_nil_r : forall v, outer_raw v nil = repeat nil (length v).
Proof.
  induction v as [| x xs IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Theorem outer_product_1x1 : forall a b,
  outer_raw [a] [b] = [[a * b]].
Proof. reflexivity. Qed.

Theorem outer_raw_length : forall v w,
  length (outer_raw v w) = length v.
Proof.
  induction v as [| x xs IH]; intros w; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(* ================================================================= *)
(** * Trace linearity — additive                                      *)
(* ================================================================= *)

(** nth of map2 Qplus with Qeq (same-length lists). *)
Lemma nth_map2_Qplus : forall (ra rb : list Q) (i : nat),
  length ra = length rb ->
  nth i (map2 Qplus ra rb) 0 == nth i ra 0 + nth i rb 0.
Proof.
  induction ra as [| a as2 IH]; intros [| b bs2] i Hlen; simpl in *.
  - destruct i; ring.
  - discriminate.
  - discriminate.
  - destruct i as [| i'].
    + ring.
    + apply IH. lia.
Qed.

(** Row-lengths match via Forall2. *)
Definition rows_compat (A B : list (list Q)) : Prop :=
  Forall2 (fun a b => length a = length b) A B.

Lemma gen_trace_add : forall A B i,
  rows_compat A B ->
  gen_trace (add_rows A B) i == gen_trace A i + gen_trace B i.
Proof.
  unfold rows_compat.
  intros A B i Hrc.
  generalize dependent i.
  induction Hrc as [| ra rb as_ bs Hlen Htl IH]; intros i.
  - unfold gen_trace. simpl. lra.
  - assert (H1 : gen_trace (add_rows (ra :: as_) (rb :: bs)) i ==
                  nth i (map2 Qplus ra rb) 0 + gen_trace (add_rows as_ bs) (S i)).
    { apply gen_trace_cons. }
    assert (H2 : gen_trace (ra :: as_) i == nth i ra 0 + gen_trace as_ (S i)).
    { apply gen_trace_cons. }
    assert (H3 : gen_trace (rb :: bs) i == nth i rb 0 + gen_trace bs (S i)).
    { apply gen_trace_cons. }
    assert (IHres : gen_trace (add_rows as_ bs) (S i) ==
                    gen_trace as_ (S i) + gen_trace bs (S i)).
    { apply IH. }
    assert (Hnth : nth i (map2 Qplus ra rb) 0 == nth i ra 0 + nth i rb 0).
    { apply nth_map2_Qplus. exact Hlen. }
    lra.
Qed.

Theorem trace_add_raw : forall A B,
  rows_compat A B ->
  trace_raw (add_rows A B) == trace_raw A + trace_raw B.
Proof.
  intros A B Hrc. apply gen_trace_add. exact Hrc.
Qed.

(* ================================================================= *)
(** * Trace linearity — scalar                                        *)
(* ================================================================= *)

(** nth of map (Qmult c) with Qeq. *)
Lemma nth_map_Qmult : forall (c : Q) (r : list Q) (i : nat),
  nth i (map (Qmult c) r) 0 == c * nth i r 0.
Proof.
  intros c. induction r as [| a as2 IH]; intros i; simpl.
  - destruct i; ring.
  - destruct i; [ring | apply IH].
Qed.

Lemma gen_trace_scale : forall c rows i,
  gen_trace (scale_rows c rows) i == c * gen_trace rows i.
Proof.
  intros c. induction rows as [| r rs IH]; intros i.
  - unfold gen_trace. simpl. ring.
  - rewrite gen_trace_cons. unfold scale_rows. simpl.
    fold (scale_rows c rs).
    rewrite gen_trace_cons.
    rewrite IH.
    rewrite nth_map_Qmult. ring.
Qed.

Theorem trace_scale_raw : forall c rows,
  trace_raw (scale_rows c rows) == c * trace_raw rows.
Proof.
  intros c rows. apply gen_trace_scale.
Qed.

(* ================================================================= *)
(** * Zero-rows helpers                                               *)
(* ================================================================= *)

Theorem zero_rows_length : forall m n,
  length (zero_rows m n) = m.
Proof.
  induction m as [| m' IH]; intros n; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(** TOTAL: 39 Qed, 0 Admitted, 0 axioms *)
