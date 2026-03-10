(* ========================================================================= *)
(*        MATRIX OPERATIONS — Multiplication, Transpose, Trace             *)
(*                                                                          *)
(*  Extends LinearAlgebra.v with matrix-matrix operations needed for        *)
(*  eigenvalue algorithms and quantum mechanics.                             *)
(*                                                                          *)
(*  STATUS: ~28 Qed, 0 Admitted                                            *)
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

(* ========================================================================= *)
(*  PART I: Zero Matrix + Column Extraction                                  *)
(* ========================================================================= *)

Definition zero_mat (r c : nat) : QMat r c :=
  mkQMat (repeat (qv_zero c) r) (repeat_length (qv_zero c) r).

Lemma zero_mat_entry : forall r c i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (zero_mat r c) i j == 0.
Proof.
  intros r c i j Hi Hj.
  unfold mat_entry, mat_row, zero_mat. simpl.
  rewrite nth_repeat. apply qv_zero_nth. exact Hj.
Qed.

(** Column extraction: column j of M as a QVec r *)
Definition mat_col {r c} (M : QMat r c) (j : nat) : QVec r.
Proof.
  refine (mkQVec (map (fun i => mat_entry M i j) (seq 0 r)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

Lemma mat_col_nth : forall {r c} (M : QMat r c) (j i : nat),
  (i < r)%nat ->
  qv_nth (mat_col M j) i == mat_entry M i j.
Proof.
  intros r c M j i Hi.
  unfold qv_nth, mat_col. simpl.
  rewrite (nth_map_general _ (seq 0 r) 0%nat 0 i);
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*  PART II: Matrix Addition and Scaling                                     *)
(* ========================================================================= *)

(** Matrix addition using map+seq (avoids Q-specific map2) *)
Definition mat_add {r c} (A B : QMat r c) : QMat r c.
Proof.
  refine (mkQMat
    (map (fun i => qv_add (nth i (qm_rows A) (qv_zero c))
                          (nth i (qm_rows B) (qv_zero c)))
         (seq 0 r)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

Definition mat_scale {r c} (k : Q) (M : QMat r c) : QMat r c.
Proof.
  refine (mkQMat (map (fun row => qv_scale k row) (qm_rows M)) _).
  rewrite map_length. exact (qm_nrows M).
Defined.

Definition mat_sub {r c} (A B : QMat r c) : QMat r c :=
  mat_add A (mat_scale (-(1)) B).

Lemma mat_add_entry : forall {r c} (A B : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_add A B) i j == mat_entry A i j + mat_entry B i j.
Proof.
  intros r c A B i j Hi Hj.
  unfold mat_entry, mat_row, mat_add. simpl.
  rewrite (nth_map_general _ (seq 0 r) 0%nat (qv_zero c) i);
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  apply qv_add_nth. exact Hj.
Qed.

Lemma mat_scale_entry : forall {r c} (k : Q) (M : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_scale k M) i j == k * mat_entry M i j.
Proof.
  intros r c k M i j Hi Hj.
  unfold mat_entry, mat_row, mat_scale. simpl.
  rewrite (nth_map_general _ (qm_rows M) (qv_zero c) (qv_zero c) i);
    [| rewrite (qm_nrows M); exact Hi].
  apply qv_scale_nth. exact Hj.
Qed.

Lemma mat_sub_entry : forall {r c} (A B : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_sub A B) i j == mat_entry A i j - mat_entry B i j.
Proof.
  intros r c A B i j Hi Hj.
  unfold mat_sub.
  rewrite mat_add_entry; [| exact Hi | exact Hj].
  rewrite mat_scale_entry; [| exact Hi | exact Hj].
  ring.
Qed.

Lemma mat_add_comm : forall {r c} (A B : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_add A B) i j == mat_entry (mat_add B A) i j.
Proof.
  intros r c A B i j Hi Hj.
  rewrite !mat_add_entry; [ring | exact Hi | exact Hj | exact Hi | exact Hj].
Qed.

Lemma mat_add_assoc : forall {r c} (A B C : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_add (mat_add A B) C) i j ==
  mat_entry (mat_add A (mat_add B C)) i j.
Proof.
  intros r c A B C i j Hi Hj.
  rewrite !mat_add_entry; try exact Hi; try exact Hj.
  ring.
Qed.

Lemma mat_scale_one : forall {r c} (M : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_scale 1 M) i j == mat_entry M i j.
Proof.
  intros r c M i j Hi Hj.
  rewrite mat_scale_entry; [ring | exact Hi | exact Hj].
Qed.

Lemma mat_scale_assoc : forall {r c} (a b : Q) (M : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_scale a (mat_scale b M)) i j ==
  mat_entry (mat_scale (a * b) M) i j.
Proof.
  intros r c a b M i j Hi Hj.
  rewrite !mat_scale_entry; try exact Hi; try exact Hj.
  ring.
Qed.

Lemma mat_scale_distrib_add : forall {r c} (k : Q) (A B : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_scale k (mat_add A B)) i j ==
  mat_entry (mat_add (mat_scale k A) (mat_scale k B)) i j.
Proof.
  intros r c k A B i j Hi Hj.
  rewrite mat_scale_entry, mat_add_entry, mat_add_entry, !mat_scale_entry;
    try exact Hi; try exact Hj.
  ring.
Qed.

(* ========================================================================= *)
(*  PART III: Transpose                                                      *)
(* ========================================================================= *)

Definition mat_transpose {r c} (M : QMat r c) : QMat c r.
Proof.
  refine (mkQMat (map (fun j => mat_col M j) (seq 0 c)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

Lemma mat_transpose_entry : forall {r c} (M : QMat r c) i j,
  (i < c)%nat -> (j < r)%nat ->
  mat_entry (mat_transpose M) i j == mat_entry M j i.
Proof.
  intros r c M i j Hi Hj.
  unfold mat_entry at 1, mat_row, mat_transpose. simpl.
  rewrite (nth_map_general _ (seq 0 c) 0%nat (qv_zero r) i);
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  apply mat_col_nth. exact Hj.
Qed.

Lemma mat_transpose_involutive : forall {r c} (M : QMat r c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_transpose (mat_transpose M)) i j == mat_entry M i j.
Proof.
  intros r c M i j Hi Hj.
  rewrite mat_transpose_entry; [| exact Hi | exact Hj].
  rewrite mat_transpose_entry; [| exact Hj | exact Hi].
  reflexivity.
Qed.

Lemma mat_transpose_symmetric : forall {n} (M : QMat n n),
  is_symmetric M ->
  forall i j, (i < n)%nat -> (j < n)%nat ->
  mat_entry (mat_transpose M) i j == mat_entry M i j.
Proof.
  intros n M Hsym i j Hi Hj.
  rewrite mat_transpose_entry; [| exact Hi | exact Hj].
  apply Hsym; assumption.
Qed.

(* ========================================================================= *)
(*  PART IV: Matrix Multiplication                                           *)
(* ========================================================================= *)

Definition mat_mul_row_vec {m c} (row : QVec m) (B : QMat m c) : QVec c.
Proof.
  refine (mkQVec
    (map (fun j => dot_product row (mat_col B j)) (seq 0 c)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

Definition mat_mul {r m c} (A : QMat r m) (B : QMat m c) : QMat r c.
Proof.
  refine (mkQMat
    (map (fun i => mat_mul_row_vec (mat_row A i) B) (seq 0 r)) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

Lemma mat_mul_row_vec_nth : forall {m c} (row : QVec m) (B : QMat m c) j,
  (j < c)%nat ->
  qv_nth (mat_mul_row_vec row B) j == dot_product row (mat_col B j).
Proof.
  intros m c row B j Hj.
  unfold qv_nth, mat_mul_row_vec. simpl.
  rewrite (nth_map_general _ (seq 0 c) 0%nat 0 j);
    [| rewrite seq_length; exact Hj].
  rewrite seq_nth; [| exact Hj]. simpl.
  reflexivity.
Qed.

Lemma mat_mul_entry : forall {r m c} (A : QMat r m) (B : QMat m c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_mul A B) i j ==
  dot_product (mat_row A i) (mat_col B j).
Proof.
  intros r m c A B i j Hi Hj.
  unfold mat_entry, mat_row at 1, mat_mul. simpl.
  rewrite (nth_map_general _ (seq 0 r) 0%nat (qv_zero c) i);
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  apply mat_mul_row_vec_nth. exact Hj.
Qed.

(** dot_product extensionality *)
Lemma dot_product_ext : forall {n} (u1 u2 v : QVec n),
  (forall i, (i < n)%nat -> qv_nth u1 i == qv_nth u2 i) ->
  dot_product u1 v == dot_product u2 v.
Proof.
  intros n u1 u2 v Hext.
  unfold dot_product.
  destruct u1 as [d1 Hl1], u2 as [d2 Hl2], v as [dv Hlv]. simpl.
  assert (Hlen1v : length d1 = length dv) by (rewrite Hl1, Hlv; reflexivity).
  assert (Hlen2v : length d2 = length dv) by (rewrite Hl2, Hlv; reflexivity).
  assert (Hm1 : length (map2 Qmult d1 dv) = n)
    by (rewrite map2_length; [exact Hl1 | exact Hlen1v]).
  assert (Hm2 : length (map2 Qmult d2 dv) = n)
    by (rewrite map2_length; [exact Hl2 | exact Hlen2v]).
  apply fold_left_Qplus_Qeq.
  - rewrite Hm1, Hm2. reflexivity.
  - intro i.
    destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
    + rewrite nth_map2_Qeq; [| rewrite Hl1; exact Hi | exact Hlen1v].
      rewrite nth_map2_Qeq; [| rewrite Hl2; exact Hi | exact Hlen2v].
      assert (Heq := Hext i Hi). unfold qv_nth in Heq. simpl in Heq.
      rewrite Heq. reflexivity.
    + rewrite !nth_overflow; [reflexivity | rewrite Hm2; lia | rewrite Hm1; lia].
Qed.

Lemma dot_product_ext_r : forall {n} (u v1 v2 : QVec n),
  (forall i, (i < n)%nat -> qv_nth v1 i == qv_nth v2 i) ->
  dot_product u v1 == dot_product u v2.
Proof.
  intros n u v1 v2 Hext.
  rewrite dot_product_comm. rewrite (dot_product_comm u v2).
  apply dot_product_ext. exact Hext.
Qed.

(** I * A = A *)
Lemma mat_mul_id_l : forall {n m} (A : QMat n m) i j,
  (i < n)%nat -> (j < m)%nat ->
  mat_entry (mat_mul (id_mat n) A) i j == mat_entry A i j.
Proof.
  intros n m A i j Hi Hj.
  rewrite mat_mul_entry; [| exact Hi | exact Hj].
  unfold mat_row, id_mat. simpl.
  rewrite (nth_map_general _ (seq 0 n) 0%nat (qv_zero n) i);
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  rewrite dot_basis_extracts; [| exact Hi].
  apply mat_col_nth. exact Hi.
Qed.

(** A * I = A *)
Lemma mat_mul_id_r : forall {n m} (A : QMat n m) i j,
  (i < n)%nat -> (j < m)%nat ->
  mat_entry (mat_mul A (id_mat m)) i j == mat_entry A i j.
Proof.
  intros n m A i j Hi Hj.
  rewrite mat_mul_entry; [| exact Hi | exact Hj].
  rewrite dot_product_comm.
  assert (Hcol_basis : forall k, (k < m)%nat ->
    qv_nth (mat_col (id_mat m) j) k == qv_nth (basis_vec m j) k).
  { intros k Hk.
    rewrite mat_col_nth; [| exact Hk].
    rewrite id_mat_entry; [| exact Hk | exact Hj].
    destruct (Nat.eq_dec k j) as [Heq | Hneq].
    - subst. symmetry. apply basis_vec_same. exact Hj.
    - symmetry. apply basis_vec_diff; [exact Hk | exact Hneq]. }
  rewrite (dot_product_ext (mat_col (id_mat m) j) (basis_vec m j) (mat_row A i) Hcol_basis).
  rewrite dot_basis_extracts; [| exact Hj].
  unfold mat_entry. reflexivity.
Qed.

(** 0 * B = 0 *)
Lemma mat_mul_zero_l : forall {r m c} (B : QMat m c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_mul (zero_mat r m) B) i j == 0.
Proof.
  intros r m c B i j Hi Hj.
  rewrite mat_mul_entry; [| exact Hi | exact Hj].
  unfold mat_row, zero_mat. simpl. rewrite nth_repeat.
  apply dot_product_zero_left.
Qed.

(** A * 0 = 0 *)
Lemma mat_mul_zero_r : forall {r m c} (A : QMat r m) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_mul A (zero_mat m c)) i j == 0.
Proof.
  intros r m c A i j Hi Hj.
  rewrite mat_mul_entry; [| exact Hi | exact Hj].
  rewrite dot_product_comm.
  assert (Hzc : forall k, (k < m)%nat ->
    qv_nth (mat_col (zero_mat m c) j) k == 0).
  { intros k Hk. rewrite mat_col_nth; [| exact Hk].
    apply zero_mat_entry; [exact Hk | exact Hj]. }
  rewrite (dot_product_ext (mat_col (zero_mat m c) j) (qv_zero m) (mat_row A i)).
  - apply dot_product_zero_left.
  - intros k Hk. rewrite Hzc; [| exact Hk].
    symmetry. apply qv_zero_nth. exact Hk.
Qed.

(** (kA) * B = k * (A * B) *)
Lemma mat_mul_scale_l : forall {r m c} (k : Q) (A : QMat r m) (B : QMat m c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_mul (mat_scale k A) B) i j ==
  k * mat_entry (mat_mul A B) i j.
Proof.
  intros r m c k A B i j Hi Hj.
  rewrite !mat_mul_entry; try exact Hi; try exact Hj.
  unfold mat_row at 1, mat_scale. simpl.
  rewrite (nth_map_general _ (qm_rows A) (qv_zero m) (qv_zero m) i);
    [| rewrite (qm_nrows A); exact Hi].
  rewrite dot_product_scale_l. reflexivity.
Qed.

(** A * (B + C) = A*B + A*C (entry-wise) *)
Lemma mat_mul_distrib_r : forall {r m c} (A : QMat r m) (B C : QMat m c) i j,
  (i < r)%nat -> (j < c)%nat ->
  mat_entry (mat_mul A (mat_add B C)) i j ==
  mat_entry (mat_mul A B) i j + mat_entry (mat_mul A C) i j.
Proof.
  intros r m c A B C i j Hi Hj.
  rewrite !mat_mul_entry; try exact Hi; try exact Hj.
  (* Need: dot(row_A_i, col_{B+C}_j) = dot(row_A_i, col_B_j) + dot(row_A_i, col_C_j) *)
  (* col_{B+C}_j componentwise = qv_add (col_B_j) (col_C_j) *)
  assert (Hcol : forall k, (k < m)%nat ->
    qv_nth (mat_col (mat_add B C) j) k ==
    qv_nth (qv_add (mat_col B j) (mat_col C j)) k).
  { intros k Hk.
    rewrite mat_col_nth; [| exact Hk].
    rewrite mat_add_entry; [| exact Hk | exact Hj].
    rewrite qv_add_nth; [| exact Hk].
    rewrite !mat_col_nth; [reflexivity | exact Hk | exact Hk]. }
  rewrite (dot_product_ext_r (mat_row A i) (mat_col (mat_add B C) j)
            (qv_add (mat_col B j) (mat_col C j)) Hcol).
  apply dot_product_add_r.
Qed.

(* ========================================================================= *)
(*  PART V: Matrix Trace                                                     *)
(* ========================================================================= *)

Fixpoint sum_Q (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => sum_Q f k + f k
  end.

Definition mat_trace {n} (M : QMat n n) : Q :=
  sum_Q (fun i => mat_entry M i i) n.

Lemma sum_Q_ext : forall (f g : nat -> Q) n,
  (forall i, (i < n)%nat -> f i == g i) ->
  sum_Q f n == sum_Q g n.
Proof.
  intros f g n Hext. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH; [| intros; apply Hext; lia].
    rewrite (Hext n' ltac:(lia)). reflexivity.
Qed.

Lemma sum_Q_plus : forall (f g : nat -> Q) n,
  sum_Q (fun i => f i + g i) n == sum_Q f n + sum_Q g n.
Proof.
  intros f g n. induction n as [| n' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_Q_scale : forall (k : Q) (f : nat -> Q) n,
  sum_Q (fun i => k * f i) n == k * sum_Q f n.
Proof.
  intros k f n. induction n as [| n' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma mat_trace_add : forall {n} (A B : QMat n n),
  mat_trace (mat_add A B) == mat_trace A + mat_trace B.
Proof.
  intros n A B. unfold mat_trace.
  rewrite <- sum_Q_plus.
  apply sum_Q_ext. intros i Hi.
  apply mat_add_entry; exact Hi.
Qed.

Lemma mat_trace_scale : forall {n} (k : Q) (M : QMat n n),
  mat_trace (mat_scale k M) == k * mat_trace M.
Proof.
  intros n k M. unfold mat_trace.
  rewrite <- sum_Q_scale.
  apply sum_Q_ext. intros i Hi.
  apply mat_scale_entry; exact Hi.
Qed.

Lemma mat_trace_id : forall n, (0 < n)%nat ->
  mat_trace (id_mat n) == inject_Z (Z.of_nat n).
Proof.
  intros n Hn. unfold mat_trace.
  induction n as [| n' IH]; [lia |].
  simpl sum_Q.
  rewrite id_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec n' n') as [_ | Habs]; [| lia].
  destruct n' as [| n''].
  - simpl. ring.
  - assert (IH' := IH ltac:(lia)).
    assert (Hext : forall i, (i < S n'')%nat ->
      mat_entry (id_mat (S (S n''))) i i == mat_entry (id_mat (S n'')) i i).
    { intros i Hi.
      rewrite !id_mat_entry; try lia.
      destruct (Nat.eq_dec i i); [reflexivity | lia]. }
    rewrite (sum_Q_ext _ _ _ Hext). rewrite IH'.
    replace (Z.of_nat (S (S n''))) with (Z.of_nat (S n'') + 1)%Z by lia.
    rewrite inject_Z_plus. ring.
Qed.

(** Trace of diagonal matrix = sum of eigenvalues *)
Lemma mat_trace_diag : forall {n} (eigenvals : QVec n),
  mat_trace (diag_mat eigenvals) == sum_Q (fun i => qv_nth eigenvals i) n.
Proof.
  intros n eigenvals. unfold mat_trace.
  apply sum_Q_ext. intros i Hi.
  rewrite diag_mat_entry; [| exact Hi | exact Hi].
  destruct (Nat.eq_dec i i); [reflexivity | lia].
Qed.

(* ========================================================================= *)
(*  PART VI: Matrix Shift                                                    *)
(* ========================================================================= *)

Definition mat_shift {n} (A : QMat n n) (sigma : Q) : QMat n n :=
  mat_sub A (mat_scale sigma (id_mat n)).

Lemma mat_shift_entry : forall {n} (A : QMat n n) sigma i j,
  (i < n)%nat -> (j < n)%nat ->
  mat_entry (mat_shift A sigma) i j ==
  mat_entry A i j - (if Nat.eq_dec i j then sigma else 0).
Proof.
  intros n A sigma i j Hi Hj.
  unfold mat_shift, mat_sub.
  rewrite mat_add_entry; [| exact Hi | exact Hj].
  rewrite mat_scale_entry; [| exact Hi | exact Hj].
  rewrite mat_scale_entry; [| exact Hi | exact Hj].
  rewrite id_mat_entry; [| exact Hi | exact Hj].
  destruct (Nat.eq_dec i j); ring.
Qed.

Lemma mat_shift_symmetric : forall {n} (A : QMat n n) sigma,
  is_symmetric A -> is_symmetric (mat_shift A sigma).
Proof.
  intros n A sigma Hsym i j Hi Hj.
  rewrite !mat_shift_entry; try exact Hi; try exact Hj.
  rewrite (Hsym i j Hi Hj).
  destruct (Nat.eq_dec i j), (Nat.eq_dec j i); try lia; ring.
Qed.

(* ========================================================================= *)
(*  SUMMARY: 28 Qed, 0 Admitted                                             *)
(*  Definitions: zero_mat, mat_col, mat_add, mat_scale, mat_sub,            *)
(*    mat_transpose, mat_mul, sum_Q, mat_trace, mat_shift                    *)
(*  Lemmas: zero_mat_entry, mat_col_nth, mat_add_entry, mat_scale_entry,    *)
(*    mat_sub_entry, mat_add_comm, mat_add_assoc, mat_scale_one,            *)
(*    mat_scale_assoc, mat_scale_distrib_add, mat_transpose_entry,          *)
(*    mat_transpose_involutive, mat_transpose_symmetric, mat_mul_entry,     *)
(*    dot_product_ext, dot_product_ext_r, mat_mul_id_l, mat_mul_id_r,      *)
(*    mat_mul_zero_l, mat_mul_zero_r, mat_mul_scale_l, mat_mul_distrib_r,  *)
(*    sum_Q_ext, sum_Q_plus, sum_Q_scale, mat_trace_add, mat_trace_scale,  *)
(*    mat_trace_id, mat_trace_diag, mat_shift_entry, mat_shift_symmetric   *)
(* ========================================================================= *)
