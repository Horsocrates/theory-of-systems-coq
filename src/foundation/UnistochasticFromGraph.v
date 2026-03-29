(** * UnistochasticFromGraph.v -- |U|^2 from orthogonal U -> doubly stochastic + unistochastic
    Elements: orthogonal matrix, elementwise square, doubly stochastic matrix
    Roles:    orthogonality -> row/col normalization, squaring -> non-negativity
    Rules:    orth_diag_is_row_sum, orth_implies_gamma_row_1, unistochastic_from_cayley
    Status:   Foundation File (Unistochastic)
    STATUS: 19 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================ *)
(** ** Matrix definitions over Q *)
(* ================================================================ *)

Definition Mat := nat -> nat -> Q.

Definition mat_prod (A B : Mat) (N : nat) (i j : nat) : Q :=
  fold_left (fun acc k => acc + A i k * B k j) (seq 0 N) 0.

Definition mat_trans (A : Mat) (i j : nat) : Q := A j i.

Definition is_orthogonal (U : Mat) (N : nat) : Prop :=
  forall i j, (i < N)%nat -> (j < N)%nat ->
  mat_prod U (mat_trans U) N i j == (if Nat.eqb i j then 1 else 0).

Definition gamma_of (U : Mat) (i j : nat) : Q := U i j * U i j.

Definition gamma_row_sum (U : Mat) (N : nat) (i : nat) : Q :=
  fold_left (fun acc j => acc + U i j * U i j) (seq 0 N) 0.

Definition gamma_col_sum (U : Mat) (N : nat) (j : nat) : Q :=
  fold_left (fun acc i => acc + U i j * U i j) (seq 0 N) 0.

(* ================================================================ *)
(** ** General structural lemmas *)
(* ================================================================ *)

(** The diagonal of UU^T equals the row sum of Gamma *)
Lemma orth_diag_is_row_sum : forall (U : Mat) (N : nat) (i : nat),
  mat_prod U (mat_trans U) N i i == gamma_row_sum U N i.
Proof.
  intros U N i.
  unfold mat_prod, mat_trans, gamma_row_sum.
  reflexivity.
Qed.

(** If U is orthogonal, gamma row sum = 1 *)
Lemma orth_implies_gamma_row_1 : forall (U : Mat) (N : nat) (i : nat),
  is_orthogonal U N -> (i < N)%nat ->
  gamma_row_sum U N i == 1.
Proof.
  intros U N i Horth Hi.
  rewrite <- orth_diag_is_row_sum.
  specialize (Horth i i Hi Hi).
  rewrite Nat.eqb_refl in Horth.
  exact Horth.
Qed.

(** The diagonal of U^TU equals the col sum of Gamma *)
Lemma orth_trans_diag_is_col_sum : forall (U : Mat) (N : nat) (j : nat),
  mat_prod (mat_trans U) U N j j == gamma_col_sum U N j.
Proof.
  intros U N j.
  unfold mat_prod, mat_trans, gamma_col_sum.
  reflexivity.
Qed.

(** Transpose orthogonality: UU^T = I implies U^TU = I for the diagonal *)
(** We state this as a hypothesis since the general proof requires determinant theory *)
Definition is_transpose_orthogonal (U : Mat) (N : nat) : Prop :=
  forall i j, (i < N)%nat -> (j < N)%nat ->
  mat_prod (mat_trans U) U N i j == (if Nat.eqb i j then 1 else 0).

Lemma trans_orth_implies_gamma_col_1 : forall (U : Mat) (N : nat) (j : nat),
  is_transpose_orthogonal U N -> (j < N)%nat ->
  gamma_col_sum U N j == 1.
Proof.
  intros U N j Horth Hj.
  rewrite <- orth_trans_diag_is_col_sum.
  specialize (Horth j j Hj Hj).
  rewrite Nat.eqb_refl in Horth.
  exact Horth.
Qed.

(* ================================================================ *)
(** ** Unistochastic definition *)
(* ================================================================ *)

Definition is_doubly_stochastic (Gamma : Mat) (N : nat) : Prop :=
  (forall i, (i < N)%nat ->
    fold_left (fun acc j => acc + Gamma i j) (seq 0 N) 0 == 1) /\
  (forall j, (j < N)%nat ->
    fold_left (fun acc i => acc + Gamma i j) (seq 0 N) 0 == 1).

Definition is_unistochastic (Gamma : Mat) (N : nat) : Prop :=
  exists U : Mat,
    is_orthogonal U N /\
    is_transpose_orthogonal U N /\
    (forall i j, Gamma i j == gamma_of U i j).

(* ================================================================ *)
(** ** Concrete 2x2 Cayley matrix at theta=1 *)
(** U = [[3/5, -4/5], [4/5, 3/5]] *)
(* ================================================================ *)

Definition U2 (i j : nat) : Q :=
  match i, j with
  | O, O => 3 # 5
  | O, S O => -(4 # 5)
  | S O, O => 4 # 5
  | S O, S O => 3 # 5
  | _, _ => 0
  end.

Definition Gamma2 (i j : nat) : Q :=
  match i, j with
  | O, O => 9 # 25
  | O, S O => 16 # 25
  | S O, O => 16 # 25
  | S O, S O => 9 # 25
  | _, _ => 0
  end.

Lemma gamma_2_DS_at_1 :
  (9 # 25) + (16 # 25) == 1 /\
  (16 # 25) + (9 # 25) == 1 /\
  (9 # 25) + (16 # 25) == 1 /\
  (16 # 25) + (9 # 25) == 1.
Proof.
  repeat split; reflexivity.
Qed.

Lemma U2_orthogonal : is_orthogonal U2 2.
Proof.
  intros i j Hi Hj.
  unfold mat_prod, mat_trans, U2; simpl.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia; reflexivity.
Qed.

Lemma U2_trans_orthogonal : is_transpose_orthogonal U2 2.
Proof.
  intros i j Hi Hj.
  unfold mat_prod, mat_trans, U2; simpl.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia; reflexivity.
Qed.

Lemma Gamma2_is_gamma_of_U2 : forall i j,
  Gamma2 i j == gamma_of U2 i j.
Proof.
  intros i j.
  unfold Gamma2, gamma_of, U2.
  destruct i as [|[|i']]; destruct j as [|[|j']]; reflexivity.
Qed.

Lemma Gamma2_unistochastic : is_unistochastic Gamma2 2.
Proof.
  exists U2. split; [|split].
  - exact U2_orthogonal.
  - exact U2_trans_orthogonal.
  - exact Gamma2_is_gamma_of_U2.
Qed.

(* ================================================================ *)
(** ** Concrete 3x3 Cayley matrix *)
(** U_3 = [[2/3, -2/3, 1/3], [2/3, 1/3, -2/3], [1/3, 2/3, 2/3]] *)
(* ================================================================ *)

Definition U3 (i j : nat) : Q :=
  match i, j with
  | O, O => 2 # 3
  | O, S O => -(2 # 3)
  | O, S (S O) => 1 # 3
  | S O, O => 2 # 3
  | S O, S O => 1 # 3
  | S O, S (S O) => -(2 # 3)
  | S (S O), O => 1 # 3
  | S (S O), S O => 2 # 3
  | S (S O), S (S O) => 2 # 3
  | _, _ => 0
  end.

Definition Gamma3 (i j : nat) : Q :=
  match i, j with
  | O, O => 4 # 9
  | O, S O => 4 # 9
  | O, S (S O) => 1 # 9
  | S O, O => 4 # 9
  | S O, S O => 1 # 9
  | S O, S (S O) => 4 # 9
  | S (S O), O => 1 # 9
  | S (S O), S O => 4 # 9
  | S (S O), S (S O) => 4 # 9
  | _, _ => 0
  end.

Lemma gamma_3_DS :
  (4 # 9) + (4 # 9) + (1 # 9) == 1 /\
  (4 # 9) + (1 # 9) + (4 # 9) == 1 /\
  (1 # 9) + (4 # 9) + (4 # 9) == 1 /\
  (4 # 9) + (4 # 9) + (1 # 9) == 1 /\
  (4 # 9) + (1 # 9) + (4 # 9) == 1 /\
  (1 # 9) + (4 # 9) + (4 # 9) == 1.
Proof.
  repeat split; reflexivity.
Qed.

Lemma U3_orthogonal : is_orthogonal U3 3.
Proof.
  intros i j Hi Hj.
  unfold mat_prod, mat_trans, U3; simpl.
  destruct i as [|[|[|i']]]; destruct j as [|[|[|j']]]; try lia; reflexivity.
Qed.

Lemma U3_trans_orthogonal : is_transpose_orthogonal U3 3.
Proof.
  intros i j Hi Hj.
  unfold mat_prod, mat_trans, U3; simpl.
  destruct i as [|[|[|i']]]; destruct j as [|[|[|j']]]; try lia; reflexivity.
Qed.

Lemma Gamma3_is_gamma_of_U3 : forall i j,
  Gamma3 i j == gamma_of U3 i j.
Proof.
  intros i j.
  unfold Gamma3, gamma_of, U3.
  destruct i as [|[|[|i']]]; destruct j as [|[|[|j']]]; reflexivity.
Qed.

Lemma Gamma3_unistochastic : is_unistochastic Gamma3 3.
Proof.
  exists U3. split; [|split].
  - exact U3_orthogonal.
  - exact U3_trans_orthogonal.
  - exact Gamma3_is_gamma_of_U3.
Qed.

(* ================================================================ *)
(** ** Synthesis: unistochastic implies doubly stochastic *)
(* ================================================================ *)

Lemma gamma_row_sum_eq_fold : forall (U : Mat) (N : nat) (i : nat),
  gamma_row_sum U N i ==
  fold_left (fun acc j => acc + gamma_of U i j) (seq 0 N) 0.
Proof.
  intros U N i.
  unfold gamma_row_sum, gamma_of.
  reflexivity.
Qed.

Lemma gamma_col_sum_eq_fold : forall (U : Mat) (N : nat) (j : nat),
  gamma_col_sum U N j ==
  fold_left (fun acc i => acc + gamma_of U i j) (seq 0 N) 0.
Proof.
  intros U N j.
  unfold gamma_col_sum, gamma_of.
  reflexivity.
Qed.

(** Helper: fold_left with Qeq-equal functions for row sums *)
Lemma fold_left_gamma_row : forall (Gamma : Mat) (U : Mat) (i : nat) (l : list nat),
  (forall i0 j0, Gamma i0 j0 == gamma_of U i0 j0) ->
  fold_left (fun acc j => acc + Gamma i j) l 0 ==
  fold_left (fun acc j => acc + gamma_of U i j) l 0.
Proof.
  intros Gamma0 U0 i0 l HG.
  induction l as [|k ks IH].
  - reflexivity.
  - simpl.
    assert (Hstep : 0 + Gamma0 i0 k == 0 + gamma_of U0 i0 k).
    { rewrite (HG i0 k). reflexivity. }
    revert Hstep.
    generalize (0 + Gamma0 i0 k) as a.
    generalize (0 + gamma_of U0 i0 k) as b.
    intros b a Hab.
    clear -HG Hab.
    revert a b Hab.
    induction ks as [|x xs IHks]; intros a b Hab.
    + exact Hab.
    + simpl. apply IHks.
      rewrite Hab, (HG i0 x). reflexivity.
Qed.

Lemma fold_left_gamma_col : forall (Gamma : Mat) (U : Mat) (j : nat) (l : list nat),
  (forall i0 j0, Gamma i0 j0 == gamma_of U i0 j0) ->
  fold_left (fun acc i => acc + Gamma i j) l 0 ==
  fold_left (fun acc i => acc + gamma_of U i j) l 0.
Proof.
  intros Gamma0 U0 j0 l HG.
  induction l as [|k ks IH].
  - reflexivity.
  - simpl.
    assert (Hstep : 0 + Gamma0 k j0 == 0 + gamma_of U0 k j0).
    { rewrite (HG k j0). reflexivity. }
    revert Hstep.
    generalize (0 + Gamma0 k j0) as a.
    generalize (0 + gamma_of U0 k j0) as b.
    intros b a Hab.
    clear -HG Hab.
    revert a b Hab.
    induction ks as [|x xs IHks]; intros a b Hab.
    + exact Hab.
    + simpl. apply IHks.
      rewrite Hab, (HG x j0). reflexivity.
Qed.

(** Main theorem: unistochastic => doubly stochastic *)
Theorem unistochastic_implies_DS : forall (Gamma : Mat) (N : nat),
  is_unistochastic Gamma N -> is_doubly_stochastic Gamma N.
Proof.
  intros Gamma N [U [Horth [Htorth HGamma]]].
  split.
  - (* Row sums *)
    intros i Hi.
    apply Qeq_trans with (fold_left (fun acc j => acc + gamma_of U i j) (seq 0 N) 0).
    + apply fold_left_gamma_row. exact HGamma.
    + rewrite <- gamma_row_sum_eq_fold.
      exact (orth_implies_gamma_row_1 U N i Horth Hi).
  - (* Col sums *)
    intros j Hj.
    apply Qeq_trans with (fold_left (fun acc i => acc + gamma_of U i j) (seq 0 N) 0).
    + apply fold_left_gamma_col. exact HGamma.
    + rewrite <- gamma_col_sum_eq_fold.
      exact (trans_orth_implies_gamma_col_1 U N j Htorth Hj).
Qed.
