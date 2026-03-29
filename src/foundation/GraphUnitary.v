(* ========================================================================= *)
(*  GraphUnitary.v                                                          *)
(*                                                                          *)
(*  Graph adjacency + Cayley transform -> unitary (orthogonal) matrices.    *)
(*  Chain graphs produce anti-symmetric M; Cayley U = (I+M/2)(I-M/2)^{-1}  *)
(*  yields orthogonal U with doubly stochastic |U|^2.                       *)
(*                                                                          *)
(*  E/R/R: Elements = matrix entries (Q-valued);                            *)
(*         Roles = orthogonality (U * U^T = I), doubly stochastic Gamma;    *)
(*         Rules = Cayley transform preserves anti-symmetry -> unitarity.   *)
(*  STATUS: 26 Qed, 0 Admitted, 0 axioms                                   *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== N=2 Chain Graph ===== *)

(* Anti-symmetric matrix from 2-node chain graph *)
Definition M_2 (theta : Q) (i j : nat) : Q :=
  match i, j with
  | O, S O => -(theta)
  | S O, O => theta
  | _, _ => 0
  end.

(* M_2 is anti-symmetric *)
Lemma M_2_antisym : forall theta i j,
  (i < 2)%nat -> (j < 2)%nat ->
  M_2 theta i j == -(M_2 theta j i).
Proof.
  intros theta i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; simpl; try lia; try lra.
Qed.

(* Cayley transform for 2x2 anti-symmetric matrix:
   U = (I + M/2)(I - M/2)^{-1}
   For anti-symmetric M with parameter a:
   U = 1/(1+a^2/4) * [[(1-a^2/4), -a], [a, (1-a^2/4)]] *)
Definition cayley_2 (a : Q) (i j : nat) : Q :=
  let d := 1 + a * a / 4 in
  match i, j with
  | O, O => (1 - a * a / 4) / d
  | O, S O => (-(a)) / d
  | S O, O => a / d
  | S O, S O => (1 - a * a / 4) / d
  | _, _ => 0
  end.

(* Denominator d = 1 + a^2/4 is positive *)
Lemma sq_nonneg : forall a : Q, 0 <= a * a.
Proof.
  intros a.
  destruct (Qlt_le_dec a 0) as [Hn|Hp].
  - assert (Heq : a * a == (-a) * (-a)) by ring.
    rewrite Heq.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma inv4_pos : 0 < / 4.
Proof. reflexivity. Qed.

Lemma sq_div4_nonneg : forall a : Q, 0 <= a * a / 4.
Proof.
  intros a.
  assert (H := sq_nonneg a).
  unfold Qdiv.
  apply Qmult_le_0_compat.
  - exact H.
  - apply Qlt_le_weak. exact inv4_pos.
Qed.

Lemma denom_pos : forall a : Q, 0 < 1 + a * a / 4.
Proof.
  intros a. generalize (sq_div4_nonneg a). lra.
Qed.

(* Denominator is non-zero (in the form field tactic produces) *)
Lemma denom_neq_0 : forall a : Q, ~ (1 + a * a / 4 == 0).
Proof.
  intros a H. generalize (denom_pos a). lra.
Qed.

Lemma four_plus_sq_neq_0 : forall a : Q, ~ (4 + a * a == 0).
Proof.
  intros a H.
  assert (Hsq := sq_nonneg a). lra.
Qed.

(* Helper tactic for field proofs with cayley_2 *)
Ltac cayley_2_field :=
  unfold cayley_2; field; apply four_plus_sq_neq_0.

(* Orthogonality: row 0 dot row 0 of U = 1 *)
Lemma cayley_2_orth_00 : forall a : Q,
  cayley_2 a O O * cayley_2 a O O + cayley_2 a O (S O) * cayley_2 a O (S O) == 1.
Proof. intros a. cayley_2_field. Qed.

(* Orthogonality: row 1 dot row 1 of U = 1 *)
Lemma cayley_2_orth_11 : forall a : Q,
  cayley_2 a (S O) O * cayley_2 a (S O) O +
  cayley_2 a (S O) (S O) * cayley_2 a (S O) (S O) == 1.
Proof. intros a. cayley_2_field. Qed.

(* Orthogonality: row 0 dot row 1 = 0 *)
Lemma cayley_2_orth_01 : forall a : Q,
  cayley_2 a O O * cayley_2 a (S O) O +
  cayley_2 a O (S O) * cayley_2 a (S O) (S O) == 0.
Proof. intros a. cayley_2_field. Qed.

(* Column orthogonality: col 0 dot col 0 = 1 *)
Lemma cayley_2_col_orth_00 : forall a : Q,
  cayley_2 a O O * cayley_2 a O O +
  cayley_2 a (S O) O * cayley_2 a (S O) O == 1.
Proof. intros a. cayley_2_field. Qed.

(* Gamma = |U|^2 row sum for row 0 equals 1 *)
Lemma gamma_2_row_0 : forall a : Q,
  cayley_2 a O O * cayley_2 a O O +
  cayley_2 a O (S O) * cayley_2 a O (S O) == 1.
Proof.
  exact cayley_2_orth_00.
Qed.

(* Gamma = |U|^2 row sum for row 1 equals 1 *)
Lemma gamma_2_row_1 : forall a : Q,
  cayley_2 a (S O) O * cayley_2 a (S O) O +
  cayley_2 a (S O) (S O) * cayley_2 a (S O) (S O) == 1.
Proof.
  exact cayley_2_orth_11.
Qed.

(* ===== Concrete at theta = 1 ===== *)

(* U at theta=1: [[3/5, -4/5], [4/5, 3/5]] *)
Lemma cayley_2_at_1_00 : cayley_2 1 O O == 3 # 5.
Proof. unfold cayley_2. field. Qed.

Lemma cayley_2_at_1_01 : cayley_2 1 O (S O) == -(4 # 5).
Proof. unfold cayley_2. field. Qed.

Lemma cayley_2_at_1_10 : cayley_2 1 (S O) O == 4 # 5.
Proof. unfold cayley_2. field. Qed.

Lemma cayley_2_at_1_11 : cayley_2 1 (S O) (S O) == 3 # 5.
Proof. unfold cayley_2. field. Qed.

(* ===== N=3 Chain Graph ===== *)

(* Anti-symmetric matrix from 3-node chain graph *)
Definition M_3 (theta : Q) (i j : nat) : Q :=
  match i, j with
  | O, S O => -(theta)
  | S O, O => theta
  | S O, S (S O) => -(theta)
  | S (S O), S O => theta
  | _, _ => 0
  end.

(* M_3 is anti-symmetric *)
Lemma M_3_antisym : forall theta i j,
  (i < 3)%nat -> (j < 3)%nat ->
  M_3 theta i j == -(M_3 theta j i).
Proof.
  intros theta i j Hi Hj.
  destruct i as [|[|[|i']]]; destruct j as [|[|[|j']]];
    simpl; try lia; try lra.
Qed.

(* Cayley U for 3-node chain at theta=1:
   U = [[2/3, -2/3, 1/3], [2/3, 1/3, -2/3], [1/3, 2/3, 2/3]] *)
Definition U_3_cayley (i j : nat) : Q :=
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

(* Gamma = |U|^2 for N=3 *)
Definition Gamma_3 (i j : nat) : Q :=
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

(* Row orthogonality of U_3: row 0 has norm 1 *)
Lemma U_3_orth_row0 :
  U_3_cayley O O * U_3_cayley O O +
  U_3_cayley O (S O) * U_3_cayley O (S O) +
  U_3_cayley O (S (S O)) * U_3_cayley O (S (S O)) == 1.
Proof. unfold U_3_cayley. ring. Qed.

(* Row orthogonality: row 1 has norm 1 *)
Lemma U_3_orth_row1 :
  U_3_cayley (S O) O * U_3_cayley (S O) O +
  U_3_cayley (S O) (S O) * U_3_cayley (S O) (S O) +
  U_3_cayley (S O) (S (S O)) * U_3_cayley (S O) (S (S O)) == 1.
Proof. unfold U_3_cayley. ring. Qed.

(* Row orthogonality: row 2 has norm 1 *)
Lemma U_3_orth_row2 :
  U_3_cayley (S (S O)) O * U_3_cayley (S (S O)) O +
  U_3_cayley (S (S O)) (S O) * U_3_cayley (S (S O)) (S O) +
  U_3_cayley (S (S O)) (S (S O)) * U_3_cayley (S (S O)) (S (S O)) == 1.
Proof. unfold U_3_cayley. ring. Qed.

(* Row orthogonality: row 0 dot row 1 = 0 *)
Lemma U_3_orth_01 :
  U_3_cayley O O * U_3_cayley (S O) O +
  U_3_cayley O (S O) * U_3_cayley (S O) (S O) +
  U_3_cayley O (S (S O)) * U_3_cayley (S O) (S (S O)) == 0.
Proof. unfold U_3_cayley. ring. Qed.

(* Gamma_3 row 0 sum = 1 (doubly stochastic) *)
Lemma Gamma_3_row0 :
  Gamma_3 O O + Gamma_3 O (S O) + Gamma_3 O (S (S O)) == 1.
Proof. unfold Gamma_3. ring. Qed.

(* Gamma_3 row 1 sum = 1 *)
Lemma Gamma_3_row1 :
  Gamma_3 (S O) O + Gamma_3 (S O) (S O) + Gamma_3 (S O) (S (S O)) == 1.
Proof. unfold Gamma_3. ring. Qed.

(* Gamma_3 col 0 sum = 1 *)
Lemma Gamma_3_col0 :
  Gamma_3 O O + Gamma_3 (S O) O + Gamma_3 (S (S O)) O == 1.
Proof. unfold Gamma_3. ring. Qed.

(* Gamma_3 col 1 sum = 1 *)
Lemma Gamma_3_col1 :
  Gamma_3 O (S O) + Gamma_3 (S O) (S O) + Gamma_3 (S (S O)) (S O) == 1.
Proof. unfold Gamma_3. ring. Qed.
