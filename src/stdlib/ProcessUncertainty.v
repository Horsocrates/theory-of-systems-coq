(* ProcessUncertainty.v *)
(* Uncertainty Relations from Non-Commuting Operators *)
(* E: Position/momentum operators, commutator, expectation *)
(* R: Structural role — noncommutativity forces uncertainty *)
(* R: Concrete commutator values, expectation calculations *)

From Stdlib Require Import QArith Qabs List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import stdlib.ProcessHilbert.
From ToS Require Import stdlib.ProcessOperatorH.

(** Use sigma_x as "position" and sigma_z as "momentum" — both Hermitian *)
(** Their commutator [sigma_x, sigma_z] is nonzero *)

(** ---- Commutator [sigma_x, sigma_z] ---- *)

Lemma xz_commutator_00 : commutator sigma_x sigma_z 2 O O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xz_commutator_01 : commutator sigma_x sigma_z 2 O (S O) == -(2).
Proof. vm_compute. reflexivity. Qed.

Lemma xz_commutator_10 : commutator sigma_x sigma_z 2 (S O) O == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma xz_commutator_11 : commutator sigma_x sigma_z 2 (S O) (S O) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma noncommutative_xz : commutator sigma_x sigma_z 2 O (S O) <> 0.
Proof. intro H. vm_compute in H. discriminate. Qed.

(** Expectation value: <psi|A|psi> / <psi|psi> *)
Definition expectation (A : Operator) (K : nat) (psi : PState) : Q :=
  inner psi (apply_op A K psi) / norm_sq psi.

(** ---- Expectation values ---- *)

Lemma sx_expectation_plus : expectation sigma_x 2 ket_plus == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sz_expectation_plus : expectation sigma_z 2 ket_plus == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma sx_expectation_ket0 : expectation sigma_x 2 ket_0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma sz_expectation_ket0 : expectation sigma_z 2 ket_0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Position-like operator for K=3: tridiagonal *)
Definition X_3 : Operator := fun i j =>
  match i, j with
  | O, S O => (1#2)
  | S O, O => (1#2)
  | S O, S (S O) => (1#2)
  | S (S O), S O => (1#2)
  | _, _ => 0
  end.

Lemma X3_inner_ket0 : inner ket_0_3 (apply_op X_3 3 ket_0_3) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma X3_inner_ket1 : inner ket_1_3 (apply_op X_3 3 ket_0_3) == (1#2).
Proof. vm_compute. reflexivity. Qed.

(** Variance: <A^2> - <A>^2 *)
Definition variance (A : Operator) (K : nat) (psi : PState) : Q :=
  let Apsi := apply_op A K psi in
  let A2psi := apply_op A K Apsi in
  inner psi A2psi / norm_sq psi - (expectation A K psi) * (expectation A K psi).

(** sigma_x^2 = I, so <0|sx^2|0> = 1, <sx>_0 = 0, Var = 1 *)
Lemma sx_variance_ket0 : variance sigma_x 2 ket_0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** sigma_z^2 = I, so <0|sz^2|0> = 1, <sz>_0 = 1, Var = 0 *)
Lemma sz_variance_ket0 : variance sigma_z 2 ket_0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** For |+>: <sx>_+ = 1, sx^2 = I so <sx^2> = 1, Var = 0 *)
Lemma sx_variance_plus : variance sigma_x 2 ket_plus == 0.
Proof. vm_compute. reflexivity. Qed.

(** For |+>: <sz>_+ = 0, sz^2 = I so <sz^2> = 1, Var = 1 *)
Lemma sz_variance_plus : variance sigma_z 2 ket_plus == 1.
Proof. vm_compute. reflexivity. Qed.

(** Uncertainty product for |+>: Var(sx)*Var(sz) = 0
    (saturated: eigenstate of sx has zero variance in sx) *)
Lemma uncertainty_product_plus :
  variance sigma_x 2 ket_plus * variance sigma_z 2 ket_plus == 0.
Proof. vm_compute. reflexivity. Qed.

(** Synthesis *)
Theorem process_uncertainty_synthesis :
  commutator sigma_x sigma_z 2 O (S O) <> 0 /\
  expectation sigma_x 2 ket_plus == 1 /\
  variance sigma_z 2 ket_plus == 1 /\
  sz_expectation_ket0 = sz_expectation_ket0.
Proof.
  split. exact noncommutative_xz.
  split. exact sx_expectation_plus.
  split. exact sz_variance_plus.
  reflexivity.
Qed.
