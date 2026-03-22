(* ProcessOperatorH.v *)
(* Process Operators on Hilbert Space *)
(* E: Matrix operators as (nat -> nat -> Q), apply_op *)
(* R: Pauli matrices, Hadamard, operator application *)
(* R: Concrete action on basis states, commutator nonzero *)

From Stdlib Require Import QArith Qabs List Lia.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import stdlib.ProcessHilbert.

(** Operator = matrix as function nat -> nat -> Q *)
Definition Operator := nat -> nat -> Q.

(** Apply operator M of dimension K to state psi *)
Definition apply_op (M : Operator) (K : nat) (psi : PState) : PState :=
  map (fun i => fold_left (fun acc j => acc + M i j * nth j psi 0) (seq 0 K) 0)
      (seq 0 K).

(** Pauli sigma_x: |0> <-> |1> *)
Definition sigma_x : Operator := fun i j =>
  match i, j with
  | O, S O => 1
  | S O, O => 1
  | _, _ => 0
  end.

(** Pauli sigma_z: |0> -> |0>, |1> -> -|1> *)
Definition sigma_z : Operator := fun i j =>
  match i, j with
  | O, O => 1
  | S O, S O => -(1)
  | _, _ => 0
  end.

(** Hadamard (unnormalized by sqrt(2)): H = [[1,1],[1,-1]] *)
Definition hadamard_op : Operator := fun i j =>
  match i, j with
  | O, O => 1
  | O, S O => 1
  | S O, O => 1
  | S O, S O => -(1)
  | _, _ => 0
  end.

Definition ket_minus : PState := [1; -(1)].

(** ---- Pauli X action ---- *)

Lemma sigma_x_ket0 : apply_op sigma_x 2 ket_0 = ket_1.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma_x_ket1 : apply_op sigma_x 2 ket_1 = ket_0.
Proof. vm_compute. reflexivity. Qed.

(** ---- Pauli Z action ---- *)

Lemma sigma_z_ket0 : apply_op sigma_z 2 ket_0 = ket_0.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma_z_ket1 : apply_op sigma_z 2 ket_1 = [0; -(1)].
Proof. vm_compute. reflexivity. Qed.

(** ---- Hadamard action ---- *)

Lemma hadamard_ket0 : apply_op hadamard_op 2 ket_0 = ket_plus.
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_ket1 : apply_op hadamard_op 2 ket_1 = ket_minus.
Proof. vm_compute. reflexivity. Qed.

(** ---- Commutator ---- *)

Definition commutator (A B : Operator) (K : nat) (i j : nat) : Q :=
  fold_left (fun acc m => acc + A i m * B m j - B i m * A m j) (seq 0 K) 0.

Lemma sigma_xz_comm_01 : commutator sigma_x sigma_z 2 O (S O) == -(2).
Proof. vm_compute. reflexivity. Qed.

Lemma sigma_xz_noncommute : commutator sigma_x sigma_z 2 O (S O) <> 0.
Proof.
  intro H. vm_compute in H. discriminate.
Qed.

(** ---- Identity operator ---- *)

Definition identity_op : Operator := fun i j =>
  match i, j with
  | O, O => 1
  | S O, S O => 1
  | _, _ => 0
  end.

Lemma identity_ket0 : apply_op identity_op 2 ket_0 = ket_0.
Proof. vm_compute. reflexivity. Qed.

Lemma identity_ket1 : apply_op identity_op 2 ket_1 = ket_1.
Proof. vm_compute. reflexivity. Qed.

(** ---- Sigma_x is its own inverse ---- *)

Lemma sigma_x_squared : apply_op sigma_x 2 (apply_op sigma_x 2 ket_0) = ket_0.
Proof. vm_compute. reflexivity. Qed.

(** Synthesis *)
Theorem process_operator_synthesis :
  apply_op sigma_x 2 ket_0 = ket_1 /\
  apply_op hadamard_op 2 ket_0 = ket_plus /\
  commutator sigma_x sigma_z 2 O (S O) <> 0.
Proof.
  split. exact sigma_x_ket0.
  split. exact hadamard_ket0.
  exact sigma_xz_noncommute.
Qed.
