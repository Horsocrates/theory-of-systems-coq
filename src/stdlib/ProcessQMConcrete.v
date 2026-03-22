(* ProcessQMConcrete.v *)
(* Concrete QM Computations in Process Hilbert Space *)
(* E: Operator compositions, involutions, Hadamard squared *)
(* R: Structural role — verifiable quantum gate identities *)
(* R: sigma_x^2=I, H^2=2I, ZX vs XZ ordering matters *)

From Stdlib Require Import QArith Qabs List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import stdlib.ProcessHilbert.
From ToS Require Import stdlib.ProcessOperatorH.

(** ---- Hadamard squared = 2*Identity (unnormalized) ---- *)

Lemma hadamard_squared_ket0 :
  apply_op hadamard_op 2 (apply_op hadamard_op 2 ket_0) = [2; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_squared_ket1 :
  apply_op hadamard_op 2 (apply_op hadamard_op 2 ket_1) = [0; 2].
Proof. vm_compute. reflexivity. Qed.

(** H^2|0> has inner product 2 with |0> *)
Lemma hadamard_squared_inner :
  inner ket_0 (apply_op hadamard_op 2 (apply_op hadamard_op 2 ket_0)) == 2.
Proof. vm_compute. reflexivity. Qed.

(** ---- sigma_x is involutory ---- *)

Lemma sigma_x_involution_ket0 :
  apply_op sigma_x 2 (apply_op sigma_x 2 ket_0) = ket_0.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma_x_involution_ket1 :
  apply_op sigma_x 2 (apply_op sigma_x 2 ket_1) = ket_1.
Proof. vm_compute. reflexivity. Qed.

(** ---- sigma_z is involutory ---- *)

Lemma sigma_z_involution_ket0 :
  apply_op sigma_z 2 (apply_op sigma_z 2 ket_0) = ket_0.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma_z_involution_ket1 :
  apply_op sigma_z 2 (apply_op sigma_z 2 ket_1) = ket_1.
Proof. vm_compute. reflexivity. Qed.

(** ---- Operator ordering matters: ZX|0> != XZ|0> ---- *)

Lemma zx_ket0 : apply_op sigma_z 2 (apply_op sigma_x 2 ket_0) = [0; -(1)].
Proof. vm_compute. reflexivity. Qed.

Lemma xz_ket0 : apply_op sigma_x 2 (apply_op sigma_z 2 ket_0) = [0; 1].
Proof. vm_compute. reflexivity. Qed.

Lemma operator_order_matters :
  apply_op sigma_z 2 (apply_op sigma_x 2 ket_0) <>
  apply_op sigma_x 2 (apply_op sigma_z 2 ket_0).
Proof.
  vm_compute. intro H. discriminate.
Qed.

(** ---- Hadamard maps between X and Z eigenstates ---- *)

Lemma hadamard_plus_to_ket0 :
  inner ket_0 (apply_op hadamard_op 2 ket_plus) == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_minus_to_ket1 :
  inner ket_1 (apply_op hadamard_op 2 ket_minus) == 2.
Proof. vm_compute. reflexivity. Qed.

(** Synthesis *)
Theorem process_qm_concrete_synthesis :
  apply_op sigma_x 2 (apply_op sigma_x 2 ket_0) = ket_0 /\
  apply_op hadamard_op 2 (apply_op hadamard_op 2 ket_0) = [2; 0] /\
  apply_op sigma_z 2 (apply_op sigma_x 2 ket_0) <>
  apply_op sigma_x 2 (apply_op sigma_z 2 ket_0).
Proof.
  split. exact sigma_x_involution_ket0.
  split. exact hadamard_squared_ket0.
  exact operator_order_matters.
Qed.
