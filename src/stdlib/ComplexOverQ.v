(** * ComplexOverQ.v -- Complex Numbers as 2x2 Matrices over Q as ToS System
    Elements: complex_mat, C_one, C_i, C_zero, complex_mod_sq, complex_conj
    Roles:    i^2 = -I verified component-wise; (a+bi)(c+di) = (ac-bd)+(ad+bc)i
    Rules:    Matrix representation makes complex arithmetic decidable over Q
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  COMPLEX NUMBERS AS 2x2 REAL MATRICES                               *)
(*  a + bi  <-->  [ a  -b ]                                             *)
(*                [ b   a ]                                             *)
(* ================================================================== *)

Definition complex_mat (a b : Q) : Mat2 := fun i j =>
  match (i, j) with
  | (O, O) => a
  | (O, S O) => -b
  | (S O, O) => b
  | (S O, S O) => a
  | _ => 0
  end.

Definition C_one : Mat2 := complex_mat 1 0.
Definition C_i : Mat2 := complex_mat 0 1.
Definition C_zero : Mat2 := complex_mat 0 0.

(* ================================================================== *)
(*  i^2 = -I  (component-wise verification)                            *)
(* ================================================================== *)

Lemma i_sq_00 : mat2_mul C_i C_i 0%nat 0%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma i_sq_01 : mat2_mul C_i C_i 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma i_sq_10 : mat2_mul C_i C_i 1%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma i_sq_11 : mat2_mul C_i C_i 1%nat 1%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COMPLEX MULTIPLICATION: (2+3i)(4+5i) = -7 + 22i                   *)
(* ================================================================== *)

Lemma complex_mul_real :
  mat2_mul (complex_mat 2 3) (complex_mat 4 5) 0%nat 0%nat == -(7).
Proof. vm_compute. reflexivity. Qed.

Lemma complex_mul_imag :
  mat2_mul (complex_mat 2 3) (complex_mat 4 5) 1%nat 0%nat == 22.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MODULUS SQUARED: |a+bi|^2 = a^2 + b^2                             *)
(* ================================================================== *)

Definition complex_mod_sq (a b : Q) : Q := a * a + b * b.

Lemma mod_sq_example : complex_mod_sq 3 4 == 25.
Proof. unfold complex_mod_sq. vm_compute. reflexivity. Qed.

Lemma mod_sq_unit_i : complex_mod_sq 0 1 == 1.
Proof. unfold complex_mod_sq. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COMPLEX CONJUGATE: conj(a+bi) = a - bi                            *)
(* ================================================================== *)

Definition complex_conj (a b : Q) : Mat2 := complex_mat a (-b).

Lemma conj_real_part : complex_conj 3 4 0%nat 0%nat == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma conj_imag_part : complex_conj 3 4 1%nat 0%nat == -(4).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  IDENTITY PROPERTIES                                                 *)
(* ================================================================== *)

Lemma one_mul_00 :
  forall a b : Q,
  mat2_mul C_one (complex_mat a b) 0%nat 0%nat == a.
Proof.
  intros a b. unfold mat2_mul, C_one, complex_mat. ring.
Qed.

Lemma one_mul_10 :
  forall a b : Q,
  mat2_mul C_one (complex_mat a b) 1%nat 0%nat == b.
Proof.
  intros a b. unfold mat2_mul, C_one, complex_mat. ring.
Qed.

(* ================================================================== *)
(*  ZERO AND ADDITION                                                   *)
(* ================================================================== *)

Lemma zero_mul_00 :
  forall a b : Q,
  mat2_mul C_zero (complex_mat a b) 0%nat 0%nat == 0.
Proof.
  intros a b. unfold mat2_mul, C_zero, complex_mat. ring.
Qed.

Lemma mod_sq_zero : complex_mod_sq 0 0 == 0.
Proof. unfold complex_mod_sq. vm_compute. reflexivity. Qed.

Lemma mod_sq_real : complex_mod_sq 5 0 == 25.
Proof. unfold complex_mod_sq. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONJUGATE * ORIGINAL = |z|^2 * I (real part)                       *)
(* ================================================================== *)

Lemma conj_mul_real :
  mat2_mul (complex_conj 3 4) (complex_mat 3 4) 0%nat 0%nat == 25.
Proof. vm_compute. reflexivity. Qed.

Lemma conj_mul_imag :
  mat2_mul (complex_conj 3 4) (complex_mat 3 4) 1%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem complex_over_Q_synthesis :
  mat2_mul C_i C_i 0%nat 0%nat == -(1) /\
  mat2_mul C_i C_i 1%nat 1%nat == -(1) /\
  mat2_mul (complex_mat 2 3) (complex_mat 4 5) 0%nat 0%nat == -(7) /\
  complex_mod_sq 3 4 == 25.
Proof.
  split; [exact i_sq_00 |].
  split; [exact i_sq_11 |].
  split; [exact complex_mul_real |].
  exact mod_sq_example.
Qed.
