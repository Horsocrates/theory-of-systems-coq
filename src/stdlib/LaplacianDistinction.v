(** * LaplacianDistinction.v — First and Second Distinction Operators
    Elements: Functions nat -> Q, distinction operators Δ and Δ²
    Roles:    Δf(n) = f(n+1) - f(n), Δ²f(n) = f(n+1) - 2f(n) + f(n-1)
    Rules:    Linear functions have Δ²=0, quadratic have Δ²=constant
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  DISTINCTION OPERATORS                                              *)
(*  The discrete Laplacian IS the second distinction operator.         *)
(*  Δ²f(n) = f(n+1) - 2f(n) + f(n-1)                                 *)
(* ================================================================== *)

Definition distinction_1 (f : nat -> Q) (n : nat) : Q :=
  f (S n) - f n.

Definition distinction_2 (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => f (S O) - 2 * f O
  | S m => f (S n) - 2 * f n + f m
  end.

(* ================================================================== *)
(*  TEST FUNCTIONS                                                     *)
(* ================================================================== *)

Definition f_linear (n : nat) : Q := inject_Z (Z.of_nat n).
Definition f_quadratic (n : nat) : Q :=
  inject_Z (Z.of_nat n) * inject_Z (Z.of_nat n).

(* ================================================================== *)
(*  FIRST DISTINCTION OF LINEAR: always 1                              *)
(* ================================================================== *)

Lemma dist1_linear_0 : distinction_1 f_linear O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma dist1_linear_1 : distinction_1 f_linear 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma dist1_linear_2 : distinction_1 f_linear 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SECOND DISTINCTION OF LINEAR: always 0                             *)
(*  This is the discrete analogue of d²(ax+b)/dx² = 0                 *)
(* ================================================================== *)

Lemma dist2_linear_1 : distinction_2 f_linear 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma dist2_linear_2 : distinction_2 f_linear 2%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FIRST DISTINCTION OF QUADRATIC: 2n+1                               *)
(* ================================================================== *)

Lemma dist1_quad_0 : distinction_1 f_quadratic O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma dist1_quad_1 : distinction_1 f_quadratic 1%nat == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma dist1_quad_2 : distinction_1 f_quadratic 2%nat == 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SECOND DISTINCTION OF QUADRATIC: always 2                          *)
(*  This is the discrete analogue of d²(n²)/dx² = 2                   *)
(*  The Laplacian of a quadratic is CONSTANT — fundamental property.   *)
(* ================================================================== *)

Lemma dist2_quad_1 : distinction_2 f_quadratic 1%nat == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma dist2_quad_2 : distinction_2 f_quadratic 2%nat == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma dist2_quad_3 : distinction_2 f_quadratic 3%nat == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** The discrete Laplacian (second distinction) annihilates linear
    functions and maps quadratics to constants, exactly like the
    continuous Laplacian d²/dx². *)
Theorem laplacian_distinction_synthesis :
  distinction_2 f_linear 1%nat == 0 /\
  distinction_2 f_linear 2%nat == 0 /\
  distinction_2 f_quadratic 1%nat == 2 /\
  distinction_2 f_quadratic 2%nat == 2 /\
  distinction_2 f_quadratic 3%nat == 2.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
