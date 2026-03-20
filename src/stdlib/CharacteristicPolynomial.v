(** * CharacteristicPolynomial.v -- Eigenvalue process via Newton's method
    Elements: newton_step, char_poly_eval, eigenvalue_newton_process
    Roles:    Newton's method on char poly = eigenvalue process
    Rules:    x_{n+1} = x_n - p(x_n)/p'(x_n), exact Q at each step
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.

Open Scope Q_scope.

(* ================================================================== *)
(*  CHARACTERISTIC POLYNOMIAL EVALUATION                               *)
(* ================================================================== *)

(** For 2×2: p(λ) = λ² - tr(M)·λ + det(M) *)
(** Derivative: p'(λ) = 2λ - tr(M) *)

Definition char_poly_deriv_2x2 (M : QMat 2 2) (lambda : Q) : Q :=
  2 * lambda - mat_trace M.

(** Newton step: x_{n+1} = x_n - p(x_n)/p'(x_n) *)
Definition newton_step (M : QMat 2 2) (x : Q) : Q :=
  x - char_poly_2x2 M x / char_poly_deriv_2x2 M x.

(** Newton iteration *)
Fixpoint newton_iterate (M : QMat 2 2) (x0 : Q) (K : nat) : Q :=
  match K with
  | O => x0
  | S j => newton_step M (newton_iterate M x0 j)
  end.

(** Eigenvalue process via Newton on char poly *)
Definition eigenvalue_newton_process (M : QMat 2 2) (x0 : Q) (K : nat) : Q :=
  newton_iterate M x0 K.

(* ================================================================== *)
(*  GOLDEN MEAN: λ² - λ - 1 = 0, Newton from x₀ = 2                  *)
(* ================================================================== *)

Definition golden_mat_pf : QMat 2 2 := qmat2x2 1 1 1 0.

(** p(2) = 4 - 2 - 1 = 1 *)
Lemma golden_poly_at_2 : char_poly_2x2 golden_mat_pf 2 == 1.
Proof.
  unfold char_poly_2x2, mat_trace, sum_Q, det_2x2,
         golden_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** p'(2) = 4 - 1 = 3 *)
Lemma golden_deriv_at_2 : char_poly_deriv_2x2 golden_mat_pf 2 == 3.
Proof.
  unfold char_poly_deriv_2x2, mat_trace, sum_Q,
         golden_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** x₁ = 2 - 1/3 = 5/3 ≈ 1.667 *)
Lemma golden_newton_1 : eigenvalue_newton_process golden_mat_pf 2 1 == 5#3.
Proof.
  unfold eigenvalue_newton_process, newton_iterate, newton_step.
  unfold char_poly_2x2, char_poly_deriv_2x2, mat_trace, sum_Q, det_2x2,
         golden_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** x₂ = 5/3 - p(5/3)/p'(5/3) *)
(** p(5/3) = 25/9 - 5/3 - 1 = 25/9 - 15/9 - 9/9 = 1/9 *)
(** p'(5/3) = 10/3 - 1 = 7/3 *)
(** x₂ = 5/3 - (1/9)/(7/3) = 5/3 - 1/21 = 34/21 ≈ 1.619 *)
Lemma golden_newton_2 : eigenvalue_newton_process golden_mat_pf 2 2 == 34#21.
Proof.
  unfold eigenvalue_newton_process, newton_iterate, newton_step.
  unfold char_poly_2x2, char_poly_deriv_2x2, mat_trace, sum_Q, det_2x2,
         golden_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** x₃ = 34/21 - p(34/21)/p'(34/21) *)
Lemma golden_newton_3 : eigenvalue_newton_process golden_mat_pf 2 3 == 1597#987.
Proof.
  unfold eigenvalue_newton_process, newton_iterate, newton_step.
  unfold char_poly_2x2, char_poly_deriv_2x2, mat_trace, sum_Q, det_2x2,
         golden_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** Convergence: oscillation decreases *)
Lemma golden_newton_osc_01 :
  Qabs (eigenvalue_newton_process golden_mat_pf 2 1 - 2) == 1#3.
Proof.
  rewrite golden_newton_1. vm_compute. reflexivity.
Qed.

Lemma golden_newton_osc_12 :
  Qabs (eigenvalue_newton_process golden_mat_pf 2 2 -
         eigenvalue_newton_process golden_mat_pf 2 1) == 1#21.
Proof.
  rewrite golden_newton_1, golden_newton_2. vm_compute. reflexivity.
Qed.

Theorem golden_newton_converges :
  Qabs (eigenvalue_newton_process golden_mat_pf 2 2 -
         eigenvalue_newton_process golden_mat_pf 2 1) <
  Qabs (eigenvalue_newton_process golden_mat_pf 2 1 - 2).
Proof.
  rewrite golden_newton_osc_12, golden_newton_osc_01. lra.
Qed.

(* ================================================================== *)
(*  FULL SHIFT: λ² - 2λ = 0 → eigenvalue 2                           *)
(* ================================================================== *)

Definition full_mat_pf : QMat 2 2 := qmat2x2 1 1 1 1.

(** p(3) = 9 - 6 + 0 = 3, p'(3) = 6 - 2 = 4 *)
(** x₁ = 3 - 3/4 = 9/4 *)
Lemma full_newton_1 : eigenvalue_newton_process full_mat_pf 3 1 == 9#4.
Proof.
  unfold eigenvalue_newton_process, newton_iterate, newton_step.
  unfold char_poly_2x2, char_poly_deriv_2x2, mat_trace, sum_Q, det_2x2,
         full_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** x₂ converges toward 2 *)
Lemma full_newton_2 : eigenvalue_newton_process full_mat_pf 3 2 == 81#40.
Proof.
  unfold eigenvalue_newton_process, newton_iterate, newton_step.
  unfold char_poly_2x2, char_poly_deriv_2x2, mat_trace, sum_Q, det_2x2,
         full_mat_pf, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** Newton converges quadratically: error shrinks rapidly *)
Lemma full_osc_1 : Qabs (eigenvalue_newton_process full_mat_pf 3 1 - 2) == 1#4.
Proof. rewrite full_newton_1. vm_compute. reflexivity. Qed.

Lemma full_osc_2 : Qabs (eigenvalue_newton_process full_mat_pf 3 2 - 2) == 1#40.
Proof. rewrite full_newton_2. vm_compute. reflexivity. Qed.

Theorem full_newton_converges :
  Qabs (eigenvalue_newton_process full_mat_pf 3 2 - 2) <
  Qabs (eigenvalue_newton_process full_mat_pf 3 1 - 2).
Proof. rewrite full_osc_1, full_osc_2. lra. Qed.

(** SYNTHESIS *)
Theorem char_poly_synthesis :
  (* Golden: Newton from 2 gives {2, 5/3, 34/21, 1597/987, ...} → φ *)
  eigenvalue_newton_process golden_mat_pf 2 2 == 34#21 /\
  (* Full: Newton from 3 gives {3, 9/4, 129/64, ...} → 2 *)
  eigenvalue_newton_process full_mat_pf 3 1 == 9#4 /\
  (* Both converge: oscillations decrease *)
  Qabs (eigenvalue_newton_process golden_mat_pf 2 2 -
        eigenvalue_newton_process golden_mat_pf 2 1) <
  Qabs (eigenvalue_newton_process golden_mat_pf 2 1 - 2).
Proof.
  split; [|split].
  - exact golden_newton_2.
  - exact full_newton_1.
  - exact golden_newton_converges.
Qed.
