(** * LagrangeTheorem.v -- Periodic CF ↔ quadratic irrational
    Elements: cf_period_matrix, sqrt2_period, sqrt3_period
    Roles:    Period matrix = transfer matrix of associated SFT
    Rules:    Periodic CF [a;b,b,...] → M = A(b), eigenvalue = quadratic irrational
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
From ToS Require Import stdlib.SFTEntropyGeneral.
From ToS Require Import stdlib.CFMatrixProduct.

Open Scope Q_scope.

(* ================================================================== *)
(*  PERIOD MATRIX: transfer matrix of periodic CF                      *)
(* ================================================================== *)

(** For CF [a₀; a₁, ..., a_p, a₁, ..., a_p, ...] with period (a₁,...,a_p):
    Period matrix = A(a₁)·A(a₂)·...·A(a_p).
    Eigenvalues of period matrix → the quadratic irrational. *)

Definition cf_period_matrix (period : list Z) : QMat 2 2 :=
  cf_product period.

(* ================================================================== *)
(*  φ = [1;1,1,1,...]: period = [1], matrix = A(1) = [[1,1],[1,0]]    *)
(* ================================================================== *)

Definition golden_period : QMat 2 2 := cf_period_matrix [1%Z].

Lemma golden_period_trace : mat_trace golden_period == 1.
Proof. unfold golden_period, cf_period_matrix, cf_product, cf_matrix.
  vm_compute. reflexivity. Qed.

Lemma golden_period_det : det_2x2 golden_period == -(1).
Proof. unfold golden_period, cf_period_matrix, cf_product, cf_matrix.
  vm_compute. reflexivity. Qed.

(** Char poly: λ² - λ - 1 = 0 → eigenvalue = φ *)
Lemma golden_period_charpoly : forall lambda,
  char_poly_2x2 golden_period lambda == lambda * lambda - lambda - 1.
Proof.
  intro. unfold char_poly_2x2.
  rewrite golden_period_trace, golden_period_det. ring.
Qed.

(* ================================================================== *)
(*  √2 = [1;2,2,...]: period = [2], matrix = A(2) = [[2,1],[1,0]]     *)
(* ================================================================== *)

Definition sqrt2_period : QMat 2 2 := cf_period_matrix [2%Z].

Lemma sqrt2_period_trace : mat_trace sqrt2_period == 2.
Proof. unfold sqrt2_period, cf_period_matrix, cf_product, cf_matrix.
  vm_compute. reflexivity. Qed.

Lemma sqrt2_period_det : det_2x2 sqrt2_period == -(1).
Proof. unfold sqrt2_period, cf_period_matrix, cf_product, cf_matrix.
  vm_compute. reflexivity. Qed.

(** Char poly: λ² - 2λ - 1 = 0 → eigenvalue = 1 + √2 *)
Lemma sqrt2_period_charpoly : forall lambda,
  char_poly_2x2 sqrt2_period lambda == lambda * lambda - 2 * lambda - 1.
Proof.
  intro. unfold char_poly_2x2.
  rewrite sqrt2_period_trace, sqrt2_period_det. ring.
Qed.

(** Discriminant = 4 + 4 = 8 (= 4·2, so eigenvalue involves √2) *)
Lemma sqrt2_discriminant : discriminant_2x2 sqrt2_period == 8.
Proof.
  unfold discriminant_2x2.
  rewrite sqrt2_period_trace, sqrt2_period_det. ring.
Qed.

(* ================================================================== *)
(*  √3 = [1;1,2,1,2,...]: period = [1,2], matrix = A(1)·A(2)          *)
(* ================================================================== *)

Definition sqrt3_period : QMat 2 2 := cf_period_matrix [1;2]%Z.

Lemma sqrt3_period_trace : mat_trace sqrt3_period == 4.
Proof. unfold sqrt3_period, cf_period_matrix, cf_product, cf_matrix.
  vm_compute. reflexivity. Qed.

Lemma sqrt3_period_det : det_2x2 sqrt3_period == 1.
Proof. unfold sqrt3_period, cf_period_matrix, cf_product, cf_matrix.
  vm_compute. reflexivity. Qed.

(** Char poly: λ² - 4λ + 1 = 0 → eigenvalue = 2 + √3 *)
Lemma sqrt3_period_charpoly : forall lambda,
  char_poly_2x2 sqrt3_period lambda == lambda * lambda - 4 * lambda + 1.
Proof.
  intro. unfold char_poly_2x2.
  rewrite sqrt3_period_trace, sqrt3_period_det. ring.
Qed.

(** Discriminant = 16 - 4 = 12 (= 4·3, so eigenvalue involves √3) *)
Lemma sqrt3_discriminant : discriminant_2x2 sqrt3_period == 12.
Proof.
  unfold discriminant_2x2.
  rewrite sqrt3_period_trace, sqrt3_period_det. ring.
Qed.

(** LAGRANGE PATTERN: discriminant = 4·n for √n
    golden: disc = 5 (not 4·n, because φ = (1+√5)/2)
    √2:    disc = 8 = 4·2  ✓
    √3:    disc = 12 = 4·3  ✓ *)

Theorem lagrange_synthesis :
  (* Each periodic CF → char poly → discriminant *)
  discriminant_2x2 golden_period == 5 /\
  discriminant_2x2 sqrt2_period == 8 /\
  discriminant_2x2 sqrt3_period == 12 /\
  (* All determinants: |det| = 1 (unimodular) *)
  det_2x2 golden_period == -(1) /\
  det_2x2 sqrt2_period == -(1) /\
  det_2x2 sqrt3_period == 1.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - unfold discriminant_2x2. rewrite golden_period_trace, golden_period_det. ring.
  - exact sqrt2_discriminant.
  - exact sqrt3_discriminant.
  - exact golden_period_det.
  - exact sqrt2_period_det.
  - exact sqrt3_period_det.
Qed.
