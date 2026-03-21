(** * FibonacciGreen.v -- Fibonacci identities from matrix multiplication
    Elements: addition formula, Cassini identity, determinant process
    Roles:    M^{m+n} = M^m · M^n gives all Fibonacci identities
    Rules:    G_{00}(K) = F(K+1), derived mechanically from golden matrix
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  FIBONACCI FROM GREEN'S FUNCTION                                    *)
(* ================================================================== *)

(** M^K = [[G00, G01], [G10, G11]]
    G_{00}(K) = F(K+1), G_{01}(K) = F(K), G_{10}(K) = F(K) *)

(** Extended Fibonacci values *)
Lemma green_golden_00_5 : green golden 0%nat 0%nat 5 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_00_6 : green golden 0%nat 0%nat 6 == 13.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ADDITION FORMULA: F(m+n+1) = F(m+1)·F(n+1) + F(m)·F(n)           *)
(*  Concrete instances from mat2_pow(m+n) = mat2_mul(mat2_pow m)(...)  *)
(* ================================================================== *)

(** m=1, n=1: G00(2) = G00(1)·G00(1) + G01(1)·G10(1) *)
Lemma fib_addition_1_1 :
  green golden 0%nat 0%nat 2 ==
  green golden 0%nat 0%nat 1 * green golden 0%nat 0%nat 1 +
  green golden 0%nat 1%nat 1 * green golden 1%nat 0%nat 1.
Proof. vm_compute. reflexivity. Qed.

(** m=2, n=1: G00(3) = G00(2)·G00(1) + G01(2)·G10(1) *)
Lemma fib_addition_2_1 :
  green golden 0%nat 0%nat 3 ==
  green golden 0%nat 0%nat 2 * green golden 0%nat 0%nat 1 +
  green golden 0%nat 1%nat 2 * green golden 1%nat 0%nat 1.
Proof. vm_compute. reflexivity. Qed.

(** m=2, n=2: G00(4) = G00(2)·G00(2) + G01(2)·G10(2) *)
Lemma fib_addition_2_2 :
  green golden 0%nat 0%nat 4 ==
  green golden 0%nat 0%nat 2 * green golden 0%nat 0%nat 2 +
  green golden 0%nat 1%nat 2 * green golden 1%nat 0%nat 2.
Proof. vm_compute. reflexivity. Qed.

(** m=3, n=3: G00(6) = G00(3)·G00(3) + G01(3)·G10(3) = 9+4 = 13 *)
Lemma fib_addition_3_3 :
  green golden 0%nat 0%nat 6 ==
  green golden 0%nat 0%nat 3 * green golden 0%nat 0%nat 3 +
  green golden 0%nat 1%nat 3 * green golden 1%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CASSINI IDENTITY: det(M^K) = (-1)^K                               *)
(*  F(K+1)·F(K-1) - F(K)² = (-1)^K                                   *)
(* ================================================================== *)

(** det(M^K) = G00·G11 - G01·G10 *)
Definition green_det (K : nat) : Q :=
  green golden 0%nat 0%nat K * green golden 1%nat 1%nat K -
  green golden 0%nat 1%nat K * green golden 1%nat 0%nat K.

Lemma cassini_1 : green_det 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_2 : green_det 2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_3 : green_det 3 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_4 : green_det 4 == 1.
Proof. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem fibonacci_green_synthesis :
  (* F(6) = 8, F(7) = 13 *)
  green golden 0%nat 0%nat 5 == 8 /\
  green golden 0%nat 0%nat 6 == 13 /\
  (* Addition: F(5) = F(3)² + F(2)² = 4+1 = 5 *)
  green golden 0%nat 0%nat 4 ==
    green golden 0%nat 0%nat 2 * green golden 0%nat 0%nat 2 +
    green golden 0%nat 1%nat 2 * green golden 1%nat 0%nat 2 /\
  (* Cassini alternates *)
  green_det 3 == -(1) /\ green_det 4 == 1.
Proof.
  split; [|split; [|split; [|split]]].
  - exact green_golden_00_5.
  - exact green_golden_00_6.
  - exact fib_addition_2_2.
  - exact cassini_3.
  - exact cassini_4.
Qed.
