(** * ChapmanKolmogorov.v -- Chapman-Kolmogorov: G(K1+K2) = sum_m G(K1)*G(K2)
    Elements: ck_sum, chapman_kolmogorov concrete instances
    Roles:    M^{K1+K2} = M^{K1} * M^{K2} gives propagator composition
    Rules:    G_{ij}(K1+K2) = Σ_m G_{im}(K1) * G_{mj}(K2)
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  CHAPMAN-KOLMOGOROV SUM                                             *)
(* ================================================================== *)

(** CK sum: Σ_m G_{im}(K1) * G_{mj}(K2) for 2x2 *)
Definition ck_sum (M : Mat2) (i j K1 K2 : nat) : Q :=
  green M i 0%nat K1 * green M 0%nat j K2 +
  green M i 1%nat K1 * green M 1%nat j K2.

(* ================================================================== *)
(*  CONCRETE CHAPMAN-KOLMOGOROV FOR GOLDEN                             *)
(* ================================================================== *)

(** G(0,0,1+1) = G(0,0,1)*G(0,0,1) + G(0,1,1)*G(1,0,1) *)
Lemma ck_golden_00_1_1 :
  green golden 0%nat 0%nat 2 == ck_sum golden 0%nat 0%nat 1 1.
Proof. vm_compute. reflexivity. Qed.

(** G(0,0,1+2) = CK sum *)
Lemma ck_golden_00_1_2 :
  green golden 0%nat 0%nat 3 == ck_sum golden 0%nat 0%nat 1 2.
Proof. vm_compute. reflexivity. Qed.

(** G(0,0,2+2) = CK sum *)
Lemma ck_golden_00_2_2 :
  green golden 0%nat 0%nat 4 == ck_sum golden 0%nat 0%nat 2 2.
Proof. vm_compute. reflexivity. Qed.

(** G(0,0,2+3) = CK sum *)
Lemma ck_golden_00_2_3 :
  green golden 0%nat 0%nat 5 == ck_sum golden 0%nat 0%nat 2 3.
Proof. vm_compute. reflexivity. Qed.

(** G(0,0,3+3) = CK sum *)
Lemma ck_golden_00_3_3 :
  green golden 0%nat 0%nat 6 == ck_sum golden 0%nat 0%nat 3 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FIBONACCI ADDITION FORMULA VIA CK                                  *)
(*  F(m+n) = F(m)*F(n+1) + F(m-1)*F(n) where F = G_{00}              *)
(* ================================================================== *)

(** F(6) = F(3)*F(4) + F(2)*F(3) via CK with K1=3, K2=3 *)
Lemma fibonacci_addition_3_3 :
  green golden 0%nat 0%nat 6 ==
  green golden 0%nat 0%nat 3 * green golden 0%nat 0%nat 3 +
  green golden 0%nat 1%nat 3 * green golden 1%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

(** F(5) = F(2)*F(3) + F(1)*F(2) via CK with K1=2, K2=3 *)
Lemma fibonacci_addition_2_3 :
  green golden 0%nat 0%nat 5 ==
  green golden 0%nat 0%nat 2 * green golden 0%nat 0%nat 3 +
  green golden 0%nat 1%nat 2 * green golden 1%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  OFF-DIAGONAL CK                                                    *)
(* ================================================================== *)

Lemma ck_golden_01_2_2 :
  green golden 0%nat 1%nat 4 == ck_sum golden 0%nat 1%nat 2 2.
Proof. vm_compute. reflexivity. Qed.

Lemma ck_golden_10_1_2 :
  green golden 1%nat 0%nat 3 == ck_sum golden 1%nat 0%nat 1 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CK FOR FULL SHIFT                                                  *)
(* ================================================================== *)

Lemma ck_full_00_2_2 :
  green full_mat2 0%nat 0%nat 4 == ck_sum full_mat2 0%nat 0%nat 2 2.
Proof. vm_compute. reflexivity. Qed.

Lemma ck_full_00_1_3 :
  green full_mat2 0%nat 0%nat 4 == ck_sum full_mat2 0%nat 0%nat 1 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CK COMMUTATIVITY: ck_sum(K1,K2) = ck_sum(K2,K1) concretely        *)
(* ================================================================== *)

Lemma ck_commutative_golden_1_2 :
  ck_sum golden 0%nat 0%nat 1 2 == ck_sum golden 0%nat 0%nat 2 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ck_commutative_golden_2_3 :
  ck_sum golden 0%nat 0%nat 2 3 == ck_sum golden 0%nat 0%nat 3 2.
Proof. vm_compute. reflexivity. Qed.

(** CK for diagonal (1,1) entry *)
Lemma ck_golden_11_2_2 :
  green golden 1%nat 1%nat 4 == ck_sum golden 1%nat 1%nat 2 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem chapman_kolmogorov_synthesis :
  (* CK holds for golden at K1=2,K2=3 *)
  green golden 0%nat 0%nat 5 == ck_sum golden 0%nat 0%nat 2 3 /\
  (* CK holds for golden at K1=3,K2=3 *)
  green golden 0%nat 0%nat 6 == ck_sum golden 0%nat 0%nat 3 3 /\
  (* CK holds for full at K1=2,K2=2 *)
  green full_mat2 0%nat 0%nat 4 == ck_sum full_mat2 0%nat 0%nat 2 2 /\
  (* Fibonacci addition via CK *)
  green golden 0%nat 0%nat 6 ==
    green golden 0%nat 0%nat 3 * green golden 0%nat 0%nat 3 +
    green golden 0%nat 1%nat 3 * green golden 1%nat 0%nat 3.
Proof.
  split; [exact ck_golden_00_2_3|].
  split; [exact ck_golden_00_3_3|].
  split; [exact ck_full_00_2_2|exact fibonacci_addition_3_3].
Qed.
