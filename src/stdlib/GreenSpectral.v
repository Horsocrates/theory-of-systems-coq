(** * GreenSpectral.v -- Spectral decomposition of Green's functions
    Elements: char_p, char_q, golden_char, mode_ratio
    Roles:    Characteristic polynomial encodes eigenvalues; recurrence from trace/det
    Rules:    G(K+2) = trace*G(K+1) - det*G(K) is Cayley-Hamilton for 2x2
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  CHARACTERISTIC POLYNOMIAL COEFFICIENTS                             *)
(* ================================================================== *)

(** char_p = trace of M, char_q = determinant of M *)
Definition char_p (M : Mat2) : Q := M 0%nat 0%nat + M 1%nat 1%nat.
Definition char_q (M : Mat2) : Q := M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 1%nat 0%nat.

(** Golden: trace = 1, det = -1 *)
Lemma golden_char_p : char_p golden == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_char_q : char_q golden == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma golden_char : char_p golden == 1 /\ char_q golden == -(1).
Proof. split; [exact golden_char_p | exact golden_char_q]. Qed.

(* ================================================================== *)
(*  CONCRETE GREEN VALUES FOR GOLDEN (Fibonacci)                       *)
(* ================================================================== *)

Lemma green_golden_00_5 : green golden 0%nat 0%nat 5 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_00_6 : green golden 0%nat 0%nat 6 == 13.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GOLDEN RECURRENCE: CONCRETE INSTANCES                              *)
(*  G(K+2) = G(K+1) + G(K) since trace=1, det=-1                     *)
(* ================================================================== *)

Lemma golden_recurrence_0 :
  green golden 0%nat 0%nat 2 == green golden 0%nat 0%nat 1 + green golden 0%nat 0%nat 0.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_recurrence_1 :
  green golden 0%nat 0%nat 3 == green golden 0%nat 0%nat 2 + green golden 0%nat 0%nat 1.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_recurrence_2 :
  green golden 0%nat 0%nat 4 == green golden 0%nat 0%nat 3 + green golden 0%nat 0%nat 2.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_recurrence_3 :
  green golden 0%nat 0%nat 5 == green golden 0%nat 0%nat 4 + green golden 0%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CAYLEY-HAMILTON CONCRETE INSTANCES FOR GOLDEN                      *)
(*  G(K+2) = char_p * G(K+1) - char_q * G(K)                         *)
(*  For golden: G(K+2) = 1*G(K+1) - (-1)*G(K) = G(K+1) + G(K)        *)
(* ================================================================== *)

Lemma cayley_hamilton_golden_0 :
  green golden 0%nat 0%nat 2 ==
  char_p golden * green golden 0%nat 0%nat 1 - char_q golden * green golden 0%nat 0%nat 0.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_hamilton_golden_1 :
  green golden 0%nat 0%nat 3 ==
  char_p golden * green golden 0%nat 0%nat 2 - char_q golden * green golden 0%nat 0%nat 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cayley_hamilton_golden_2 :
  green golden 0%nat 0%nat 4 ==
  char_p golden * green golden 0%nat 0%nat 3 - char_q golden * green golden 0%nat 0%nat 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FULL SHIFT: trace=2, det=0 → G(K+2) = 2*G(K+1)                    *)
(* ================================================================== *)

Lemma full_char_p : char_p full_mat2 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma full_char_q : char_q full_mat2 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma full_recurrence_0 :
  green full_mat2 0%nat 0%nat 3 ==
  2 * green full_mat2 0%nat 0%nat 2.
Proof. vm_compute. reflexivity. Qed.

Lemma full_recurrence_1 :
  green full_mat2 0%nat 0%nat 4 ==
  2 * green full_mat2 0%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

(** Cayley-Hamilton for off-diagonal *)
Lemma cayley_hamilton_golden_01 :
  green golden 0%nat 1%nat 3 ==
  char_p golden * green golden 0%nat 1%nat 2 - char_q golden * green golden 0%nat 1%nat 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem green_spectral_synthesis :
  (* Golden: trace=1, det=-1, Fibonacci recurrence *)
  char_p golden == 1 /\
  char_q golden == -(1) /\
  green golden 0%nat 0%nat 6 == 13 /\
  (* Cayley-Hamilton holds concretely *)
  green golden 0%nat 0%nat 4 ==
    char_p golden * green golden 0%nat 0%nat 3 - char_q golden * green golden 0%nat 0%nat 2 /\
  (* Full shift: trace=2, det=0, doubling *)
  char_p full_mat2 == 2 /\
  char_q full_mat2 == 0.
Proof.
  split; [exact golden_char_p|].
  split; [exact golden_char_q|].
  split; [exact green_golden_00_6|].
  split; [exact cayley_hamilton_golden_2|].
  split; [exact full_char_p|exact full_char_q].
Qed.
