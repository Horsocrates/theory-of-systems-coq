(** * GellMannExplicit.v -- Gell-Mann Matrices (lambda_1,2,3,8) as ToS System
    Elements: lambda1, lambda2, lambda3, lambda8_scaled as 3x3 Q matrices
    Roles:    SU(3) generators; tracelessness verified entry-by-entry
    Rules:    lambda8 scaled by sqrt(3) to stay rational; commutation structure
    Status:   Stdlib -- Six Directions Phase 2, Section D3
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  3x3 MATRICES OVER Q (function-based)                                *)
(* ================================================================== *)

Definition Mat3 := nat -> nat -> Q.

Definition mat3_trace (M : Mat3) : Q :=
  M O O + M 1%nat 1%nat + M 2%nat 2%nat.

(* ================================================================== *)
(*  GELL-MANN MATRICES lambda_1, lambda_2, lambda_3                    *)
(*  lambda_1 = [[0,1,0],[1,0,0],[0,0,0]]                              *)
(*  lambda_2 = [[0,-1,0],[1,0,0],[0,0,0]]  (times i, we store real)   *)
(*  lambda_3 = [[1,0,0],[0,-1,0],[0,0,0]]                             *)
(* ================================================================== *)

Definition lambda1 : Mat3 := fun i j =>
  match i, j with
  | O, S O => 1
  | S O, O => 1
  | _, _ => 0
  end.

(* lambda_2 real part: entries where imaginary would go *)
Definition lambda2_real : Mat3 := fun i j =>
  match i, j with
  | O, S O => -(1)
  | S O, O => 1
  | _, _ => 0
  end.

Definition lambda3 : Mat3 := fun i j =>
  match i, j with
  | O, O => 1
  | S O, S O => -(1)
  | _, _ => 0
  end.

(* lambda_8 = diag(1,1,-2) / sqrt(3), we store sqrt(3)*lambda_8 = diag(1,1,-2) *)
Definition lambda8_scaled : Mat3 := fun i j =>
  match i, j with
  | O, O => 1
  | S O, S O => 1
  | S (S O), S (S O) => -(2)
  | _, _ => 0
  end.

(* ================================================================== *)
(*  TRACELESSNESS                                                       *)
(* ================================================================== *)

Lemma trace_lambda1 : mat3_trace lambda1 == 0.
Proof. unfold mat3_trace, lambda1. vm_compute. reflexivity. Qed.

Lemma trace_lambda2 : mat3_trace lambda2_real == 0.
Proof. unfold mat3_trace, lambda2_real. vm_compute. reflexivity. Qed.

Lemma trace_lambda3 : mat3_trace lambda3 == 0.
Proof. unfold mat3_trace, lambda3. vm_compute. reflexivity. Qed.

Lemma trace_lambda8 : mat3_trace lambda8_scaled == 0.
Proof. unfold mat3_trace, lambda8_scaled. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ENTRY VERIFICATION                                                  *)
(* ================================================================== *)

Lemma lambda1_01 : lambda1 O 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda1_10 : lambda1 1%nat O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda1_00 : lambda1 O O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda3_00 : lambda3 O O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda3_11 : lambda3 1%nat 1%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma lambda8_22 : lambda8_scaled 2%nat 2%nat == -(2).
Proof. vm_compute. reflexivity. Qed.

(* Off-diagonal zeros *)
Lemma lambda3_01 : lambda3 O 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda8_01 : lambda8_scaled O 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda8_00 : lambda8_scaled O O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda2_01 : lambda2_real O 1%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem gellmann_synthesis :
  (mat3_trace lambda1 == 0) /\
  (mat3_trace lambda3 == 0) /\
  (mat3_trace lambda8_scaled == 0) /\
  (lambda1 O 1%nat == 1) /\
  (lambda3 O O == 1).
Proof.
  split. { exact trace_lambda1. }
  split. { exact trace_lambda3. }
  split. { exact trace_lambda8. }
  split. { exact lambda1_01. }
  exact lambda3_00.
Qed.
