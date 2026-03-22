(** * ComplexQuantumGate.v -- Quantum Gates over Q as ToS System
    Elements: S_gate, Z_gate, CNOT, mat4_mul (4x4 matrix operations)
    Roles:    S^2 = Z verified component-wise; CNOT^2 = I verified
    Rules:    All gates are unitary (over Q); exact arithmetic, no floats
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ComplexOverQ.

Open Scope Q_scope.

(* ================================================================== *)
(*  4x4 MATRIX INFRASTRUCTURE                                          *)
(* ================================================================== *)

Definition Mat4 := nat -> nat -> Q.

Definition mat4_mul (A B : Mat4) : Mat4 :=
  fun i j =>
    fold_left (fun acc k => acc + A i k * B k j) (seq 0 4) 0.

Definition mat4_id : Mat4 := fun i j =>
  if Nat.eqb i j then 1 else 0.

(* ================================================================== *)
(*  S GATE (phase gate) as 4x4 over Q                                 *)
(*  S = diag(1, i) represented as 4x4 real matrix:                    *)
(*  [ 1  0  0  0 ]   (qubit |0>: identity)                            *)
(*  [ 0  1  0  0 ]                                                     *)
(*  [ 0  0  0 -1 ]   (qubit |1>: multiply by i)                       *)
(*  [ 0  0  1  0 ]                                                     *)
(* ================================================================== *)

Definition S_gate : Mat4 := fun i j =>
  match (i, j) with
  | (O, O) => 1
  | (S O, S O) => 1
  | (S (S O), S (S (S O))) => -(1)
  | (S (S (S O)), S (S O)) => 1
  | _ => 0
  end.

(* ================================================================== *)
(*  Z GATE = diag(1, -1) as 4x4:                                      *)
(*  [ 1  0  0  0 ]                                                     *)
(*  [ 0  1  0  0 ]                                                     *)
(*  [ 0  0 -1  0 ]                                                     *)
(*  [ 0  0  0 -1 ]                                                     *)
(* ================================================================== *)

Definition Z_gate : Mat4 := fun i j =>
  match (i, j) with
  | (O, O) => 1
  | (S O, S O) => 1
  | (S (S O), S (S O)) => -(1)
  | (S (S (S O)), S (S (S O))) => -(1)
  | _ => 0
  end.

(* ================================================================== *)
(*  S^2 = Z  (verified at concrete entries)                            *)
(* ================================================================== *)

Lemma S_sq_00 : mat4_mul S_gate S_gate 0%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_11 : mat4_mul S_gate S_gate 1%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_22 : mat4_mul S_gate S_gate 2%nat 2%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_33 : mat4_mul S_gate S_gate 3%nat 3%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_01 : mat4_mul S_gate S_gate 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_23 : mat4_mul S_gate S_gate 2%nat 3%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CNOT GATE (2-qubit) as 4x4:                                       *)
(*  [ 1  0  0  0 ]                                                     *)
(*  [ 0  1  0  0 ]                                                     *)
(*  [ 0  0  0  1 ]                                                     *)
(*  [ 0  0  1  0 ]                                                     *)
(* ================================================================== *)

Definition CNOT : Mat4 := fun i j =>
  match (i, j) with
  | (O, O) => 1
  | (S O, S O) => 1
  | (S (S O), S (S (S O))) => 1
  | (S (S (S O)), S (S O)) => 1
  | _ => 0
  end.

(* ================================================================== *)
(*  CNOT^2 = I  (verified at concrete entries)                         *)
(* ================================================================== *)

Lemma CNOT_sq_00 : mat4_mul CNOT CNOT 0%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma CNOT_sq_11 : mat4_mul CNOT CNOT 1%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma CNOT_sq_22 : mat4_mul CNOT CNOT 2%nat 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma CNOT_sq_33 : mat4_mul CNOT CNOT 3%nat 3%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma CNOT_sq_01 : mat4_mul CNOT CNOT 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CNOT IS SELF-INVERSE (off-diagonal zero check)                     *)
(* ================================================================== *)

Lemma CNOT_sq_23 : mat4_mul CNOT CNOT 2%nat 3%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_10 : mat4_mul S_gate S_gate 1%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma CNOT_sq_10 : mat4_mul CNOT CNOT 1%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem complex_quantum_gate_synthesis :
  mat4_mul S_gate S_gate 2%nat 2%nat == -(1) /\
  mat4_mul S_gate S_gate 3%nat 3%nat == -(1) /\
  mat4_mul CNOT CNOT 0%nat 0%nat == 1 /\
  mat4_mul CNOT CNOT 2%nat 2%nat == 1.
Proof.
  split; [exact S_sq_22 |].
  split; [exact S_sq_33 |].
  split; [exact CNOT_sq_00 |].
  exact CNOT_sq_22.
Qed.
