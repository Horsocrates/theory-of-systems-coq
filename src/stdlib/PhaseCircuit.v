(** * PhaseCircuit.v -- Phase gates as 4x4 matrices: S^2 = Z, S^4 = I
    Elements: S_gate_4, Z_gate_4, I_gate_4 as 4x4 diagonal matrices
    Roles:    Phase accumulation: S rotates by pi/2, Z by pi, S^4 = full cycle
    Rules:    S^2 = Z (universal), S^4 = I (universal), interference from phase
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ComplexOverQ.
Open Scope Q_scope.

(* ================================================================== *)
(*  LOCAL: 4x4 matrix multiplication                                   *)
(* ================================================================== *)

Definition mat4_mul_pc (A B : nat -> nat -> Q) (r c : nat) : Q :=
  fold_left (fun acc m => acc + A r m * B m c) (seq 0%nat 4%nat) 0.

(* ================================================================== *)
(*  PART I: GATE DEFINITIONS                                           *)
(* ================================================================== *)

(* S gate: phase by i on |1>, identity on |0>. Embedded in 4x4: *)
(* S = diag(1, i, 1, i) but using real 4x4 rep of complex:     *)
(* Qubit |0> maps to block rows 0-1, |1> to block rows 2-3     *)
(* Block for |0>: I_2 (identity), block for |1>: C_i            *)
(* S_gate_4 = diag_block(I_2, C_i)                              *)

Definition S_gate_4 (r c : nat) : Q :=
  match (r, c) with
  | (O, O) => 1 | (S O, S O) => 1
  | (S (S O), S (S (S O))) => -(1) | (S (S (S O)), S (S O)) => 1
  | _ => 0
  end.

(* Z gate: phase by -1 on |1>, identity on |0>                  *)
(* Z_gate_4 = diag_block(I_2, -I_2)                             *)

Definition Z_gate_4 (r c : nat) : Q :=
  match (r, c) with
  | (O, O) => 1 | (S O, S O) => 1
  | (S (S O), S (S O)) => -(1) | (S (S (S O)), S (S (S O))) => -(1)
  | _ => 0
  end.

(* Identity 4x4 *)
Definition I_gate_4 (r c : nat) : Q :=
  match (r, c) with
  | (O, O) => 1 | (S O, S O) => 1
  | (S (S O), S (S O)) => 1 | (S (S (S O)), S (S (S O))) => 1
  | _ => 0
  end.

(* ================================================================== *)
(*  PART II: S^2 = Z (universal over bounded r,c)                      *)
(* ================================================================== *)

Lemma S_sq_00 : mat4_mul_pc S_gate_4 S_gate_4 O O == Z_gate_4 O O.
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_11 : mat4_mul_pc S_gate_4 S_gate_4 (S O) (S O) == Z_gate_4 (S O) (S O).
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_22 : mat4_mul_pc S_gate_4 S_gate_4 (S (S O)) (S (S O)) == Z_gate_4 (S (S O)) (S (S O)).
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_33 : mat4_mul_pc S_gate_4 S_gate_4 (S (S (S O))) (S (S (S O))) == Z_gate_4 (S (S (S O))) (S (S (S O))).
Proof. vm_compute. reflexivity. Qed.

Lemma S_sq_eq_Z : forall r c, (r <= 3)%nat -> (c <= 3)%nat ->
  mat4_mul_pc S_gate_4 S_gate_4 r c == Z_gate_4 r c.
Proof.
  intros r c Hr Hc.
  do 4 (try destruct r; try lia); do 4 (try destruct c; try lia);
  vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  PART III: S^4 = I (universal over bounded r,c)                     *)
(* ================================================================== *)

Definition S_sq (r c : nat) : Q := mat4_mul_pc S_gate_4 S_gate_4 r c.
Definition S_4th (r c : nat) : Q := mat4_mul_pc S_sq S_sq r c.

Lemma S_4th_eq_I : forall r c, (r <= 3)%nat -> (c <= 3)%nat ->
  S_4th r c == I_gate_4 r c.
Proof.
  intros r c Hr Hc.
  do 4 (try destruct r; try lia); do 4 (try destruct c; try lia);
  vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  PART IV: INTERFERENCE — phase changes measurement                  *)
(* ================================================================== *)

(* State |+> = (1,0,1,0) in 4x4 rep (|0>+|1> unnormalized)       *)
(* After S: S|+> = (1,0,0,1) — imaginary rotation on |1> block   *)
(* Measurement: |<0|S|+>|^2 vs |<1|S|+>|^2 unchanged (still 1:1) *)

Lemma S_on_plus_0 : mat4_mul_pc S_gate_4 (fun r _ => match r with O => 1 | S (S O) => 1 | _ => 0 end) O O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma S_on_plus_2 : mat4_mul_pc S_gate_4 (fun r _ => match r with O => 1 | S (S O) => 1 | _ => 0 end) (S (S O)) O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma S_on_plus_3 : mat4_mul_pc S_gate_4 (fun r _ => match r with O => 1 | S (S O) => 1 | _ => 0 end) (S (S (S O))) O == 1.
Proof. vm_compute. reflexivity. Qed.

(* After Z: Z|+> = (1,0,-1,0) — destructive interference on |1> *)
Lemma Z_on_plus_2 : mat4_mul_pc Z_gate_4 (fun r _ => match r with O => 1 | S (S O) => 1 | _ => 0 end) (S (S O)) O == -(1).
Proof. vm_compute. reflexivity. Qed.

(* Z flips sign of |1> component — observable interference *)
Lemma Z_flips_component :
  mat4_mul_pc Z_gate_4 (fun r _ => match r with O => 1 | S (S O) => 1 | _ => 0 end) (S (S O)) O ==
  -(mat4_mul_pc I_gate_4 (fun r _ => match r with O => 1 | S (S O) => 1 | _ => 0 end) (S (S O)) O).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem phase_circuit_synthesis :
  (* S^2 = Z *)
  mat4_mul_pc S_gate_4 S_gate_4 (S (S O)) (S (S O)) == Z_gate_4 (S (S O)) (S (S O)) /\
  (* S^4 = I *)
  S_4th O O == I_gate_4 O O /\
  S_4th (S (S O)) (S (S O)) == I_gate_4 (S (S O)) (S (S O)).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
