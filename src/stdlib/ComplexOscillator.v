(** * ComplexOscillator.v -- Oscillator Hamiltonian with Complex Numbers as ToS System
    Elements: number_op, osc_hamiltonian (H = N + 1/2 on finite lattice)
    Roles:    Eigenvalues verified at concrete K; trace computations
    Rules:    H diagonal with E_n = n + 1/2; trace(N) = K(K-1)/2
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
(*  NUMBER OPERATOR AND HAMILTONIAN ON FINITE LATTICE                  *)
(* ================================================================== *)

Definition number_op (K : nat) (i j : nat) : Q :=
  if Nat.eqb i j then inject_Z (Z.of_nat i) else 0.

Definition osc_hamiltonian (K : nat) (i j : nat) : Q :=
  number_op K i j + (if Nat.eqb i j then (1#2) else 0).

(* ================================================================== *)
(*  EIGENVALUE VERIFICATION (K=3, states 0,1,2)                       *)
(* ================================================================== *)

Lemma H_eigenvalue_0 : osc_hamiltonian 3 0%nat 0%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma H_eigenvalue_1 : osc_hamiltonian 3 1%nat 1%nat == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma H_eigenvalue_2 : osc_hamiltonian 3 2%nat 2%nat == 5#2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DIAGONAL STRUCTURE                                                  *)
(* ================================================================== *)

Lemma H_diagonal_01 : osc_hamiltonian 3 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H_diagonal_10 : osc_hamiltonian 3 1%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H_diagonal_02 : osc_hamiltonian 3 0%nat 2%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE OF NUMBER OPERATOR: tr(N) = 0+1+...+(K-1) = K(K-1)/2        *)
(* ================================================================== *)

Definition trace_sum (f : nat -> nat -> Q) (K : nat) : Q :=
  fold_left (fun acc k => acc + f k k) (seq 0 K) 0.

Lemma tr_N_3 : trace_sum (number_op 3) 3 == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_N_5 : trace_sum (number_op 5) 5 == 10.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_N_10 : trace_sum (number_op 10) 10 == 45.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE OF N^2: tr(N^2) = 0+1+4+...+(K-1)^2 = K(K-1)(2K-1)/6       *)
(* ================================================================== *)

Definition number_sq (K : nat) (i j : nat) : Q :=
  if Nat.eqb i j then inject_Z (Z.of_nat i) * inject_Z (Z.of_nat i) else 0.

Lemma tr_N2_5 : trace_sum (number_sq 5) 5 == 30.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE COMPARISON: tr(H) = tr(N) + K/2                              *)
(* ================================================================== *)

Lemma tr_H_3 : trace_sum (osc_hamiltonian 3) 3 == 9#2.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_H_5 : trace_sum (osc_hamiltonian 5) 5 == 25#2.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_N2_3 : trace_sum (number_sq 3) 3 == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma H_diagonal_12 : osc_hamiltonian 3 1%nat 2%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem complex_oscillator_synthesis :
  osc_hamiltonian 3 0%nat 0%nat == 1#2 /\
  osc_hamiltonian 3 1%nat 1%nat == 3#2 /\
  osc_hamiltonian 3 0%nat 1%nat == 0 /\
  trace_sum (number_op 3) 3 == 3 /\
  trace_sum (osc_hamiltonian 3) 3 == 9#2.
Proof.
  split; [exact H_eigenvalue_0 |].
  split; [exact H_eigenvalue_1 |].
  split; [exact H_diagonal_01 |].
  split; [exact tr_N_3 |].
  exact tr_H_3.
Qed.
