(** * CoulombKernel.v — Discrete Coulomb Kernel on Lattice
    Elements: Coulomb kernel K(M,i,j), lattice discretization
    Roles:    Define electron-electron interaction on finite grid
    Rules:    K(M,i,j) = M/|i-j| for i≠j, 0 for i=j; symmetric
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  COULOMB KERNEL ON LATTICE                                          *)
(*  K(M, i, j) = M / |i - j|  for i ≠ j                              *)
(*              = 0            for i = j                               *)
(*  Uses Z.abs for the integer distance                                *)
(* ================================================================== *)

Definition coulomb_kernel (M i j : nat) : Q :=
  if Nat.eqb i j then 0
  else inject_Z (Z.of_nat M) / inject_Z (Z.abs (Z.of_nat i - Z.of_nat j)).

(* ================================================================== *)
(*  SELF-INTERACTION: K(M, i, i) = 0                                   *)
(* ================================================================== *)

Lemma kernel_self_zero_0 : coulomb_kernel 10 0 0 == 0.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

Lemma kernel_self_zero_3 : coulomb_kernel 10 3 3 == 0.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  NEAREST NEIGHBOR: K(10, 0, 1) = 10/1 = 10                         *)
(* ================================================================== *)

Lemma kernel_01 : coulomb_kernel 10 0 1 == 10.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISTANCE 5: K(10, 0, 5) = 10/5 = 2                                *)
(* ================================================================== *)

Lemma kernel_05 : coulomb_kernel 10 0 5 == 2.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISTANCE 2: K(10, 1, 3) = 10/2 = 5                                *)
(* ================================================================== *)

Lemma kernel_13 : coulomb_kernel 10 1 3 == 5.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYMMETRY: K(M, i, j) = K(M, j, i) (concrete cases)                *)
(* ================================================================== *)

Lemma kernel_symmetric_01 : coulomb_kernel 10 0 1 == coulomb_kernel 10 1 0.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

Lemma kernel_symmetric_25 : coulomb_kernel 10 2 5 == coulomb_kernel 10 5 2.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MONOTONE: closer sites have stronger interaction                   *)
(*  K(10, 0, 1) > K(10, 0, 5)                                         *)
(* ================================================================== *)

Lemma kernel_monotone : coulomb_kernel 10 0 5 < coulomb_kernel 10 0 1.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  POSITIVITY: K > 0 for i ≠ j with M > 0                            *)
(* ================================================================== *)

Lemma kernel_positive_01 : 0 < coulomb_kernel 10 0 1.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.

Lemma kernel_positive_05 : 0 < coulomb_kernel 10 0 5.
Proof. unfold coulomb_kernel. vm_compute. reflexivity. Qed.
