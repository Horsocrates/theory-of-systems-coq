(** * HydrogenRadial.v -- Hydrogen Hamiltonian on finite lattice (radial part)
    Elements: H_hydrogen (kinetic + Coulomb), matrix entries, trace
    Roles:    Tridiagonal kinetic + diagonal Coulomb → Hamiltonian as process
    Rules:    All over Q, concrete entries verified for M=2, K=3
    Status:   Stdlib
    STATUS: 17 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

(* ================================================================== *)
(*  HYDROGEN HAMILTONIAN: H(M, K, i, j)                               *)
(*  Kinetic: tridiagonal with 2M² on diagonal, -M² on off-diagonal    *)
(*  Coulomb: -2M/(i+1) on diagonal                                    *)
(* ================================================================== *)

(** Hydrogen Hamiltonian matrix entry.
    H(i,j) = δ(i,j) * (2*M² - 2*M/(i+1)) + δ(|i-j|,1) * (-M²)
    We define outside Q_scope to avoid nat literal issues. *)

Definition H_hydrogen (M K i j : nat) : Q :=
  let Mq := inject_Z (Z.of_nat M) in
  let ip1 := inject_Z (Z.of_nat (S i)) in
  if Nat.eqb i j then
    2 * Mq * Mq - 2 * Mq / ip1
  else if orb (Nat.eqb (S i) j) (Nat.eqb i (S j)) then
    - (Mq * Mq)
  else
    0.

Open Scope Q_scope.

(* ================================================================== *)
(*  CONCRETE ENTRIES FOR M=2                                           *)
(* ================================================================== *)

(** H(2,K,0,0) = 2*4 - 2*2/1 = 8 - 4 = 4 *)
Lemma H_M2_diag0 : H_hydrogen 2 10 0 0 == 4.
Proof. vm_compute. reflexivity. Qed.

(** H(2,K,1,1) = 8 - 2*2/2 = 8 - 2 = 6 *)
Lemma H_M2_diag1 : H_hydrogen 2 10 1 1 == 6.
Proof. vm_compute. reflexivity. Qed.

(** H(2,K,2,2) = 8 - 2*2/3 = 8 - 4/3 = 20/3 *)
Lemma H_M2_diag2 : H_hydrogen 2 10 2 2 == 20#3.
Proof. vm_compute. reflexivity. Qed.

(** H(2,K,0,1) = -M² = -4 *)
Lemma H_M2_off01 : H_hydrogen 2 10 0 1 == -(4).
Proof. vm_compute. reflexivity. Qed.

(** H(2,K,1,0) = -M² = -4 *)
Lemma H_M2_off10 : H_hydrogen 2 10 1 0 == -(4).
Proof. vm_compute. reflexivity. Qed.

(** H(2,K,1,2) = -4 *)
Lemma H_M2_off12 : H_hydrogen 2 10 1 2 == -(4).
Proof. vm_compute. reflexivity. Qed.

(** H(2,K,2,1) = -4 *)
Lemma H_M2_off21 : H_hydrogen 2 10 2 1 == -(4).
Proof. vm_compute. reflexivity. Qed.

(** Non-adjacent entries are zero *)
Lemma H_M2_zero02 : H_hydrogen 2 10 0 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE FOR K=3                                                      *)
(* ================================================================== *)

Definition trace_H (M K : nat) : Q :=
  let fix sum_diag (k : nat) : Q :=
    match k with
    | O => H_hydrogen M K 0 0
    | S k' => sum_diag k' + H_hydrogen M K (S k') (S k')
    end
  in sum_diag (pred K).

(** tr(H) for M=2, K=3: 4 + 6 + 20/3 = 50/3 *)
Lemma trace_M2_K3 : trace_H 2 3 == 50#3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYMMETRY                                                           *)
(* ================================================================== *)

(** H is symmetric: H(i,j) = H(j,i) for concrete entries *)
Lemma H_symmetric_01 : H_hydrogen 2 10 0 1 == H_hydrogen 2 10 1 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H_symmetric_12 : H_hydrogen 2 10 1 2 == H_hydrogen 2 10 2 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DIAGONAL DOMINANCE CHECK                                           *)
(* ================================================================== *)

(** Diagonal entry grows: H(2,K,0,0) < H(2,K,1,1) *)
Lemma diag_grows_01 : H_hydrogen 2 10 0 0 < H_hydrogen 2 10 1 1.
Proof. vm_compute. reflexivity. Qed.

(** Diagonal entry grows: H(2,K,1,1) < H(2,K,2,2) *)
Lemma diag_grows_12 : H_hydrogen 2 10 1 1 < H_hydrogen 2 10 2 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  KINETIC AND COULOMB PARTS                                          *)
(* ================================================================== *)

Definition H_kinetic (M K i j : nat) : Q :=
  let Mq := inject_Z (Z.of_nat M) in
  if Nat.eqb i j then
    2 * Mq * Mq
  else if orb (Nat.eqb (S i) j) (Nat.eqb i (S j)) then
    - (Mq * Mq)
  else
    0.

Definition H_coulomb (M i : nat) : Q :=
  let Mq := inject_Z (Z.of_nat M) in
  let ip1 := inject_Z (Z.of_nat (S i)) in
  - (2 * Mq / ip1).

(** Decomposition: H = kinetic + coulomb on diagonal *)
Lemma H_decomp_diag0 : H_hydrogen 2 10 0 0 == H_kinetic 2 10 0 0 + H_coulomb 2 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H_decomp_diag1 : H_hydrogen 2 10 1 1 == H_kinetic 2 10 1 1 + H_coulomb 2 1.
Proof. vm_compute. reflexivity. Qed.

(** Kinetic diagonal = 2M² = 8 for M=2 *)
Lemma kinetic_diag_M2 : H_kinetic 2 10 0 0 == 8.
Proof. vm_compute. reflexivity. Qed.

(** Coulomb diagonal for i=0: -2*2/1 = -4 *)
Lemma coulomb_diag0_M2 : H_coulomb 2 0 == -(4).
Proof. vm_compute. reflexivity. Qed.
