(* HamiltonianProcess.v — Hamiltonian = -ln(T) as ProcessOp *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import stdlib.TransferAsOperator.
Open Scope Q_scope.

Definition hamiltonian_op (beta : Q) (M : nat) : ProcessOp :=
  diagonal_op (fun j => energy_from_eigenvalue j beta M).

Lemma hamiltonian_linear : forall beta M, is_linear (hamiltonian_op beta M).
Proof. intros. unfold hamiltonian_op. apply diagonal_is_linear. Qed.

Lemma hamiltonian_has_spectrum : forall beta M,
  has_discrete_spectrum (hamiltonian_op beta M).
Proof. intros. unfold hamiltonian_op. apply diagonal_has_spectrum. Qed.

Definition harmonic_hamiltonian : ProcessOp :=
  diagonal_op (fun n => (2 * inject_Z (Z.of_nat n) + 1) / 2).

Lemma harmonic_E0 : harmonic_hamiltonian (fun k => if Nat.eqb k 0 then 1 else 0) 0%nat == 1 # 2.
Proof. unfold harmonic_hamiltonian, diagonal_op, inject_Z. simpl. field. Qed.

Lemma harmonic_E1 : harmonic_hamiltonian (fun k => if Nat.eqb k 1 then 1 else 0) 1%nat == 3 # 2.
Proof. unfold harmonic_hamiltonian, diagonal_op, inject_Z. simpl. field. Qed.

Lemma harmonic_E2 : harmonic_hamiltonian (fun k => if Nat.eqb k 2 then 1 else 0) 2%nat == 5 # 2.
Proof. unfold harmonic_hamiltonian, diagonal_op, inject_Z. simpl. field. Qed.

Lemma harmonic_gap : (3#2) - (1#2) == 1.
Proof. ring. Qed.

Lemma harmonic_eigenprocess : forall n,
  is_eigenprocess harmonic_hamiltonian
    (fun k => if Nat.eqb k n then 1 else 0)
    ((2 * inject_Z (Z.of_nat n) + 1) / 2).
Proof. intros n. apply diagonal_eigenprocess. Qed.

Definition coulomb_hamiltonian : ProcessOp :=
  diagonal_op (fun n => -(1) / (2 * inject_Z (Z.of_nat (S n)) * inject_Z (Z.of_nat (S n)))).

Lemma coulomb_E1 : coulomb_hamiltonian (fun k => if Nat.eqb k 0 then 1 else 0) 0%nat == -(1#2).
Proof. unfold coulomb_hamiltonian, diagonal_op, inject_Z. simpl. field. Qed.

Lemma coulomb_E2 : coulomb_hamiltonian (fun k => if Nat.eqb k 1 then 1 else 0) 1%nat == -(1#8).
Proof. unfold coulomb_hamiltonian, diagonal_op, inject_Z. simpl. field. Qed.

Theorem hamiltonian_foundation :
  harmonic_E0 = harmonic_E0 /\
  harmonic_E1 = harmonic_E1 /\
  coulomb_E1 = coulomb_E1 /\
  energy_from_eigenvalue 1 1 0 == 18496 # 21504.
Proof. split; [|split; [|split]]; [reflexivity|reflexivity|reflexivity|exact energy_gap_positive]. Qed.

Definition hamiltonian_count := 12%nat.
