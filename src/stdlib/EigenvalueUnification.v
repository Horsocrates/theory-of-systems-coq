(* EigenvalueUnification.v — Eigenvalues as ProcessOperator instances *)
From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import stdlib.TransferAsOperator.
From ToS Require Import stdlib.HamiltonianProcess.
Open Scope Q_scope.
Theorem transfer_is_diagonal : is_linear (transfer_op 1 0%nat).
Proof. apply transfer_linear. Qed.
Theorem transfer_has_spectrum_instance : has_discrete_spectrum (transfer_op 1 0%nat).
Proof. apply transfer_has_spectrum. Qed.
Theorem harmonic_is_diagonal : is_linear (diagonal_op (fun n => (2 * inject_Z (Z.of_nat n) + 1) / 2)).
Proof. apply diagonal_is_linear. Qed.
Theorem coulomb_is_diagonal : is_linear coulomb_hamiltonian.
Proof. unfold coulomb_hamiltonian. apply diagonal_is_linear. Qed.
Theorem eigenvalue_unified :
  is_linear (transfer_op 1 0%nat) /\ is_linear coulomb_hamiltonian /\
  transfer_eigenvalue 0 1 0%nat == 7 # 8.
Proof. split; [|split]; [exact transfer_is_diagonal | exact coulomb_is_diagonal | exact transfer_eigenvalue_value]. Qed.
Definition eigenvalue_unification_count := 5%nat.
