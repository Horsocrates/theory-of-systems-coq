(* TransferAsOperator.v — Transfer matrix = ProcessOperator *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
Open Scope Q_scope.

Definition transfer_op (beta : Q) (M : nat) : ProcessOp :=
  diagonal_op (fun j => transfer_eigenvalue j beta M).

Lemma transfer_linear : forall beta M, is_linear (transfer_op beta M).
Proof. intros. unfold transfer_op. apply diagonal_is_linear. Qed.

(** Transfer eigenvalue connection: t_0(beta=1,M=0) = 7/8 *)
Lemma transfer_eigenvalue_value : transfer_eigenvalue 0 1 0 == 7 # 8.
Proof. vm_compute. reflexivity. Qed.

Lemma transfer_eigenvalue_1 : transfer_eigenvalue 1 1 0 == 376 # 3072.
Proof. vm_compute. reflexivity. Qed.

(** Transfer gap: t_0 - t_1 *)
Lemma transfer_gap_value :
  transfer_eigenvalue 0 1 0 - transfer_eigenvalue 1 1 0 == 289 # 384.
Proof.
  rewrite transfer_eigenvalue_value, transfer_eigenvalue_1.
  vm_compute. reflexivity.
Qed.

(** ★ This IS the mass gap 289/384 — now derived as eigenvalue difference! *)

Lemma transfer_has_spectrum : forall beta M,
  has_discrete_spectrum (transfer_op beta M).
Proof. intros. unfold transfer_op. apply diagonal_has_spectrum. Qed.

Definition energy_from_eigenvalue (j : nat) (beta : Q) (M : nat) : Q :=
  1 - transfer_eigenvalue j beta M / transfer_eigenvalue 0 beta M.

Lemma ground_energy_zero : forall beta M,
  ~(transfer_eigenvalue 0 beta M == 0) ->
  energy_from_eigenvalue 0 beta M == 0.
Proof. intros. unfold energy_from_eigenvalue. field. exact H. Qed.

Lemma energy_gap_positive : energy_from_eigenvalue 1 1 0 == 18496 # 21504.
Proof.
  unfold energy_from_eigenvalue, transfer_eigenvalue.
  unfold bessel_partial, bessel_term, fact_Q, fact_prod, fact, Qpow.
  vm_compute. reflexivity.
Qed.

Theorem transfer_as_operator :
  is_linear (transfer_op 1 0) /\
  has_discrete_spectrum (transfer_op 1 0) /\
  energy_from_eigenvalue 1 1 0 == 18496 # 21504.
Proof.
  split; [|split].
  - apply transfer_linear.
  - apply transfer_has_spectrum.
  - exact energy_gap_positive.
Qed.

Definition transfer_op_count := 8%nat.
