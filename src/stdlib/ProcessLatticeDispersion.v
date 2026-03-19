(* ProcessLatticeDispersion.v — Dispersion from transfer matrix *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import SeriesConvergence.
From ToS Require Import stdlib.TransferAsOperator.
From ToS Require Import gauge.CharacterTransfer.
Open Scope Q_scope.

Definition lattice_momentum (j K : nat) : Q :=
  2 * (22#7) * inject_Z (Z.of_nat j) / inject_Z (Z.of_nat (S K)).

Lemma momentum_0 : forall K, lattice_momentum 0 K == 0.
Proof. intros. unfold lattice_momentum, inject_Z. simpl. field.
  unfold Qeq. simpl. lia.
Qed.

Lemma momentum_positive : forall K, 0 < lattice_momentum 1 (S K).
Proof.
  intros K. unfold lattice_momentum, inject_Z. simpl.
  apply Qmult_lt_0_compat; [|apply Qinv_lt_0_compat; unfold Qlt; simpl; lia].
  apply Qmult_lt_0_compat; [lra|lra].
Qed.

Definition lattice_energy (j : nat) (beta : Q) (M : nat) : Q :=
  energy_from_eigenvalue j beta M.

Lemma energy_0 : forall beta M,
  ~(transfer_eigenvalue 0 beta M == 0) ->
  lattice_energy 0 beta M == 0.
Proof. intros. unfold lattice_energy. apply ground_energy_zero. exact H. Qed.

Lemma energy_1_value : lattice_energy 1 1 0%nat == 18496 # 21504.
Proof. unfold lattice_energy. exact energy_gap_positive. Qed.

Lemma energy_1_positive : 0 < lattice_energy 1 1 0%nat.
Proof. rewrite energy_1_value. lra. Qed.

Definition effective_mass (beta : Q) (M K : nat) : Q :=
  let k1 := lattice_momentum 1 K in
  let E1 := lattice_energy 1 beta M in
  k1 * k1 / (2 * E1).

Definition dispersion_D (beta : Q) (M K : nat) : Q :=
  lattice_energy 1 beta M / (lattice_momentum 1 K * lattice_momentum 1 K).

Lemma dispersion_positive : forall K,
  0 < lattice_energy 1 1 0%nat ->
  0 < lattice_momentum 1 (S K) ->
  0 < dispersion_D 1 0%nat (S K).
Proof.
  intros K HE Hk. unfold dispersion_D.
  apply Qmult_lt_0_compat; [exact HE|].
  apply Qinv_lt_0_compat.
  apply Qmult_lt_0_compat; exact Hk.
Qed.

Definition dispersion_process (beta : Q) (M : nat) : RealProcess :=
  fun K => dispersion_D beta M K.

Theorem lattice_dispersion_foundation :
  lattice_energy 1 1 0%nat == 18496 # 21504 /\
  0 < lattice_energy 1 1 0%nat /\
  (forall K, lattice_momentum 0 K == 0).
Proof.
  split; [|split].
  - exact energy_1_value.
  - exact energy_1_positive.
  - exact momentum_0.
Qed.

Definition dispersion_count := 10%nat.
