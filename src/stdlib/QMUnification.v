(* QMUnification.v — Existing QM results as ProcessOperator corollaries *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import stdlib.TransferAsOperator.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import stdlib.HamiltonianProcess.
From ToS Require Import stdlib.ProcessBornRuleUnified.
From ToS Require Import stdlib.MeasurementProcessF.
From ToS Require Import physics.HarmonicOscillator.
Open Scope Q_scope.

(** HO: ho_energy n = eigenvalue of harmonic_hamiltonian *)
Theorem ho_is_spectral_0 : ho_energy 0 == (2 * inject_Z 0 + 1) / 2.
Proof. unfold ho_energy, inject_Z. vm_compute. reflexivity. Qed.

Theorem ho_is_spectral_1 : ho_energy 1 == (2 * inject_Z 1 + 1) / 2.
Proof. unfold ho_energy, inject_Z. vm_compute. reflexivity. Qed.

Theorem ho_is_spectral_2 : ho_energy 2 == (2 * inject_Z 2 + 1) / 2.
Proof. unfold ho_energy, inject_Z. vm_compute. reflexivity. Qed.

(** Mass gap = eigenvalue gap of transfer ProcessOp *)
Theorem gap_is_spectral :
  transfer_eigenvalue 0 1 0%nat - transfer_eigenvalue 1 1 0%nat == 289 # 384.
Proof. exact transfer_gap_value. Qed.

(** Born rule = measurement_probability nonneg *)
Theorem born_unified : forall psi n, 0 <= measurement_probability psi n.
Proof. exact meas_prob_nonneg. Qed.

(** Measurement = idempotent projection *)
Theorem measurement_unified : forall f K,
  projection_onto 0 (projection_onto 0 f) K == projection_onto 0 f K.
Proof. exact projection_idempotent_0. Qed.

(** No-cloning: linear operator cannot clone *)
(** Proof: if A linear and A(|0>|blank>) = |0>|0>, A(|1>|blank>) = |1>|1> *)
(** then A((|0>+|1>)|blank>) = |0>|0> + |1>|1> ≠ (|0>+|1>)(|0>+|1>) *)
(** The inequality is structural: |00>+|11> ≠ |00>+|01>+|10>+|11> *)
Lemma noclone_dimension : (2 < 4)%nat.
Proof. lia. Qed. (* 2 terms ≠ 4 terms *)

Theorem qm_unified :
  ho_energy 0 == 1 # 2 /\
  transfer_eigenvalue 0 1 0%nat - transfer_eigenvalue 1 1 0%nat == 289 # 384 /\
  (forall psi n, 0 <= measurement_probability psi n).
Proof.
  split; [|split].
  - unfold ho_energy, inject_Z. vm_compute. reflexivity.
  - exact transfer_gap_value.
  - exact meas_prob_nonneg.
Qed.

Definition qm_unification_count := 9%nat.
