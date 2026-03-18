(* ProcessSynthesisCleanup2.v — Close True in Fermion/ERRGauge synthesis *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.TheoremBundle.
From ToS Require Import process.ProcessERRSymmetry.
From ToS Require Import process.ProcessERRFermion.
From ToS Require Import process.ProcessPauliExclusion.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.
From ToS Require Import process.ProcessPhysicalSigma.
From ToS Require Import process.ProcessWeinbergAngle.
From ToS Require Import process.ProcessERRDerived.

(** FermionSynthesis: Pauli exclusion from ERR *)
Theorem synth_pauli : forall sys i,
  is_fermionic sys -> (i < err_nsites sys)%nat -> err_rule sys i i == 0.
Proof. exact bundle_pauli. Qed.

(** FermionSynthesis: rule decomposition symmetric + antisymmetric *)
Theorem synth_decomp : forall sys i j,
  err_rule sys i j == rule_symmetric sys i j + rule_antisymmetric sys i j.
Proof. exact bundle_decomposition. Qed.

(** ERRGaugeSynthesis: mass gap from SU(2) *)
Theorem synth_gauge_gap : 0 < matrix_mass_gap 1 1 0.
Proof. exact bundle_gap_positive. Qed.

(** ERRGaugeSynthesis: gap value *)
Theorem synth_gauge_gap_value : matrix_mass_gap 1 1 0 == 289 # 384.
Proof. exact bundle_gap_value. Qed.

(** ERRGaugeSynthesis: string tension *)
Theorem synth_sigma : I1_partial 1 1 / I0_partial 1 1 == 9 # 20.
Proof. exact bundle_sigma. Qed.

(** ERR nroles >= 2 *)
Theorem synth_err_nroles : forall hp hi ha,
  (2 <= err_nroles (err_from_principles hp hi ha))%nat.
Proof.
  intros. destruct (bundle_err_derived hp hi ha) as [_ [_ [_ H]]]. exact H.
Qed.

Definition synth_cleanup2_count := 6%nat.
