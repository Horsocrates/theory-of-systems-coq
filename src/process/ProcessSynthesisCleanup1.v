(* ProcessSynthesisCleanup1.v — Close True in Step3/Step5 synthesis *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.TheoremBundle.
From ToS Require Import stdlib.OS1Closure.
From ToS Require Import process.ProcessERRDerived.
From ToS Require Import process.ProcessERRSymmetry.
From ToS Require Import process.ProcessRegge.
From ToS Require Import process.ProcessP3Gravity.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.
From ToS Require Import process.ProcessWeinbergAngle.
From ToS Require Import process.ProcessPhysicalSigma.

(** Step3 Phase 18: E/R/R → gauge *)
(** Concrete: err_is_derived gives (2 <= nroles) *)
Theorem synth3_err : forall hp hi ha,
  let sys := err_from_principles hp hi ha in
  (0 < err_nsites sys)%nat /\ (2 <= err_nroles sys)%nat.
Proof.
  intros hp hi ha. destruct (bundle_err_derived hp hi ha) as [H1 [H2 [H3 H4]]].
  split; exact H3 || exact H4.
Qed.

(** Step3 Phase 19: P3 → metric *)
(** Concrete: deficit_angle(6) = 0 (flat space) *)
Theorem synth3_deficit : deficit_angle 6 == 0.
Proof. exact bundle_deficit_flat. Qed.

(** Step3 Phase 19.5: L4 → Einstein *)
(** Concrete: curvature nonneg *)
Theorem synth3_curvature : forall G, 0 <= total_curvature G.
Proof. exact bundle_curvature_nonneg. Qed.

(** Step5: mass gap *)
Theorem synth5_gap : 0 < matrix_mass_gap 1 1 0.
Proof. exact bundle_gap_positive. Qed.

Theorem synth5_gap_value : matrix_mass_gap 1 1 0 == 289 # 384.
Proof. exact bundle_gap_value. Qed.

(** Step5: Weinberg angle *)
Theorem synth5_weinberg : sin2_weinberg r_physical == 3 # 13.
Proof. exact bundle_weinberg. Qed.

Definition synth_cleanup1_count := 6%nat.
