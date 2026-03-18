(* ProcessSynthesisCleanup3.v — Close True in Lorentzian/Step8/Step11/PathB *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.TheoremBundle.
From ToS Require Import stdlib.OS1Closure.
From ToS Require Import stdlib.OS2Closure.
From ToS Require Import stdlib.OS3Closure.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.
From ToS Require Import process.ProcessPhysicalSigma.
From ToS Require Import process.ProcessWeinbergAngle.
From ToS Require Import process.ProcessSpacetime.
From ToS Require Import process.ProcessRegge.

(** LorentzianSynthesis: spacetime from P4 *)
Theorem synth_spacetime :
  space_reversible empty_stlattice /\ time_irreversible empty_stlattice.
Proof.
  split; [exact bundle_space_reversible | exact bundle_time_irreversible].
Qed.

(** Step8Synthesis: mass gap resolved *)
Theorem synth_step8_gap : matrix_mass_gap 1 1 0 == 289 # 384.
Proof. exact bundle_gap_value. Qed.

(** Step11Synthesis: experimental accuracy *)
(** Weinberg angle *)
Theorem synth_step11_weinberg : sin2_weinberg r_physical == 3 # 13.
Proof. exact bundle_weinberg. Qed.

(** String tension ratio *)
Theorem synth_step11_sigma : I1_partial 1 1 / I0_partial 1 1 == 9 # 20.
Proof. exact bundle_sigma. Qed.

(** PathBSynthesis: deficit angle flat *)
Theorem synth_pathb_deficit : deficit_angle 6 == 0.
Proof. exact bundle_deficit_flat. Qed.

(** OS axioms now proved *)
Theorem synth_os_complete :
  os1_analyticity_proved /\ os2_regularity_proved /\ os3_covariance_proved.
Proof.
  split; [|split].
  - exact os1_proved.
  - exact os2_proved.
  - exact os3_proved.
Qed.

Definition synth_cleanup3_count := 7%nat.
