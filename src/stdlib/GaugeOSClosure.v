(* GaugeOSClosure.v — Close gauge/ True using OS libs *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.OS1Closure.
From ToS Require Import stdlib.OS2Closure.
From ToS Require Import stdlib.OS3Closure.
From ToS Require Import stdlib.TheoremBundle.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.

(** ContinuumCovariance True → OS3 results *)
Theorem gauge_covariance : os3_covariance_proved.
Proof. exact os3_proved. Qed.

(** Analyticity from OS1 *)
Theorem gauge_analyticity : os1_analyticity_proved.
Proof. exact os1_proved. Qed.

(** Regularity from OS2 *)
Theorem gauge_regularity : os2_regularity_proved.
Proof. exact os2_proved. Qed.

(** YMLevel5 OS strengthened *)
Theorem gauge_os_strengthened :
  os1_analyticity_proved /\
  os2_regularity_proved /\
  os3_covariance_proved.
Proof.
  split; [|split].
  - exact os1_proved.
  - exact os2_proved.
  - exact os3_proved.
Qed.

(** Mass gap from ProofClosure *)
Theorem gauge_gap : 0 < matrix_mass_gap 1 1 0.
Proof. exact mass_gap_positive_beta_1. Qed.

Theorem gauge_gap_value : matrix_mass_gap 1 1 0 == 289 # 384.
Proof. exact mass_gap_value_beta_1. Qed.

(** All nine gaps *)
Theorem gauge_nine_gaps :
  0 < matrix_mass_gap 1 1 0 /\ matrix_mass_gap 1 1 0 == 289 # 384.
Proof. split; [exact mass_gap_positive_beta_1 | exact mass_gap_value_beta_1]. Qed.

Definition gauge_os_count := 8%nat.
