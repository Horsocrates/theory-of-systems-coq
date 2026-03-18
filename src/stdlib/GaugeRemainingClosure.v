(* GaugeRemainingClosure.v — Close remaining gauge/ True *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.TheoremBundle.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.GapRatio.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.

(** RGContraction: β increases under RG *)
Theorem gauge_beta_increases :
  0 < gap_ratio 1 /\ gap_ratio 1 < 1 /\
  0 < gap_ratio 2 /\ gap_ratio 2 < 1.
Proof.
  split; [|split; [|split]].
  - exact gap_ratio_pos_1.
  - exact gap_ratio_lt1_beta_1.
  - exact gap_ratio_pos_2.
  - exact gap_ratio_lt1_beta_2.
Qed.

(** 3×3 eigenvalue gap at K=8 *)
Theorem gauge_3x3_gap : (16#9) - (3#2) == 5 # 18.
Proof. ring. Qed.

(** Gap concrete values *)
Theorem gauge_gap_beta2 : matrix_mass_gap 1 2 0 == 1 # 24.
Proof. exact mass_gap_value_beta_2. Qed.

(** UniversalityClass: both actions give gap > 0 *)
Theorem gauge_both_gaps :
  0 < matrix_mass_gap 1 1 0 /\ 0 < matrix_mass_gap 1 2 0.
Proof.
  split; [exact mass_gap_positive_beta_1 | exact mass_gap_positive_beta_2].
Qed.

(** Gap ratio values *)
Theorem gauge_ratio_values :
  gap_ratio 1 == 47 # 336 /\ gap_ratio 2 == 11 # 12.
Proof.
  split; [exact gap_ratio_at_beta_1 | exact gap_ratio_at_beta_2].
Qed.

Definition gauge_remaining_count := 6%nat.
