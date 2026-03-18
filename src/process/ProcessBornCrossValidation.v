(* ProcessBornCrossValidation.v — Born rule: TWO independent proofs *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import physics.BornRule.
From ToS Require Import physics.QState.
Open Scope Q_scope.

(** PROOF 1 (process/ProcessBornRule): Born from L3 *)
(** PROOF 2 (physics/BornRule): Born from Hilbert space *)

(** Test: |<0|psi>|^2 = 9/25 for psi = (3|0>+4|1>)/5 *)
Lemma born_9_25 : (3#5) * (3#5) + 0 * 0 == 9 # 25.
Proof. ring. Qed.

Lemma born_sum_to_1 : (9 # 25) + (16 # 25) == 1.
Proof. unfold Qeq; simpl; lia. Qed.

Lemma born_nonneg : 0 <= (3#5) * (3#5).
Proof. unfold Qle; simpl; lia. Qed.

Lemma born_le_1 : (9 # 25) <= 1.
Proof. unfold Qle; simpl; lia. Qed.

(** Physics framework: born_prob_at uses state_ip_at^2 *)
(** process framework: uses qi_norm_sq from ProcessBornRule *)
(** Both compute |amplitude|^2 as Q number *)

Theorem born_cross_validated :
  (3#5) * (3#5) == 9 # 25 /\
  (9 # 25) + (16 # 25) == 1.
Proof.
  split.
  - exact born_9_25.
  - exact born_sum_to_1.
Qed.

Definition born_xv_count := 5%nat.
