(* ProcessLambShiftConnection.v — Lamb shift as process *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import experimental.LambShiftTower.
Open Scope Q_scope.

Theorem lamb_splitting_process :
  lamb_splitting 1 == -(3 # 8) /\
  lamb_splitting 3 == -(1 # 8) /\
  lamb_splitting 9 == (1 # 40).
Proof.
  split; [|split].
  - exact splitting_at_1.
  - exact splitting_at_3.
  - exact splitting_at_9.
Qed.

Theorem energy_levels_K3 :
  energy_2S 3 == -(3 # 32) /\
  energy_2P 3 == (1 # 32).
Proof.
  split.
  - exact energy_2S_at_3.
  - exact energy_2P_at_3.
Qed.

(** Sign flip at K=9: splitting changes sign *)
(** Physical: process CONVERGES — sign change = approaching limit *)
Lemma sign_flip : lamb_splitting 3 < 0 /\ 0 < lamb_splitting 9.
Proof.
  split.
  - rewrite splitting_at_3. unfold Qlt; simpl; lia.
  - rewrite splitting_at_9. unfold Qlt; simpl; lia.
Qed.

Definition lamb_count := 4%nat.
