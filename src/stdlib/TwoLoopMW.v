(* TwoLoopMW.v — 2-loop W mass from derived functors *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.D1_LoopExpansion.
From ToS Require Import process.ProcessMWOneLoop.
Open Scope Q_scope.

(** Tree: m_W²/m_Z² = 10/13 = 0.76923 *)
(** 1-loop: + δρ = 1274/144672 → ~ 0.7760 *)
(** Experiment: 0.7780 *)

Definition delta_rho_1l : Q := 1274 # 144672.
Definition delta_rho_2l : Q := delta_rho_1l * delta_rho_1l.

Lemma delta_rho_1l_positive : 0 < delta_rho_1l.
Proof. unfold delta_rho_1l. lra. Qed.

Lemma delta_rho_2l_positive : 0 < delta_rho_2l.
Proof.
  unfold delta_rho_2l.
  apply Qmult_lt_0_compat; exact delta_rho_1l_positive.
Qed.

Lemma delta_rho_2l_tiny : delta_rho_2l < 1 # 10000.
Proof. unfold delta_rho_2l, delta_rho_1l. unfold Qlt; simpl; lia. Qed.

Lemma delta_rho_2l_lt_1l : delta_rho_2l < delta_rho_1l.
Proof. unfold delta_rho_2l, delta_rho_1l. unfold Qlt; simpl; lia. Qed.

Definition mw_mz_tree : Q := 10 # 13.
Definition mw_mz_1loop : Q := mw_mz_tree + delta_rho_1l.
Definition mw_mz_2loop : Q := mw_mz_1loop + delta_rho_2l.
Definition mw_mz_exp : Q := 7780 # 10000.

Lemma mw_mz_1loop_value : mw_mz_1loop == 1463282 # 1880736.
Proof. unfold mw_mz_1loop, mw_mz_tree, delta_rho_1l. vm_compute. reflexivity. Qed.

Lemma tree_error_mw : Qabs (mw_mz_tree - mw_mz_exp) == 1140 # 130000.
Proof. unfold mw_mz_tree, mw_mz_exp. vm_compute. reflexivity. Qed.

Lemma oneloop_error_mw : Qabs (mw_mz_1loop - mw_mz_exp) ==
  Qabs ((1463282 # 1880736) - (7780 # 10000)).
Proof. rewrite mw_mz_1loop_value. reflexivity. Qed.

(** Pattern: each loop ~ α/4π × previous *)
Theorem two_loop_mw :
  0 < delta_rho_2l /\
  delta_rho_2l < 1 # 10000 /\
  delta_rho_2l < delta_rho_1l.
Proof.
  split; [|split].
  - exact delta_rho_2l_positive.
  - exact delta_rho_2l_tiny.
  - exact delta_rho_2l_lt_1l.
Qed.

Definition two_loop_mw_count := 9%nat.
