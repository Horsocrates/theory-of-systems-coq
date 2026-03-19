(* LoopUnification.v — 1-loop as derived functor instance *)
From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import stdlib.D1_LoopExpansion.
From ToS Require Import process.ProcessWMassRatio.
From ToS Require Import process.ProcessMWOneLoop.
Open Scope Q_scope.
Theorem mw_oneloop_improves : mW_sq_over_mZ_sq < mW_mZ_corrected.
Proof. exact correction_improves. Qed.
Theorem loop1_matches_derived : loop_correction 1 (1#10) == 1 # 10.
Proof. apply loop_1_loop. Qed.
Theorem loop_derived_bridge :
  loop_correction 0 (1#10) == 1 /\ loop_correction 1 (1#10) == 1 # 10 /\ mW_sq_over_mZ_sq < mW_mZ_corrected.
Proof. split; [|split]; [apply loop_tree_level | apply loop_1_loop | exact mw_oneloop_improves]. Qed.
Definition loop_unification_count := 3%nat.
