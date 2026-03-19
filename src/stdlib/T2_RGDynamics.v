From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore. From ToS Require Import process.ProcessRGFlow.
Open Scope Q_scope.
Definition rg_orbit (u0 : Q) : RealProcess := fun K => rg_iterate u0 K.
Lemma orbit_at_0 : rg_orbit 1 0%nat == 1. Proof. reflexivity. Qed.
Lemma orbit_at_1 : rg_orbit 1 1%nat == 7 # 4. Proof. exact rg_from_1_step1. Qed.
Lemma uv_fixed : rg_step 0 == 0. Proof. exact rg_step_zero. Qed.
Lemma ir_fixed : rg_step 4 == 4. Proof. exact rg_fixed_point_4. Qed.
Lemma orbit_increases : rg_orbit 1 0%nat < rg_orbit 1 1%nat.
Proof. rewrite orbit_at_0, orbit_at_1. lra. Qed.
Theorem rg_dynamics : rg_step 0 == 0 /\ rg_step 4 == 4 /\ rg_orbit 1 0%nat < rg_orbit 1 1%nat.
Proof. split; [|split]; [exact uv_fixed|exact ir_fixed|exact orbit_increases]. Qed.
Definition t2_rg_count := 6%nat.
