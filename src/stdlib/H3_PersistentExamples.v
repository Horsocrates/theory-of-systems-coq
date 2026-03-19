From Stdlib Require Import QArith QArith_base Lia ZArith. From Stdlib Require Import Lqa.
From ToS Require Import stdlib.H3_PersistentHomology. From ToS Require Import stdlib.ChainComplex.
Open Scope Q_scope.
Lemma S2_topology : filtration_euler 12 30 20 = 2%Z /\ (persistence bd_S2_0 = 1000)%nat.
Proof. split; reflexivity. Qed.
Lemma torus_topology : filtration_euler 7 21 14 = 0%Z.
Proof. reflexivity. Qed.
Lemma triangle_d2_check : mat_mul_entry triangle_d1 triangle_d2 0 0 == 0.
Proof. exact triangle_d2_zero_00. Qed.
Theorem persistent_examples :
  filtration_euler 12 30 20 = 2%Z /\ filtration_euler 7 21 14 = 0%Z.
Proof. split; reflexivity. Qed.
Definition h3_ex_count := 4%nat.
