(* ProcessCoulombConnection.v — Hydrogen spectrum from lattice *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import experimental.CoulombFull3D.
From ToS Require Import experimental.LambShiftTower.
Open Scope Q_scope.

Theorem hydrogen_spectrum_K3 :
  scaled_energy_3d 3 0 0 == -(7 # 32) /\
  scaled_energy_3d 3 0 1 == (1 # 32) /\
  scaled_energy_3d 3 1 0 == -(3 # 32).
Proof.
  split; [|split].
  - exact energy_3d_3_0_0.
  - exact energy_3d_3_0_1.
  - exact energy_3d_3_1_0.
Qed.

Lemma p3_vs_coulomb_n2 : (1#3) * (1#3) == 1 # 9.
Proof. ring. Qed.

Lemma p3_vs_coulomb_n4 : ~((1#3) * (1#3) * (1#3) == 1 # 16).
Proof. unfold Qeq; simpl; lia. Qed.

Theorem centrifugal_values :
  centrifugal_scaled 3 0 1 == (1 # 4) /\
  centrifugal_scaled 3 0 2 == (3 # 4).
Proof.
  split.
  - exact centrifugal_at_l1.
  - exact centrifugal_at_l2.
Qed.

Definition coulomb_count := 5%nat.
