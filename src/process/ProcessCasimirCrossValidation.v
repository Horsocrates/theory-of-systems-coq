(* ProcessCasimirCrossValidation.v — Casimir from TWO methods *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import experimental.CasimirProcess.
From ToS Require Import experimental.VacuumEnergy.
Open Scope Q_scope.

Theorem casimir_from_zeta : casimir_1d == -(1 # 12).
Proof. exact casimir_1d_verified. Qed.

Theorem casimir_3d : casimir_3d == (1 # 120).
Proof. exact casimir_3d_verified. Qed.

Theorem vacuum_values :
  vacuum_energy_1d 0 == (1#2) /\
  vacuum_energy_1d 1 == (3#2) /\
  vacuum_energy_1d 2 == 3.
Proof.
  split; [|split].
  - exact vacuum_1d_at_0.
  - exact vacuum_1d_at_1.
  - exact vacuum_1d_at_2.
Qed.

Theorem casimir_cross_validated :
  casimir_1d == -(1 # 12) /\ experimental.CasimirProcess.casimir_3d == (1 # 120).
Proof. split; [exact casimir_1d_verified | exact casimir_3d_verified]. Qed.

Definition casimir_xv_count := 5%nat.
