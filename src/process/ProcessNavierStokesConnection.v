(* ProcessNavierStokesConnection.v — NS as P4 process *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import navier_stokes.EnergyEstimate.
Open Scope Q_scope.

(** NS at modal truncation K: finite ODE over Q *)

Theorem ns_energy_monotone : forall K u,
  energy_decreasing K u ->
  forall m n, (m <= n)%nat -> energy_at K u n <= energy_at K u m.
Proof. exact energy_monotone. Qed.

Theorem ns_energy_bounded : forall K u,
  energy_decreasing K u ->
  forall n, energy_at K u n <= energy_at K u 0.
Proof. exact energy_bounded_by_initial. Qed.

Theorem ns_connection :
  (forall K u, energy_decreasing K u ->
    forall m n, (m <= n)%nat -> energy_at K u n <= energy_at K u m) /\
  (forall K u, energy_decreasing K u ->
    forall n, energy_at K u n <= energy_at K u 0).
Proof. split; [exact energy_monotone | exact energy_bounded_by_initial]. Qed.

Definition ns_count := 3%nat.
