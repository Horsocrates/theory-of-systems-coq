(* ProcessGeodesic.v — Geodesics on Regge lattice *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.
Open Scope Q_scope.

(** ★ GEODESIC = locally straightest path on Regge lattice *)

(** Effective potential: V_eff(k) *)
Definition effective_potential (M ell L : Q) (k : nat) : Q :=
  let r := shell_radius ell k in
  let f := schwarzschild_factor M ell k in
  L * L / (2 * r * r) + f / 2.

(** ISCO: r = 6M → k = 6M/ℓ − 1 *)
(** For M=5, ℓ=1: r = 30 → k = 29 *)
Lemma isco_radius : shell_radius 1 29 == 30.
Proof. unfold shell_radius. simpl. ring. Qed.

Lemma isco_factor : schwarzschild_factor 5 1 29 == 2 # 3.
Proof. unfold schwarzschild_factor, shell_radius. simpl. field. Qed.

(** ★ RADIAL FREE FALL from infinity *)
(** E = 1, v² = 1 − f = 2M/r *)
Definition freefall_velocity_sq (M ell : Q) (k : nat) : Q :=
  1 - schwarzschild_factor M ell k.

Lemma freefall_at_15 : freefall_velocity_sq 5 1 14 == 2 # 3.
Proof. unfold freefall_velocity_sq, schwarzschild_factor, shell_radius. simpl. field. Qed.

Lemma freefall_at_20 : freefall_velocity_sq 5 1 19 == 1 # 2.
Proof. unfold freefall_velocity_sq, schwarzschild_factor, shell_radius. simpl. field. Qed.

Lemma freefall_at_horizon : freefall_velocity_sq 5 1 9 == 1.
Proof. unfold freefall_velocity_sq, schwarzschild_factor, shell_radius. simpl. field. Qed.

(** v² increases toward horizon *)
Lemma freefall_increases :
  freefall_velocity_sq 5 1 19 < freefall_velocity_sq 5 1 14.
Proof. rewrite freefall_at_20, freefall_at_15. lra. Qed.

(** v² = 1 at horizon → reaches speed of light *)
Lemma freefall_lightspeed : freefall_velocity_sq 5 1 9 == 1.
Proof. exact freefall_at_horizon. Qed.

(** v² ≥ 0 (physical) *)
Lemma freefall_nonneg : 0 <= freefall_velocity_sq 5 1 14.
Proof. rewrite freefall_at_15. lra. Qed.

(** ★ ORBITAL PERIOD: T² = (4π²/M)·r³ (Kepler) *)
Definition kepler_T_sq_over_r3 (M : Q) : Q := 4 * (22#7) * (22#7) / M.

Lemma kepler_ratio : kepler_T_sq_over_r3 5 == 1936 # 245.
Proof. unfold kepler_T_sq_over_r3. field. Qed.

(** ★ Escape velocity: v² = 2M/r = 2f_complement *)
Lemma escape_at_100 : freefall_velocity_sq 5 1 99 == 1 # 10.
Proof. unfold freefall_velocity_sq, schwarzschild_factor, shell_radius. simpl. field. Qed.

Theorem geodesic_foundation :
  freefall_velocity_sq 5 1 14 == 2 # 3 /\
  freefall_velocity_sq 5 1 9 == 1 /\
  schwarzschild_factor 5 1 29 == 2 # 3.
Proof.
  split; [|split].
  - exact freefall_at_15.
  - exact freefall_at_horizon.
  - exact isco_factor.
Qed.

Definition geodesic_count := 12%nat.
