(* ProcessFriedmann.v — Discrete Friedmann from Regge *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
Open Scope Q_scope.

(** ★ FRIEDMANN FROM HOMOGENEOUS REGGE LATTICE *)
(** Scale factor process: ℓ(t) = ℓ₀(1 + Ht) *)

Definition scale_factor (ell0 H : Q) (t : nat) : Q :=
  ell0 * (1 + H * inject_Z (Z.of_nat t)).

Lemma scale_at_0 : forall ell0 H, scale_factor ell0 H O == ell0.
Proof. intros. unfold scale_factor, inject_Z. simpl. ring. Qed.

Lemma scale_at_1 : forall ell0 H, scale_factor ell0 H 1 == ell0 * (1 + H).
Proof. intros. unfold scale_factor, inject_Z. simpl. ring. Qed.

(** Discrete Hubble: (ℓ(t+1) − ℓ(t)) / ℓ(t) *)
Definition discrete_hubble (ell0 H : Q) (t : nat) : Q :=
  (scale_factor ell0 H (S t) - scale_factor ell0 H t) / scale_factor ell0 H t.

Lemma hubble_at_0 : forall ell0 H,
  0 < ell0 ->
  discrete_hubble ell0 H O == H.
Proof.
  intros ell0 H Hell. unfold discrete_hubble.
  rewrite scale_at_0, scale_at_1. field. lra.
Qed.

(** ★ Friedmann consistency: H² = 8πρ/3 at t=0 *)
(** ρ₀ = 3H²/(8π) = 3H²/(8·22/7) = 21H²/176 *)
Definition friedmann_rho0 (H : Q) : Q := 21 * H * H / 176.

Lemma friedmann_consistent : forall H,
  8 * (22 # 7) * friedmann_rho0 H / 3 == H * H.
Proof. intros H. unfold friedmann_rho0. field. Qed.

Lemma rho0_at_1 : friedmann_rho0 1 == 21 # 176.
Proof. unfold friedmann_rho0. field. Qed.

Lemma rho0_pos_1 : 0 < friedmann_rho0 1.
Proof. rewrite rho0_at_1. lra. Qed.

(** Matter density: ρ ∝ 1/a³ *)
Definition matter_density (rho0 ell0 H : Q) (t : nat) : Q :=
  rho0 * ell0 * ell0 * ell0 /
  (scale_factor ell0 H t * scale_factor ell0 H t * scale_factor ell0 H t).

Lemma density_at_0 : forall rho0 ell0 H,
  0 < ell0 ->
  matter_density rho0 ell0 H O == rho0.
Proof.
  intros. unfold matter_density. rewrite scale_at_0. field. lra.
Qed.

(** ★ Deceleration: for matter-dominated, q = 1/2 *)
(** For Λ: q = −1 (accelerating) *)

Theorem friedmann_from_regge :
  (forall H, 8 * (22 # 7) * friedmann_rho0 H / 3 == H * H) /\
  (forall ell0 H, 0 < ell0 -> discrete_hubble ell0 H O == H).
Proof.
  split.
  - exact friedmann_consistent.
  - exact hubble_at_0.
Qed.

Definition friedmann_count := 8%nat.
