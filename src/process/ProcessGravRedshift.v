(* ProcessGravRedshift.v — Gravitational redshift and time dilation *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.
Open Scope Q_scope.

(** ★ GRAVITATIONAL TIME DILATION *)
(** f = dτ²/dt² = 1 − 2M/r = schwarzschild_factor *)
(** Clock at r runs at rate √f relative to infinity *)

Definition time_dilation_factor (M ell : Q) (k : nat) : Q :=
  schwarzschild_factor M ell k.

(** At horizon (k=9, r=10ℓ, 2M=10): f = 0 → time STOPS *)
Lemma dilation_at_horizon : time_dilation_factor 5 1 9 == 0.
Proof. unfold time_dilation_factor, schwarzschild_factor, shell_radius. simpl. field. Qed.

(** At r=15ℓ: f = 1 − 10/15 = 1/3 *)
Lemma dilation_at_15 : time_dilation_factor 5 1 14 == 1 # 3.
Proof. unfold time_dilation_factor, schwarzschild_factor, shell_radius. simpl. field. Qed.

(** At r=20ℓ: f = 1 − 10/20 = 1/2 *)
Lemma dilation_at_20 : time_dilation_factor 5 1 19 == 1 # 2.
Proof. unfold time_dilation_factor, schwarzschild_factor, shell_radius. simpl. field. Qed.

(** At r=100ℓ: f = 1 − 10/100 = 9/10 *)
Lemma dilation_at_100 : time_dilation_factor 5 1 99 == 9 # 10.
Proof. unfold time_dilation_factor, schwarzschild_factor, shell_radius. simpl. field. Qed.

(** Dilation increases with distance (less gravity → closer to 1) *)
Lemma dilation_increases :
  time_dilation_factor 5 1 14 < time_dilation_factor 5 1 19.
Proof. rewrite dilation_at_15, dilation_at_20. lra. Qed.

Lemma dilation_increases_2 :
  time_dilation_factor 5 1 19 < time_dilation_factor 5 1 99.
Proof. rewrite dilation_at_20, dilation_at_100. lra. Qed.

(** f < 1 outside horizon (gravity slows time) *)
Lemma dilation_lt_1 : time_dilation_factor 5 1 14 < 1.
Proof. rewrite dilation_at_15. lra. Qed.

(** f > 0 outside horizon *)
Lemma dilation_pos : 0 < time_dilation_factor 5 1 14.
Proof. rewrite dilation_at_15. lra. Qed.

(** ★ EXPERIMENTAL: GPS uses f = 1 − 2GM/(c²r) — SAME formula *)
(** Our f = 1 − 2M/r with r = ℓ(k+1) — IDENTICAL in Planck units *)

(** Full dilation profile *)
Theorem dilation_profile :
  time_dilation_factor 5 1 9 == 0 /\
  time_dilation_factor 5 1 14 == 1 # 3 /\
  time_dilation_factor 5 1 19 == 1 # 2 /\
  time_dilation_factor 5 1 99 == 9 # 10.
Proof.
  split; [|split; [|split]].
  - exact dilation_at_horizon.
  - exact dilation_at_15.
  - exact dilation_at_20.
  - exact dilation_at_100.
Qed.

Definition grav_redshift_count := 10%nat.
