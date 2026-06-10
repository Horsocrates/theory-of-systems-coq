(* ================================================================== *)
(*  LightGravityConnection.v                                           *)
(*  Light and gravity as edge vs vertex excitations — June 2026        *)
(*  honesty rollback: 3 True-stubs removed (transverse_is_light,       *)
(*  longitudinal_is_metric — need a mode-decomposition layer;           *)
(*  kaluza_klein_hint — needs a 5th dimension; all RETIRED).  Real      *)
(*  replacement: same_speed_different_spin (the file's honest          *)
(*  dichotomy on its own data).                                         *)
(*  STATUS: 8 Qed, 0 Admitted, 0 axioms                                *)
(*  Author: Horsocrates | Date: April 2026 (rollback: June 2026)       *)
(* ================================================================== *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                        *)
(* ------------------------------------------------------------------ *)

(** In 3+1D, transverse edge oscillations have 2 independent directions
    perpendicular to propagation *)
Definition n_transverse_3d : nat := 2%nat.

(** Light (photon) is spin-1: one unit of angular momentum *)
Definition light_spin : nat := 1%nat.

(** Gravity (graviton) is spin-2: tensor excitation of the metric *)
Definition gravity_spin : nat := 2%nat.

(** Edge wave speed in the low-k limit *)
Definition edge_wave_speed_low_k : Q := 1.

(** Causal limit *)
Definition causal_limit : Q := 1.

(** Graviton speed = causal limit (both are massless edge excitations) *)
Definition graviton_speed : Q := 1.

(* ------------------------------------------------------------------ *)
(*  Theorems                                                           *)
(* ------------------------------------------------------------------ *)

(** Two polarizations in 3D *)
Theorem two_polarizations : n_transverse_3d = 2%nat.
Proof. reflexivity. Qed.

(** Light is spin-1 *)
Theorem light_spin_one : light_spin = 1%nat.
Proof. reflexivity. Qed.

(** Gravity is spin-2 *)
Theorem gravity_spin_two : gravity_spin = 2%nat.
Proof. reflexivity. Qed.

(** Both light and gravity travel at causal limit *)
Theorem both_massless : edge_wave_speed_low_k == causal_limit.
Proof. vm_compute. reflexivity. Qed.

(** Graviton also at causal limit *)
Theorem graviton_at_c : graviton_speed == causal_limit.
Proof. vm_compute. reflexivity. Qed.

(** Spin difference *)
Theorem spin_difference : (gravity_spin - light_spin = 1)%nat.
Proof. reflexivity. Qed.

(* June 2026 honesty rollback: three True-stubs REMOVED (transverse_is_light,
   longitudinal_is_metric, kaluza_klein_hint).  The transverse/longitudinal
   identifications need a mode-decomposition layer absent here, and Kaluza-Klein
   needs a 5th dimension — those claims are RETIRED.  The real available content:
   the light/gravity DICHOTOMY on this file's own data — same causal speed,
   DIFFERENT spin. *)

(** ★ Same speed, different spin: the two massless excitations coincide in speed
    (both at the causal limit) and differ in spin — the file's honest dichotomy. *)
Theorem same_speed_different_spin :
  graviton_speed == edge_wave_speed_low_k /\ light_spin <> gravity_spin.
Proof.
  split.
  - vm_compute. reflexivity.
  - unfold light_spin, gravity_spin. lia.
Qed.

(** === SYNTHESIS === *)
Theorem light_gravity_synthesis :
  n_transverse_3d = 2%nat /\
  light_spin = 1%nat /\
  gravity_spin = 2%nat /\
  edge_wave_speed_low_k == causal_limit /\
  light_spin <> gravity_spin.
Proof.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { vm_compute. reflexivity. }
  unfold light_spin, gravity_spin. lia.
Qed.
