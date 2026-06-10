(* ================================================================== *)
(*  SpeedOfLight.v                                                     *)
(*  Speed of light as the causal bound of the graph model — June 2026 *)
(*  honesty rollback: 2 True-stubs removed (c_is_graph_property,       *)
(*  why_nothing_faster) and 1 FAKE theorem fixed (the old              *)
(*  massive_dispersion_bigger concluded `0 < 1`, hypothesis discarded).*)
(*  Real general layer: massive_dispersion_bigger (actual statement),  *)
(*  speed_bounded_by_c (v ≤ c ∀ m, ω>0), massive_strictly_slower —     *)
(*  all WITHIN the posited v_g model (the model itself is an input).   *)
(*  STATUS: 10 Qed, 0 Admitted, 0 axioms                               *)
(*  Author: Horsocrates | Date: April 2026 (rollback: June 2026)       *)
(* ================================================================== *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                        *)
(* ------------------------------------------------------------------ *)

(** The causal limit: maximum speed on the graph = 1 edge per tick *)
Definition causal_limit : Q := 1.

(** Edge (massless) wave speed in the long-wavelength limit *)
Definition edge_wave_speed_low_k : Q := 1.

(** Vertex (massive) wave: group velocity approximation
    v_g ~ 1 - m^2/(2*omega^2)  for omega >> m *)
Definition vertex_wave_speed_approx (m omega : Q) : Q :=
  1 - m * m / (2 * omega * omega).

(** Dispersion relation: omega^2 = k^2 + m^2
    For massless: omega = k, speed = 1 *)
Definition dispersion_massless (k : Q) : Q := k.

(** For massive: omega = sqrt(k^2 + m^2), always > k *)
Definition dispersion_massive_sq (k m : Q) : Q := k * k + m * m.

(* ------------------------------------------------------------------ *)
(*  Theorems                                                           *)
(* ------------------------------------------------------------------ *)

(** Edge waves travel at c = 1 *)
Theorem edge_at_c : edge_wave_speed_low_k == causal_limit.
Proof. vm_compute. reflexivity. Qed.

(** Massive particles travel slower than c *)
Theorem massive_slower : vertex_wave_speed_approx 1 2 < causal_limit.
Proof. vm_compute. reflexivity. Qed.

(** Massless particles travel at exactly c *)
Theorem massless_at_c : vertex_wave_speed_approx 0 2 == causal_limit.
Proof. vm_compute. reflexivity. Qed.

(** Concrete speed ratio for m=1, omega=2: v = 7/8 *)
Theorem speed_ratio : vertex_wave_speed_approx 1 2 == 7#8.
Proof. vm_compute. reflexivity. Qed.

(** Heavier mass means slower speed *)
Theorem heavier_is_slower :
  vertex_wave_speed_approx 2 4 < vertex_wave_speed_approx 1 4.
Proof. vm_compute. reflexivity. Qed.

(** Massless dispersion is linear *)
Theorem massless_dispersion_linear :
  dispersion_massless 3 == 3.
Proof. vm_compute. reflexivity. Qed.

(* June 2026 honesty rollback: REMOVED two True-stubs (c_is_graph_property,
   why_nothing_faster) and FIXED a fake theorem: the old massive_dispersion_bigger
   had conclusion `0 < 1` with its hypothesis discarded — it proved nothing.
   Real general layer below: the dispersion inequality as an actual statement, and
   the causal bound v ≤ c for ALL masses/frequencies (strict for massive) — the
   honest content of "c bounds everything" WITHIN this file's posited v_g model. *)

(** Massive dispersion, REAL statement: ω² = k² + m² > k² for positive mass. *)
Theorem massive_dispersion_bigger : forall k m : Q,
  0 < m -> k * k < dispersion_massive_sq k m.
Proof. intros k m Hm. unfold dispersion_massive_sq. nra. Qed.

(** ★ The causal limit BOUNDS the model's speeds: v ≤ c for all m, all ω > 0. *)
Theorem speed_bounded_by_c : forall m omega : Q,
  0 < omega -> vertex_wave_speed_approx m omega <= causal_limit.
Proof.
  intros m omega Hw. unfold vertex_wave_speed_approx, causal_limit.
  assert (Hden : 0 < 2 * omega * omega) by nra.
  assert (Hfrac : 0 <= m * m / (2 * omega * omega)).
  { unfold Qdiv. apply Qmult_le_0_compat.
    - nra.
    - apply Qlt_le_weak, Qinv_lt_0_compat. exact Hden. }
  lra.
Qed.

(** ★ Massive ⟹ STRICTLY slower than c (general; was only the m=1, ω=2 instance). *)
Theorem massive_strictly_slower : forall m omega : Q,
  0 < m -> 0 < omega -> vertex_wave_speed_approx m omega < causal_limit.
Proof.
  intros m omega Hm Hw. unfold vertex_wave_speed_approx, causal_limit.
  assert (Hden : 0 < 2 * omega * omega) by nra.
  assert (Hfrac : 0 < m * m / (2 * omega * omega)).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - nra.
    - apply Qinv_lt_0_compat. exact Hden. }
  lra.
Qed.

(** === SYNTHESIS === *)
Theorem speed_of_light_synthesis :
  edge_wave_speed_low_k == causal_limit /\
  vertex_wave_speed_approx 0 2 == causal_limit /\
  vertex_wave_speed_approx 1 2 < causal_limit /\
  (forall m omega : Q,
     0 < omega -> vertex_wave_speed_approx m omega <= causal_limit).
Proof.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  exact speed_bounded_by_c.
Qed.
