(** * QuantumBounce.v — Bounce Cosmology as ToS System
    Elements: scale factor, bounce point, Hubble parameter
    Roles:    bounce process, temperature, energy density
    Rules:    a_min > 0 always (no singularity), bounce dynamics
    Status:   Dir 2, File 2 of Quantum Cosmology
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

Open Scope Q_scope.

(* ========================================================================= *)
(*              BOUNCE COSMOLOGY DEFINITIONS                                 *)
(* ========================================================================= *)

(** Bounce process: near the bounce, a(t) ~ a_min * (1 + H^2 * t^2 / 2)
    This is the leading order expansion around the bounce point t=0. *)
Definition bounce_process (a_min H t : Q) : Q :=
  a_min * (1 + H * H * t * t / 2).

(** Maximum temperature at the bounce: T_max ~ 1/a_min
    (in natural units where T ~ 1/a) *)
Definition max_temperature (a_min : Q) : Q := 1 / a_min.

(** Maximum energy density at bounce: rho_max = 3H^2 / (8*pi*a_min^3)
    Using pi ~ 22/7 *)
Definition max_density (H a_min : Q) : Q :=
  3 * H * H / (8 * (22 # 7) * a_min * a_min * a_min).

(* ========================================================================= *)
(*              NO SINGULARITY                                               *)
(* ========================================================================= *)

(** The bounce has no singularity: a(t) >= a_min for all t *)
Lemma bounce_no_singularity : forall a_min H t,
  0 < a_min -> 0 <= H ->
  a_min <= bounce_process a_min H t.
Proof.
  intros a_min H t Ha HH.
  unfold bounce_process.
  assert (Ht2 : 0 <= H * H * t * t).
  { assert (Heq : H * H * t * t == (H * t) * (H * t)) by ring.
    rewrite Heq.
    destruct (Qlt_le_dec 0 (H * t)).
    - apply Qmult_le_0_compat; lra.
    - assert (0 <= -(H * t)) by lra.
      assert ((H * t) * (H * t) == (-(H * t)) * (-(H * t))) by ring.
      rewrite H1. apply Qmult_le_0_compat; lra. }
  assert (Hdiv : 0 <= H * H * t * t / 2).
  { unfold Qdiv. apply Qmult_le_0_compat; [assumption | unfold Qle; simpl; lia]. }
  assert (H1le : 1 <= 1 + H * H * t * t / 2).
  { assert (Heq : 1 == 1 + 0) by ring. rewrite Heq.
    apply Qplus_le_compat; [lra | assumption]. }
  assert (Hmul : a_min * 1 <= a_min * (1 + H * H * t * t / 2)).
  { assert (0 <= a_min * (H * H * t * t / 2)).
    { apply Qmult_le_0_compat; lra. }
    assert (a_min * (1 + H * H * t * t / 2) == a_min * 1 + a_min * (H * H * t * t / 2)) by ring.
    lra. }
  lra.
Qed.

(** At the bounce (t=0), a = a_min *)
Lemma bounce_at_origin : forall a_min H,
  bounce_process a_min H 0 == a_min.
Proof.
  intros a_min H. unfold bounce_process. field.
Qed.

(** Bounce is symmetric: a(-t) = a(t) *)
Lemma bounce_symmetric : forall a_min H t,
  bounce_process a_min H (- t) == bounce_process a_min H t.
Proof.
  intros a_min H t. unfold bounce_process. field.
Qed.

(* ========================================================================= *)
(*              TEMPERATURE AND DENSITY                                      *)
(* ========================================================================= *)

(** Temperature is positive for positive a_min *)
Lemma temperature_positive : forall a_min,
  0 < a_min -> 0 < max_temperature a_min.
Proof.
  intros a_min Ha. unfold max_temperature.
  assert (Hne : ~(a_min == 0)).
  { intro Heq. unfold Qeq, Qlt in *. simpl in *. lia. }
  assert (Hinv : 0 < / a_min).
  { apply Qinv_lt_0_compat. assumption. }
  unfold Qdiv. lra.
Qed.

(** Temperature decreases: concrete witness *)
Lemma temperature_decreasing_concrete :
  max_temperature 2 < max_temperature 1.
Proof.
  unfold max_temperature. unfold Qlt; simpl; lia.
Qed.

(** Temperature decreases: a1 < a2 → T(a2) < T(a1) *)
Lemma temperature_decreasing : forall a1 a2,
  0 < a1 -> a1 < a2 ->
  max_temperature a2 < max_temperature a1.
Proof.
  intros a1 a2 Ha1 Ha2.
  unfold max_temperature.
  assert (Ha2pos : 0 < a2) by lra.
  assert (Hne1 : ~(a1 == 0)) by (intro H; unfold Qeq, Qlt in *; simpl in *; lia).
  assert (Hne2 : ~(a2 == 0)) by (intro H; unfold Qeq, Qlt in *; simpl in *; lia).
  assert (Hinv1 : 0 < / a1) by (apply Qinv_lt_0_compat; assumption).
  assert (Hinv2 : 0 < / a2) by (apply Qinv_lt_0_compat; assumption).
  (* Multiply both sides by a1*a2 > 0 *)
  (* 1/a2 < 1/a1 ↔ a1 < a2 (when both positive) *)
  assert (Hmul : a1 * a2 * (1 / a2) == a1).
  { field. assumption. }
  assert (Hmul2 : a1 * a2 * (1 / a1) == a2).
  { field. assumption. }
  assert (Hprod : 0 < a1 * a2).
  { apply Qmult_lt_0_compat; assumption. }
  destruct (Qlt_le_dec (1 / a2) (1 / a1)) as [Hlt|Hle].
  - exact Hlt.
  - exfalso.
    assert (H0 : 0 <= a1 * a2 * (1/a2 - 1/a1)).
    { apply Qmult_le_0_compat; lra. }
    assert (Heq : a1 * a2 * (1/a2 - 1/a1) == a1 - a2).
    { field. split; assumption. }
    lra.
Qed.

(** Density is positive *)
Lemma density_positive : forall H a_min,
  0 < H -> 0 < a_min ->
  0 < max_density H a_min.
Proof.
  intros H a_min HH Ha.
  unfold max_density, Qdiv.
  assert (H3 : 0 < 3 * H * H).
  { apply Qmult_lt_0_compat; [lra|assumption]. }
  assert (Hd : 0 < 8 * (22 # 7) * a_min * a_min * a_min).
  { apply Qmult_lt_0_compat; [|assumption].
    apply Qmult_lt_0_compat; [|assumption].
    apply Qmult_lt_0_compat; [lra|assumption]. }
  assert (Hinv : 0 < / (8 * (22 # 7) * a_min * a_min * a_min)).
  { apply Qinv_lt_0_compat. assumption. }
  apply Qmult_lt_0_compat; assumption.
Qed.

(** Concrete: a_min=1, H=1 gives rho = 3/(8*22/7) = 21/176 *)
Lemma density_concrete : max_density 1 1 == 21 # 176.
Proof.
  unfold max_density. vm_compute. reflexivity.
Qed.

(** Concrete: a_min=1/2, T_max = 2 *)
Lemma temperature_concrete : max_temperature (1#2) == 2.
Proof.
  unfold max_temperature. vm_compute. reflexivity.
Qed.

(** Bounce cosmology summary: no singularity + finite temperature *)
Theorem bounce_cosmology_safe : forall a_min H,
  0 < a_min -> 0 < H ->
  a_min <= bounce_process a_min H 0 /\
  0 < max_temperature a_min /\
  0 < max_density H a_min.
Proof.
  intros a_min H Ha HH.
  repeat split.
  - rewrite bounce_at_origin. lra.
  - apply temperature_positive. assumption.
  - apply density_positive; assumption.
Qed.
