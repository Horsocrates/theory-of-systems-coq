(** * ProcessGravWaveform.v — Gravitational Waveform Computation

    Theory of Systems — Step 6: Unrealized Potential (File 3)

    Elements: gw_amplitude, gw_waveform, waveform at 3 time steps
    Roles:    Waveform h(t) = amplitude * (1 - cos(omega*t)) approximated over Q
    Rules:    Use one_minus_cos_approx from CosineAction for cosine terms
    Status:   complete

    STATUS: 10 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.CosineAction.
From ToS Require Import PowerSeries.
From ToS Require Import SeriesConvergence.

(* ================================================================== *)
(*  Part I: Waveform setup  (~3 lemmas)                               *)
(* ================================================================== *)

(** Gravitational wave amplitude (dimensionless strain) *)
Definition gw_amplitude : Q := (1#1000).

(** Angular frequency (rational approx) *)
Definition gw_omega : Q := (1#1).

(** Waveform at time t: h(t) = amplitude * (1 - cos(omega*t))
    Using k-term Taylor approximation for 1-cos *)
Definition gw_waveform (t : Q) (k : nat) : Q :=
  gw_amplitude * one_minus_cos_approx (gw_omega * t) k.

Lemma gw_amplitude_pos : 0 < gw_amplitude.
Proof. unfold gw_amplitude, Qlt; simpl; lia. Qed.

Lemma gw_amplitude_small : gw_amplitude < (1#10).
Proof. unfold gw_amplitude, Qlt; simpl; lia. Qed.

Lemma gw_waveform_at_zero : gw_waveform 0 0 == 0.
Proof.
  unfold gw_waveform, gw_omega, gw_amplitude, one_minus_cos_approx.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Part II: Concrete values  (~4 lemmas)                             *)
(* ================================================================== *)

(** 1 - cos(theta) at 1st order = theta^2/2 *)
Lemma cos_approx_1_value : forall theta,
  one_minus_cos_approx theta 0 == Qpow theta 2 / 2.
Proof.
  intros theta. unfold one_minus_cos_approx, partial_sum, cos_term.
  unfold alt_sign. simpl.
  unfold Qfact. simpl.
  field.
Qed.

(** Waveform at t=1, 1st-order: h = amplitude * 1^2/2 *)
Lemma gw_at_t1_order1 : gw_waveform 1 0 == (1#2000).
Proof.
  unfold gw_waveform, gw_omega, gw_amplitude.
  rewrite cos_approx_1_value. vm_compute. reflexivity.
Qed.

(** Waveform at t=2, 1st-order: h = amplitude * 4/2 = amplitude * 2 *)
Lemma gw_at_t2_order1 : gw_waveform 2 0 == (1#500).
Proof.
  unfold gw_waveform, gw_omega, gw_amplitude.
  rewrite cos_approx_1_value. vm_compute. reflexivity.
Qed.

(** Waveform increases with time (at 1st order) *)
Lemma gw_increases_t1_t2 : gw_waveform 1 0 < gw_waveform 2 0.
Proof.
  rewrite gw_at_t1_order1. rewrite gw_at_t2_order1.
  unfold Qlt; simpl; lia.
Qed.

(* ================================================================== *)
(*  Part III: Summary  (~3 lemmas)                                    *)
(* ================================================================== *)

Lemma gw_at_t3_order1 : gw_waveform 3 0 == (9#2000).
Proof.
  unfold gw_waveform, gw_omega, gw_amplitude.
  rewrite cos_approx_1_value. vm_compute. reflexivity.
Qed.

Lemma gw_all_nonneg : forall t k, 0 <= one_minus_cos_approx (gw_omega * t) k ->
  0 <= gw_waveform t k.
Proof.
  intros t k Hcos. unfold gw_waveform.
  apply Qmult_le_0_compat.
  - unfold gw_amplitude. lra.
  - exact Hcos.
Qed.

Theorem grav_waveform_summary :
  gw_waveform 0 0 == 0 /\
  gw_waveform 1 0 == (1#2000) /\
  gw_waveform 2 0 == (1#500) /\
  gw_waveform 1 0 < gw_waveform 2 0.
Proof.
  split; [| split; [| split]].
  - exact gw_waveform_at_zero.
  - apply gw_at_t1_order1.
  - apply gw_at_t2_order1.
  - apply gw_increases_t1_t2.
Qed.

Definition v1_theorem_count := 10%nat.
