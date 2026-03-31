(* ========================================================================= *)
(*                     BETA FROM DECIMATION                                  *)
(*           RG beta function extracted from block decimation data            *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 15 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  The beta function describes how couplings run under RG:                 *)
(*                                                                          *)
(*    Elements = RG data at each scale (hopping t, mass m, step n)          *)
(*    Roles    = bare coupling (step 0) vs renormalized (step 1)            *)
(*    Rules    = coupling decreases, alpha_inv increases (asymptotic        *)
(*               freedom in 1D toy), beta > 0 drives flow to weak coupling *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== RG data record ===== *)

Record RGData := mkRG { rg_t : Q; rg_m : Q; rg_step : nat }.

Definition rg0 : RGData := mkRG 1 1 0.
Definition rg1 : RGData := mkRG (1#8) (5#8) 1.

(* ===== Derived quantities ===== *)

Definition eff_coupling (d : RGData) : Q := rg_t d / rg_m d.
Definition alpha_inv (d : RGData) : Q := rg_m d / rg_t d.
Definition rg_ratio (d0 d1 : RGData) : Q := rg_t d1 / rg_t d0.
Definition beta_1step (d0 d1 : RGData) : Q := alpha_inv d1 - alpha_inv d0.

(* ===== Coupling values ===== *)

Lemma coupling_0 : eff_coupling rg0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma coupling_1 : eff_coupling rg1 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma coupling_decreased : eff_coupling rg1 < eff_coupling rg0.
Proof.
  assert (H0 : eff_coupling rg0 == 1) by (vm_compute; reflexivity).
  assert (H1 : eff_coupling rg1 == 1#5) by (vm_compute; reflexivity).
  rewrite H0, H1. lra.
Qed.

(* ===== Inverse coupling (alpha_inv) ===== *)

Lemma alpha_inv_0 : alpha_inv rg0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_inv_1 : alpha_inv rg1 == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma beta_value : beta_1step rg0 rg1 == 4.
Proof. vm_compute. reflexivity. Qed.

(* ===== Hopping and mass ===== *)

Lemma hopping_ratio : rg_ratio rg0 rg1 == 1#8.
Proof. vm_compute. reflexivity. Qed.

Lemma mass_decreased : rg_m rg1 < rg_m rg0.
Proof.
  unfold rg1, rg0, rg_m. lra.
Qed.

Lemma hopping_decreased_faster : rg_ratio rg0 rg1 < rg_m rg1 / rg_m rg0.
Proof.
  assert (H1 : rg_ratio rg0 rg1 == 1#8) by (vm_compute; reflexivity).
  assert (H2 : rg_m rg1 / rg_m rg0 == 5#8) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

Lemma beta_hopping : rg_t rg1 - rg_t rg0 == -(7#8).
Proof. vm_compute. reflexivity. Qed.

(* Linear extrapolation of alpha_inv: if beta=4 constant *)
Lemma linear_extrapolation : 1 + 4 * 14 == 57.
Proof. vm_compute. reflexivity. Qed.

(* Mass ratio *)
Lemma mass_ratio : rg_m rg1 / rg_m rg0 == 5#8.
Proof. vm_compute. reflexivity. Qed.

(* ===== Additional checks ===== *)

Lemma beta_positive : 0 < beta_1step rg0 rg1.
Proof.
  assert (H : beta_1step rg0 rg1 == 4) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

Lemma coupling_ratio_check : eff_coupling rg1 / eff_coupling rg0 == 1#5.
Proof. vm_compute. reflexivity. Qed.

(* ===== Synthesis ===== *)

Lemma beta_from_decimation_synthesis :
  eff_coupling rg1 < eff_coupling rg0 /\
  0 < beta_1step rg0 rg1 /\
  beta_1step rg0 rg1 == 4 /\
  rg_ratio rg0 rg1 < rg_m rg1 / rg_m rg0.
Proof.
  split; [exact coupling_decreased |].
  split; [exact beta_positive |].
  split; [exact beta_value |].
  exact hopping_decreased_faster.
Qed.
