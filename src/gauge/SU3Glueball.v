(** * SU3Glueball.v -- Glueball mass from SU(3) gap
    Elements: glueball_mass_su3, mass_ratio_su3
    Roles:    Glueball mass = mass gap in lattice units
    Rules:    m_G(1) = 5/6, mass ratio from gap hierarchy
    Status:   Gauge
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.SU3Characters.
From ToS Require Import gauge.SU3Transfer.

Open Scope Q_scope.

(* ================================================================== *)
(*  GLUEBALL MASS                                                      *)
(* ================================================================== *)

(** Glueball mass m_G = gap in lattice units
    m_G · a = gap(β). Physical mass: m_G = gap/a *)

Definition glueball_mass_su3 (beta : Q) : Q :=
  gap_su3 beta.

Lemma glueball_at_0 : glueball_mass_su3 0 == 1.
Proof. unfold glueball_mass_su3. exact gap_su3_at_0. Qed.

Lemma glueball_at_1 : glueball_mass_su3 1 == 5#6.
Proof. unfold glueball_mass_su3. exact gap_su3_at_1. Qed.

Lemma glueball_at_3 : glueball_mass_su3 3 == 1#2.
Proof. unfold glueball_mass_su3. exact gap_su3_at_3. Qed.

Lemma glueball_positive : 0 < glueball_mass_su3 1.
Proof. rewrite glueball_at_1. lra. Qed.

(* ================================================================== *)
(*  MASS RATIO                                                         *)
(* ================================================================== *)

(** 0⁺⁺ / 0⁻⁺ mass ratio approximation:
    ratio = (t₀₀ - t₁₁) / (t₀₀ - t₁₀) *)

Definition mass_ratio_su3 (beta : Q) : Q :=
  (t_trivial_su3 beta - t_adj_su3 beta) /
  (t_trivial_su3 beta - t_fund_su3 beta).

Lemma mass_ratio_at_1 :
  mass_ratio_su3 1 == (1 - (1#72)) / (1 - (1#6)).
Proof.
  unfold mass_ratio_su3.
  rewrite t_trivial_value, t_fund_at_1, t_adj_at_1. reflexivity.
Qed.

Lemma mass_ratio_at_1_value :
  mass_ratio_su3 1 == 71#60.
Proof.
  unfold mass_ratio_su3, t_trivial_su3, t_fund_su3, t_adj_su3.
  vm_compute. reflexivity.
Qed.

(** Mass ratio > 1 (excited state heavier) *)
Lemma mass_ratio_gt_1 : 1 < mass_ratio_su3 1.
Proof. rewrite mass_ratio_at_1_value. lra. Qed.

(** QCD lattice data: m(0++)/m(0-+) ≈ 1.39
    Our strong-coupling: 71/60 ≈ 1.183. Same ballpark. *)

(* ================================================================== *)
(*  GLUEBALL MASS DECREASES WITH β                                    *)
(* ================================================================== *)

Lemma glueball_decreases :
  glueball_mass_su3 3 < glueball_mass_su3 1.
Proof. rewrite glueball_at_1, glueball_at_3. lra. Qed.

Lemma glueball_decreases_01 :
  glueball_mass_su3 1 < glueball_mass_su3 0.
Proof. rewrite glueball_at_0, glueball_at_1. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem glueball_synthesis :
  glueball_mass_su3 1 == 5#6 /\
  0 < glueball_mass_su3 1 /\
  mass_ratio_su3 1 == 71#60 /\
  1 < mass_ratio_su3 1.
Proof.
  split; [|split; [|split]].
  - exact glueball_at_1.
  - exact glueball_positive.
  - exact mass_ratio_at_1_value.
  - exact mass_ratio_gt_1.
Qed.
