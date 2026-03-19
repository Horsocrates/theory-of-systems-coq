(** * LithiumLattice.v — Lithium with Slater Screening as ToS System
    Elements: Li atom (Z=3, 3 electrons), Slater screening
    Roles:    effective charge, frozen-core approximation
    Rules:    Z_eff from Slater rules, outer electron energy
    Status:   Dir 1, File 3 of Atomic Physics
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

Open Scope Q_scope.

(* ========================================================================= *)
(*              SLATER SCREENING FOR LITHIUM                                 *)
(* ========================================================================= *)

(** Li has Z=3, 2 inner (1s) + 1 outer (2s) electron.
    Slater screening constant for 2s by 1s: sigma = 2 * (5/16) = 5/8.
    But standard Slater for Li 2s: each 1s screens by 0.85.
    We use simplified: sigma_1s = 5/16 per 1s electron. *)

Definition Z_Li : Q := 3.

(** Slater screening per 1s electron for 2s *)
Definition slater_1s_screen : Q := 5 # 16.

(** Number of 1s electrons screening the 2s *)
Definition n_inner_Li : nat := 2.

(** Total screening *)
Definition sigma_Li : Q := inject_Z (Z.of_nat n_inner_Li) * slater_1s_screen.

(** Effective nuclear charge seen by outer electron *)
Definition Z_effective_Li : Q := Z_Li - sigma_Li.

Lemma Z_eff_Li_value : Z_effective_Li == 19 # 8.
Proof.
  unfold Z_effective_Li, Z_Li, sigma_Li, n_inner_Li, slater_1s_screen, inject_Z.
  unfold Qeq; simpl; lia.
Qed.

(** Z_eff is positive *)
Lemma Z_eff_Li_positive : 0 < Z_effective_Li.
Proof. rewrite Z_eff_Li_value. lra. Qed.

(* ========================================================================= *)
(*              FROZEN-CORE MODEL                                            *)
(* ========================================================================= *)

(** Outer electron energy in hydrogen-like model:
    E_outer = -Z_eff^2 / (2 * n^2) where n=2 for 2s.
    E_outer = -(19/8)^2 / (2*4) = -361/512 *)
Definition li_outer_energy : Q := -(Z_effective_Li * Z_effective_Li) / (2 * 4).

Lemma li_outer_value : li_outer_energy == -(361 # 512).
Proof.
  unfold li_outer_energy, Z_effective_Li, Z_Li, sigma_Li,
         n_inner_Li, slater_1s_screen.
  vm_compute. reflexivity.
Qed.

(** Inner shell (1s^2) energy estimate:
    E_inner = 2 * (-Z^2/2) + V_ee(1s,1s)
    Simplified: use He-like = -Z^2 + 5Z/8 *)
Definition li_inner_energy : Q :=
  -(Z_Li * Z_Li) + (5 # 8) * Z_Li.

Lemma li_inner_value : li_inner_energy == -(57 # 8).
Proof.
  unfold li_inner_energy, Z_Li.
  unfold Qeq; simpl; lia.
Qed.

(** Total Li energy: inner + outer *)
Definition li_total_energy : Q := li_inner_energy + li_outer_energy.

(** Li total = inner + outer. Both negative → total negative *)
Lemma li_inner_negative : li_inner_energy < 0.
Proof. rewrite li_inner_value. lra. Qed.

Lemma li_outer_negative : li_outer_energy < 0.
Proof. rewrite li_outer_value. lra. Qed.

(** Li ionization energy: remove outer electron.
    IE = E(Li+) - E(Li) = li_inner_energy - li_total_energy = -li_outer_energy *)
Definition li_ionization : Q := - li_outer_energy.

Lemma li_ionization_positive : 0 < li_ionization.
Proof.
  unfold li_ionization. rewrite li_outer_value. lra.
Qed.
