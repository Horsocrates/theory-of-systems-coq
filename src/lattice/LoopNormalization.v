(* ========================================================================= *)
(*                     LOOP NORMALIZATION                                    *)
(*           4D one-loop self-energy with time direction (N=2, N_t=2)       *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 10 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  4D loop normalization extends 3D to include temporal direction:         *)
(*                                                                          *)
(*    Elements = 4D effective propagator G_eff, self-energy sigma_4D,       *)
(*               one-loop correction delta_4D                               *)
(*    Roles    = time momenta k_0 in {0, pi} averaged over,                *)
(*               spatial eigenvalues from 3D Laplacian                      *)
(*    Rules    = G_eff < G_3D (time direction reduces propagator),          *)
(*               delta_4D positive and small (perturbative regime)          *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* 3D eigenvalues with multiplicities for N=2 *)
Definition lap3D_N2 : list (Q * nat) :=
  [(0, 1%nat); (4, 3%nat); (8, 3%nat); (12, 1%nat)].

(* 4D effective propagator: sum over time momenta k_0 in {0, pi} *)
(* G_eff(lambda_3D, m^2) = (1/2)(1/(lambda_3D+m^2) + 1/(4+lambda_3D+m^2)) *)
Definition G_eff_4D (lambda_3d m_sq : Q) : Q :=
  (1#2) * (1/(lambda_3d + m_sq) + 1/(4 + lambda_3d + m_sq)).

(* 4D self-propagator: weighted average over 3D eigenvalues *)
Definition self_prop_4D (m_sq : Q) : Q :=
  (1#8) * (
    1 * G_eff_4D 0 m_sq +
    3 * G_eff_4D 4 m_sq +
    3 * G_eff_4D 8 m_sq +
    1 * G_eff_4D 12 m_sq
  ).

(* Pre-computed self_prop via substituted G_eff values *)
Definition self_prop_4D_precomp : Q :=
  (1#8) * (1*(3#5) + 3*(7#45) + 3*(11#117) + 1*(15#221)).

(* 4D one-loop self-energy *)
Definition sigma_4D (m_sq : Q) : Q := (1#8) * self_prop_4D m_sq.

(* 4D one-loop correction to sin^2(theta_W) *)
(* delta = sin2_tree * cos2_tree * (13/8) * sigma *)
(* = (3/13)(10/13)(13/8) * sigma = (15/52) * sigma *)
Definition delta_4D (m_sq : Q) : Q :=
  (3#13) * (10#13) * (13#8) * sigma_4D m_sq.

(* ---- Lemma 1: G_eff at lambda=0, m^2=1 ---- *)
(* (1/2)(1/1 + 1/5) = (1/2)(6/5) = 3/5 *)
Lemma G_eff_zero : G_eff_4D 0 1 == 3#5.
Proof. unfold G_eff_4D. vm_compute. reflexivity. Qed.

(* ---- Lemma 2: G_eff at lambda=4, m^2=1 ---- *)
(* (1/2)(1/5 + 1/9) = (1/2)(14/45) = 7/45 *)
Lemma G_eff_four : G_eff_4D 4 1 == 7#45.
Proof. unfold G_eff_4D. vm_compute. reflexivity. Qed.

(* ---- Lemma 3: G_eff at lambda=8, m^2=1 ---- *)
(* (1/2)(1/9 + 1/13) = (1/2)(22/117) = 11/117 *)
Lemma G_eff_eight : G_eff_4D 8 1 == 11#117.
Proof. unfold G_eff_4D. vm_compute. reflexivity. Qed.

(* ---- Lemma 4: G_eff at lambda=12, m^2=1 ---- *)
(* (1/2)(1/13 + 1/17) = (1/2)(30/221) = 15/221 *)
Lemma G_eff_twelve : G_eff_4D 12 1 == 15#221.
Proof. unfold G_eff_4D. vm_compute. reflexivity. Qed.

(* ---- Lemma 5: Time direction reduces propagator ---- *)
(* G_eff(0,1) = 3/5 < 1 = G_3D(0,1) *)
Lemma G_eff_less_than_3D : G_eff_4D 0 1 < 1.
Proof.
  rewrite G_eff_zero. unfold Qlt. simpl. lia.
Qed.

(* ---- Lemma 6: self_prop_4D at m^2=1 = 587/3315 ---- *)
Lemma self_prop_4D_m1 : self_prop_4D 1 == self_prop_4D_precomp.
Proof.
  unfold self_prop_4D, self_prop_4D_precomp.
  apply Qmult_comp. { reflexivity. }
  apply Qplus_comp.
  - apply Qplus_comp.
    + apply Qplus_comp.
      * apply Qmult_comp. { reflexivity. } apply G_eff_zero.
      * apply Qmult_comp. { reflexivity. } apply G_eff_four.
    + apply Qmult_comp. { reflexivity. } apply G_eff_eight.
  - apply Qmult_comp. { reflexivity. } apply G_eff_twelve.
Qed.

Lemma self_prop_4D_exact : self_prop_4D_precomp == 587 # 3315.
Proof. unfold self_prop_4D_precomp. vm_compute. reflexivity. Qed.

(* ---- Lemma 7: sigma_4D at m^2=1 = 587/26520 ---- *)
Lemma sigma_4D_m1 : sigma_4D 1 == 587 # 26520.
Proof.
  unfold sigma_4D.
  rewrite self_prop_4D_m1, self_prop_4D_exact.
  vm_compute. reflexivity.
Qed.

(* ---- Lemma 8: delta_4D at m^2=1 = 587/91936 ---- *)
Lemma delta_4D_m1 : delta_4D 1 == 587 # 91936.
Proof.
  unfold delta_4D.
  rewrite sigma_4D_m1.
  vm_compute. reflexivity.
Qed.

(* ---- Lemma 9: delta_4D positive ---- *)
Lemma delta_4D_positive : 0 < delta_4D 1.
Proof.
  rewrite delta_4D_m1. unfold Qlt. simpl. lia.
Qed.

(* ---- Lemma 10: delta_4D small (< 1/10) ---- *)
Lemma delta_4D_small : delta_4D 1 < 1#10.
Proof.
  rewrite delta_4D_m1. unfold Qlt. simpl. lia.
Qed.
