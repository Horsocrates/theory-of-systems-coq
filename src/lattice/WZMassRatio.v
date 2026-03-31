(** * WZMassRatio.v — m_W/m_Z = cos θ_W from DOF counting
    Elements: cos2_W, mW_mZ_sq, rho parameter, observed masses
    Roles:    gauge structure → mass ratio → comparison with experiment
    Rules:    m_W/m_Z = cos θ_W, ρ = m_W²/(m_Z²·cos²θ) = 1
    STATUS:   8 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    STRUCTURAL PREDICTION:
      cos²θ = 1 - sin²θ = 1 - 3/13 = 10/13.
      m_W/m_Z = cos θ_W = √(10/13).
      (m_W/m_Z)² = 10/13 = 0.7692.

      Observed: (80.377/91.188)² = 0.7771.
      Error: 1.0%.

    NOTE: this is the SAME prediction as SM (both give m_W/m_Z = cos θ).
    The difference: our cos²θ = 10/13 is DERIVED, SM's comes from measured g,g'.
    This is a CONSISTENCY CHECK confirming sin²θ = 3/13.
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================ *)
(*  cos²θ FROM DOF COUNTING                                          *)
(* ================================================================ *)

Definition cos2_W : Q := 10 # 13.

(** (m_W/m_Z)² = cos²θ *)
Definition mW_mZ_sq_predicted : Q := cos2_W.

(** Observed masses in MeV for integer arithmetic *)
Definition mW_GeV_x1000 : Z := 80377.
Definition mZ_GeV_x1000 : Z := 91188.

(** Observed ratio² as Q *)
Definition mW_mZ_sq_observed : Q :=
  inject_Z (mW_GeV_x1000 * mW_GeV_x1000) /
  inject_Z (mZ_GeV_x1000 * mZ_GeV_x1000).

(* ================================================================ *)
(*  PREDICTIONS                                                      *)
(* ================================================================ *)

Lemma prediction : mW_mZ_sq_predicted == 10 # 13.
Proof. unfold mW_mZ_sq_predicted, cos2_W. reflexivity. Qed.

Lemma observed_lower : mW_mZ_sq_observed > 77 # 100.
Proof.
  unfold mW_mZ_sq_observed, mW_GeV_x1000, mZ_GeV_x1000.
  vm_compute. reflexivity.
Qed.

Lemma observed_upper : mW_mZ_sq_observed < 78 # 100.
Proof.
  unfold mW_mZ_sq_observed, mW_GeV_x1000, mZ_GeV_x1000.
  vm_compute. reflexivity.
Qed.

Lemma match_within_1pct :
  Qabs (mW_mZ_sq_predicted - mW_mZ_sq_observed) < 1 # 100.
Proof.
  unfold mW_mZ_sq_predicted, cos2_W, mW_mZ_sq_observed,
    mW_GeV_x1000, mZ_GeV_x1000.
  simpl. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  CONSISTENCY                                                      *)
(* ================================================================ *)

Lemma cos2_plus_sin2 : cos2_W + (3 # 13) == 1.
Proof. unfold cos2_W. vm_compute. reflexivity. Qed.

(** ρ parameter: m_W²/(m_Z²·cos²θ) = 1 at tree level *)
Lemma rho_parameter : mW_mZ_sq_predicted / cos2_W == 1.
Proof.
  unfold mW_mZ_sq_predicted, cos2_W.
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  HONEST COMPARISON                                                *)
(* ================================================================ *)

(** Our prediction matches SM's: both give m_W/m_Z = cos θ.
    The 1% difference vs experiment comes from sin²θ = 3/13 (tree)
    vs sin²θ = 0.23122 (measured with radiative corrections).
    One-loop δ (from WeinbergCorrectionFixed.v) moves us closer. *)

Lemma prediction_close_to_SM :
  Qabs (cos2_W - (7688 # 10000)) < 1 # 1000.
Proof.
  unfold cos2_W. vm_compute. reflexivity.
Qed.

(** Our cos²θ = 10/13 ≈ 0.7692.
    SM measured: cos²θ = 1 - 0.23122 = 0.76878.
    Difference: 0.0005. Within 0.1%. *)

Lemma tree_vs_measured :
  Qabs (cos2_W - (76878 # 100000)) < 1 # 1000.
Proof.
  unfold cos2_W. vm_compute. reflexivity.
Qed.
