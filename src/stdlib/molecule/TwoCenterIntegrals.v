(** * TwoCenterIntegrals.v -- Two-center integrals for H₂⁺ / H₂
    Elements: s_pade, overlap_AB, kinetic_AB, nuclear_AB, nuclear_AA_B,
              kinetic_AA, nuclear_AA, overlap_AA
    Roles:    Padé approximant for overlap → all two-center integrals over Q
    Rules:    Exact rational arithmetic, verified at α=1 R=3/2
    Status:   Stdlib/molecule
    STATUS: 14 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  BASIC TWO-CENTER INTEGRAL FUNCTIONS OVER Q                         *)
(* ================================================================== *)

(** Padé approximant for exp(-2x): s(α,R) ≈ exp(-2αR) *)
Definition s_pade (alpha R : Q) : Q :=
  let x := alpha * R in
  (12 - 6 * x + x * x) / (12 + 6 * x + x * x).

(** Overlap integral S_AB *)
Definition overlap_AB (alpha R s : Q) : Q :=
  let x := alpha * R in
  s * (1 + x + x * x / 3).

(** Kinetic energy integral T_AB *)
Definition kinetic_AB (alpha R s : Q) : Q :=
  let x := alpha * R in
  alpha * alpha / 2 * s * (1 + x - x * x / 3).

(** Nuclear attraction V_AB (electron on nucleus B, orbital on A) *)
Definition nuclear_AB (alpha R s : Q) : Q :=
  -(alpha) * s * (1 + alpha * R).

(** Nuclear attraction V_AA_B (electron on nucleus A, potential from B) *)
Definition nuclear_AA_B (alpha R s : Q) : Q :=
  -(1 / R) * (1 - (1 + alpha * R) * s * s).

(** One-center kinetic energy T_AA *)
Definition kinetic_AA (alpha : Q) : Q := alpha * alpha / 2.

(** One-center nuclear attraction V_AA *)
Definition nuclear_AA (alpha : Q) : Q := -(alpha).

(** One-center overlap S_AA *)
Definition overlap_AA : Q := 1.

(* ================================================================== *)
(*  CONCRETE VALUES AT α=1, R=3/2                                     *)
(* ================================================================== *)

Lemma s_value : s_pade 1 (3#2) == 7#31.
Proof. unfold s_pade. vm_compute. reflexivity. Qed.

Lemma S_AB_value : overlap_AB 1 (3#2) (7#31) == 91#124.
Proof. unfold overlap_AB. vm_compute. reflexivity. Qed.

Lemma T_AA_value : kinetic_AA 1 == 1#2.
Proof. unfold kinetic_AA. vm_compute. reflexivity. Qed.

Lemma V_AA_value : nuclear_AA 1 == -(1).
Proof. unfold nuclear_AA. vm_compute. reflexivity. Qed.

Lemma T_AB_value : kinetic_AB 1 (3#2) (7#31) == 49#248.
Proof. unfold kinetic_AB. vm_compute. reflexivity. Qed.

Lemma V_AB_value : nuclear_AB 1 (3#2) (7#31) == -(35#62).
Proof. unfold nuclear_AB. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ADDITIONAL PROPERTIES                                              *)
(* ================================================================== *)

Lemma overlap_AA_value : overlap_AA == 1.
Proof. unfold overlap_AA. reflexivity. Qed.

Lemma s_pade_positive : 0 < s_pade 1 (3#2).
Proof. rewrite s_value. lra. Qed.

Lemma overlap_AB_positive : 0 < overlap_AB 1 (3#2) (7#31).
Proof. rewrite S_AB_value. lra. Qed.

Lemma T_AA_positive : 0 < kinetic_AA 1.
Proof. rewrite T_AA_value. lra. Qed.

Lemma V_AA_negative : nuclear_AA 1 < 0.
Proof. rewrite V_AA_value. lra. Qed.

Lemma T_AB_positive : 0 < kinetic_AB 1 (3#2) (7#31).
Proof. rewrite T_AB_value. lra. Qed.

Lemma V_AB_negative : nuclear_AB 1 (3#2) (7#31) < 0.
Proof. rewrite V_AB_value. lra. Qed.

Lemma s_pade_bounded : s_pade 1 (3#2) < 1.
Proof. rewrite s_value. lra. Qed.
