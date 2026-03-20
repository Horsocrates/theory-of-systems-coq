(** * SU3Characters.v -- SU(3) character polynomials and transfer coefficients
    Elements: chi_fund_approx, t_trivial_su3, t_fund_su3, t_adj_su3
    Roles:    Character expansion for SU(3) at strong coupling
    Rules:    t_{0,0} = 1, t_{1,0} = β/6, t_{1,1} = β²/72
    Status:   Gauge
    STATUS: 16 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.SU3Representations.

Open Scope Q_scope.

(* ================================================================== *)
(*  CHARACTER APPROXIMATIONS                                           *)
(* ================================================================== *)

(** SU(3) characters in terms of angles θ₁, θ₂.
    χ₃(θ₁,θ₂) = e^{iθ₁} + e^{iθ₂} + e^{-i(θ₁+θ₂)}
    Over Q with cos ≈ 1 - t²/2: χ₃ ≈ 3 - (t₁² + t₂² + (t₁+t₂)²)/2 *)

Definition chi_fund_approx (t1 t2 : Q) : Q :=
  3 - (t1*t1 + t2*t2 + (t1+t2)*(t1+t2)) * (1#2).

Lemma chi_fund_at_zero : chi_fund_approx 0 0 == 3.
Proof. unfold chi_fund_approx. ring. Qed.

(** At small angle: χ₃ ≈ 3 - t² (quadratic correction) *)
Lemma chi_fund_decreases : forall t,
  chi_fund_approx t 0 == 3 - t * t.
Proof. intro t. unfold chi_fund_approx. ring. Qed.

(** χ₈(0,0) = dim(adjoint) = 8 *)
Definition chi_adj_at_zero : Q := 8.

Lemma chi_adj_value : chi_adj_at_zero == 8.
Proof. unfold chi_adj_at_zero. reflexivity. Qed.

(* ================================================================== *)
(*  TRANSFER MATRIX COEFFICIENTS                                       *)
(* ================================================================== *)

(** Strong coupling expansion: only low (p,q) matter.
    t_{0,0} ≈ 1 (trivial rep dominates)
    t_{1,0} ≈ β/6 (next order)
    t_{1,1} ≈ β²/72 (adjoint suppressed) *)

Definition t_trivial_su3 (beta : Q) : Q := 1.
Definition t_fund_su3 (beta : Q) : Q := beta * (1#6).
Definition t_adj_su3 (beta : Q) : Q := beta * beta * (1#72).

Lemma t_trivial_value : forall beta, t_trivial_su3 beta == 1.
Proof. intro. unfold t_trivial_su3. reflexivity. Qed.

Lemma t_fund_at_1 : t_fund_su3 1 == 1#6.
Proof. unfold t_fund_su3. ring. Qed.

Lemma t_adj_at_1 : t_adj_su3 1 == 1#72.
Proof. unfold t_adj_su3. ring. Qed.

Lemma t_fund_at_6 : t_fund_su3 6 == 1.
Proof. unfold t_fund_su3. ring. Qed.

(** Coefficient hierarchy: trivial > fundamental > adjoint *)
Lemma t_hierarchy_01 : forall beta,
  0 < beta -> beta < 6 ->
  t_fund_su3 beta < t_trivial_su3 beta.
Proof.
  intros beta Hpos Hlt.
  unfold t_fund_su3, t_trivial_su3. lra.
Qed.

Lemma t_hierarchy_su3 :
  t_adj_su3 1 < t_fund_su3 1.
Proof.
  rewrite t_adj_at_1, t_fund_at_1. lra.
Qed.

(** All coefficients nonneg *)
Lemma t_fund_nonneg : forall beta, 0 <= beta -> 0 <= t_fund_su3 beta.
Proof. intros. unfold t_fund_su3. lra. Qed.

Lemma t_adj_nonneg : forall beta, 0 <= beta -> 0 <= t_adj_su3 beta.
Proof. intros. unfold t_adj_su3. nra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem su3_characters_synthesis :
  chi_fund_approx 0 0 == 3 /\
  t_fund_su3 1 == 1#6 /\
  t_adj_su3 1 == 1#72 /\
  su3_casimir 1 0 == 4#3 /\
  su3_casimir 1 1 == 3.
Proof.
  split; [|split; [|split; [|split]]].
  - exact chi_fund_at_zero.
  - exact t_fund_at_1.
  - exact t_adj_at_1.
  - exact casimir_fund.
  - exact casimir_adjoint.
Qed.
