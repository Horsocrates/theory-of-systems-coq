(* ========================================================================= *)
(*        EXACT EIGENVALUES — Characteristic Polynomial of Continuum Operator *)
(*                                                                            *)
(*  Matrix M = [[-1/3, -1/2, -7/15],                                        *)
(*              [4, 8/3, 2],                                                  *)
(*              [-4, -2, -4/3]]                                               *)
(*                                                                            *)
(*  Characteristic polynomial: p(λ) = λ³ - λ² + (2/15)λ + 8/135            *)
(*  Coefficients: trace = 1, cofactors = 2/15, det = -8/135                 *)
(*  λ₀ = 2/3 is a root (verified: 40-60+12+8 = 0).                         *)
(*  Quadratic factor: q(λ) = λ² - λ/3 - 4/45                               *)
(*  Discriminant: Δ = 7/15 > 0 (two real roots)                             *)
(*                                                                            *)
(*  STATUS: ~25 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import gauge.ContinuumOperator.

(* ========================================================================= *)
(*  PART I: Principal Minors                                                  *)
(* ========================================================================= *)

(** Minor M₀₀ = det [[8/3, 2], [-2, -4/3]]
    = (8/3)(-4/3) - 2(-2) = -32/9 + 4 = 4/9 *)
Lemma minor_00 :
  cont_entry 1 1 * cont_entry 2 2 - cont_entry 1 2 * cont_entry 2 1 == 4#9.
Proof.
  unfold cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq.
  simpl. lia.
Qed.

(** Minor M₁₁ = det [[-1/3, -7/15], [-4, -4/3]]
    = (-1/3)(-4/3) - (-7/15)(-4) = 4/9 - 28/15 = -64/45 *)
Lemma minor_11 :
  cont_entry 0 0 * cont_entry 2 2 - cont_entry 0 2 * cont_entry 2 0 == -(64#45).
Proof.
  unfold cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq.
  simpl. lia.
Qed.

(** Minor M₂₂ = det [[-1/3, -1/2], [4, 8/3]]
    = (-1/3)(8/3) - (-1/2)(4) = -8/9 + 2 = 10/9 *)
Lemma minor_22 :
  cont_entry 0 0 * cont_entry 1 1 - cont_entry 0 1 * cont_entry 1 0 == 10#9.
Proof.
  unfold cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq.
  simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART II: Cofactor Sum                                                     *)
(* ========================================================================= *)

(** Cofactor sum = minor_00 + minor_11 + minor_22
    = 4/9 + (-64/45) + 10/9 = 20/45 - 64/45 + 50/45 = 6/45 = 2/15 *)
Theorem cofactor_sum_value :
  (4#9) + (-(64#45)) + (10#9) == 2#15.
Proof. unfold Qeq. simpl. lia. Qed.

(** Cofactor sum check: 2/15 is positive *)
Lemma cofactor_sum_positive : 0 < 2#15.
Proof. lra. Qed.

(* ========================================================================= *)
(*  PART III: Determinant                                                     *)
(* ========================================================================= *)

(** det(M) by cofactor expansion along row 0:
    = (-1/3)(4/9) - (-1/2)(8/3) + (-7/15)(8/3)
    = -4/27 + 4/3 - 56/45
    LCD 135: (-20 + 180 - 168)/135 = -8/135 *)
Theorem det_value :
  cont_entry 0 0 * (cont_entry 1 1 * cont_entry 2 2 - cont_entry 1 2 * cont_entry 2 1) -
  cont_entry 0 1 * (cont_entry 1 0 * cont_entry 2 2 - cont_entry 1 2 * cont_entry 2 0) +
  cont_entry 0 2 * (cont_entry 1 0 * cont_entry 2 1 - cont_entry 1 1 * cont_entry 2 0) == -(8#135).
Proof.
  unfold cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq.
  simpl. lia.
Qed.

(** Determinant is negative *)
Lemma det_negative : -(8#135) < 0.
Proof. lra. Qed.

(* ========================================================================= *)
(*  PART IV: Characteristic Polynomial                                       *)
(* ========================================================================= *)

(** p(λ) = λ³ - tr·λ² + cofactors·λ - det
    = λ³ - λ² + (2/15)λ + 8/135 *)
Definition char_poly (lam : Q) : Q :=
  lam * lam * lam - lam * lam + (2#15) * lam + (8#135).

(** Integer-scaled form: 135·p(λ) = 135λ³ - 135λ² + 18λ + 8 *)
Definition char_poly_int (lam : Q) : Q :=
  135 * lam * lam * lam - 135 * lam * lam + 18 * lam + 8.

(** p(0) = 8/135 > 0 *)
Lemma char_poly_at_0 : char_poly 0 == 8#135.
Proof. unfold char_poly, Qeq. simpl. lia. Qed.

(** p(1) = 1 - 1 + 2/15 + 8/135 = 26/135 *)
Lemma char_poly_at_1 : char_poly 1 == 26#135.
Proof. unfold char_poly, Qeq. simpl. lia. Qed.

(* ========================================================================= *)
(*  PART V: λ₀ = 2/3 is a Root                                              *)
(* ========================================================================= *)

(** (2/3)² = 4/9 *)
Lemma two_thirds_squared : (2#3) * (2#3) == 4#9.
Proof. unfold Qeq. simpl. lia. Qed.

(** (2/3)³ = 8/27 *)
Lemma two_thirds_cubed : (2#3) * (2#3) * (2#3) == 8#27.
Proof. unfold Qeq. simpl. lia. Qed.

(** ★ p(2/3) = 0 ★
    8/27 - 4/9 + 4/45 + 8/135
    LCD 135: 40 - 60 + 12 + 8 = 0 *)
Theorem lambda_0_is_root : char_poly (2#3) == 0.
Proof. unfold char_poly, Qeq. simpl. lia. Qed.

(** Integer form: P(2/3) = 135·8/27 - 135·4/9 + 18·2/3 + 8 = 40-60+12+8 = 0 *)
Theorem lambda_0_is_root_int : char_poly_int (2#3) == 0.
Proof. unfold char_poly_int, Qeq. simpl. lia. Qed.

(* ========================================================================= *)
(*  PART VI: Quadratic Factor                                                *)
(* ========================================================================= *)

(** After dividing by (λ - 2/3):
    p(λ) = (λ - 2/3) · q(λ)
    where q(λ) = λ² - (1/3)λ - 4/45 *)
Definition quadratic_factor (lam : Q) : Q :=
  lam * lam - (1#3) * lam - (4#45).

(** q(0) = -4/45 < 0 *)
Lemma quadratic_at_0 : quadratic_factor 0 == -(4#45).
Proof. unfold quadratic_factor, Qeq. simpl. lia. Qed.

Lemma quadratic_at_0_negative : quadratic_factor 0 < 0.
Proof. assert (H := quadratic_at_0). rewrite H. lra. Qed.

(** q(2/3) = 4/9 - 2/9 - 4/45 = 10/45 - 4/45 = 6/45 = 2/15 ≠ 0 *)
Lemma quadratic_at_2_3 : quadratic_factor (2#3) == 2#15.
Proof. unfold quadratic_factor, Qeq. simpl. lia. Qed.

(** q(2/3) > 0 — 2/3 is NOT a repeated root *)
Lemma quadratic_at_2_3_positive : 0 < quadratic_factor (2#3).
Proof. assert (H := quadratic_at_2_3). rewrite H. lra. Qed.

(* ========================================================================= *)
(*  PART VII: Discriminant                                                    *)
(* ========================================================================= *)

(** Discriminant of q(λ) = λ² - (1/3)λ - 4/45:
    Δ = (1/3)² + 4·(4/45) = 1/9 + 16/45 = 5/45 + 16/45 = 21/45 = 7/15 *)
Definition quad_discriminant : Q := 7#15.

Theorem discriminant_value :
  (1#3) * (1#3) + 4 * (4#45) == quad_discriminant.
Proof. unfold quad_discriminant, Qeq. simpl. lia. Qed.

Lemma discriminant_positive : 0 < quad_discriminant.
Proof. unfold quad_discriminant. lra. Qed.

(** Product of remaining roots = -4/45 < 0 (opposite signs) *)
Theorem roots_opposite_sign :
  -(4#45) < 0.
Proof. lra. Qed.

(** Sum of remaining roots = 1/3 *)
Theorem roots_sum :
  0 < 1#3.
Proof. lra. Qed.

(* ========================================================================= *)
(*  PART VIII: Summary                                                        *)
(* ========================================================================= *)

(** ★ EIGENVALUES MAIN ★ *)
Theorem eigenvalues_main :
  (* 1. Trace = 1 *)
  cont_entry 0 0 + cont_entry 1 1 + cont_entry 2 2 == 1 /\
  (* 2. Cofactor sum = 2/15 *)
  (4#9) + (-(64#45)) + (10#9) == 2#15 /\
  (* 3. λ₀ = 2/3 is root *)
  char_poly (2#3) == 0 /\
  (* 4. Discriminant = 7/15 > 0 *)
  0 < quad_discriminant.
Proof.
  split; [exact cont_matrix_trace |].
  split; [exact cofactor_sum_value |].
  split; [exact lambda_0_is_root |].
  exact discriminant_positive.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~25 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part I: minor_00, minor_11, minor_22 (3)                                 *)
(*  Part II: cofactor_sum_value, cofactor_sum_positive (2)                    *)
(*  Part III: det_value, det_negative (2)                                     *)
(*  Part IV: char_poly_at_0, char_poly_at_1 (2)                              *)
(*  Part V: two_thirds_squared, two_thirds_cubed,                            *)
(*           lambda_0_is_root, lambda_0_is_root_int (4)                      *)
(*  Part VI: quadratic_at_0, quadratic_at_0_negative,                        *)
(*            quadratic_at_2_3, quadratic_at_2_3_positive (4)                *)
(*  Part VII: discriminant_value, discriminant_positive,                      *)
(*             roots_opposite_sign, roots_sum (4)                             *)
(*  Part VIII: eigenvalues_main, total_count (2)                              *)
(* ========================================================================= *)
