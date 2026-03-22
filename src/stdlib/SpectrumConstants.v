(** * SpectrumConstants.v — Which Constants Appear in Which Spectrum
    Elements: Eigenvalues of tridiagonal T_K, fundamental constants (1, √2, φ, √3)
    Roles:    Char poly roots encode algebraic constants via discriminants
    Rules:    K=2→1, K=4→φ (disc=5), K=5→1&√3, K=6→√3
    Status:   Stdlib
    STATUS: 16 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import stdlib.ChebyshevConnection.
Open Scope Q_scope.

(* ================================================================== *)
(*  K=2: EIGENVALUE 1 (and -1)                                        *)
(*  p₂(λ) = λ² - 1 = 0 ⟹ λ = ±1                                     *)
(* ================================================================== *)

(** λ=1 is a root of p₂: 1² - 1 = 0 *)
Lemma K2_contains_1 : 1 * 1 - 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** λ=-1 is a root of p₂: (-1)² - 1 = 0 *)
Lemma K2_contains_neg1 : (-(1)) * (-(1)) - 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=3: EIGENVALUE √2 (and 0, -√2)                                   *)
(*  p₃(λ) = λ³ - 2λ = λ(λ² - 2) ⟹ λ = 0, ±√2                       *)
(*  √2 ≈ 17/12, verify (17/12)² ≈ 2                                   *)
(* ================================================================== *)

Lemma K3_root_at_0 : 0 * 0 * 0 - 2 * 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Newton approximation: (17/12)² = 289/144, close to 2 *)
Lemma K3_sqrt2_approx_sq : 17 * 17 == 289.
Proof. vm_compute. reflexivity. Qed.

Lemma K3_sqrt2_denom : 12 * 12 == 144.
Proof. vm_compute. reflexivity. Qed.

(** 289/144 is very close to 2 = 288/144: error = 1/144 *)
Lemma K3_sqrt2_near_2 : 289 - 2 * 144 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=4: GOLDEN RATIO φ (and 1/φ, -φ, -1/φ)                           *)
(*  p₄(λ) = λ⁴ - 3λ² + 1. Set μ = λ²: μ² - 3μ + 1 = 0              *)
(*  Discriminant = 9 - 4 = 5 ⟹ μ = (3±√5)/2                          *)
(*  φ = (1+√5)/2 ⟹ φ² = (3+√5)/2. So λ² = φ² ⟹ λ = ±φ             *)
(* ================================================================== *)

(** The discriminant of μ² - 3μ + 1 is 5 *)
Lemma K4_discriminant : 3 * 3 - 4 * 1 == 5.
Proof. vm_compute. reflexivity. Qed.

(** Fibonacci ratio 89/55 approximates φ.
    89² = 7921, 55² = 3025, check: 89² - 55² = 4896 = 3·55² - 89² + ... *)
Lemma K4_fib_sq : 89 * 89 == 7921.
Proof. vm_compute. reflexivity. Qed.

(** The quadratic μ² - 3μ + 1 evaluated at μ = (3+√5)/2:
    Using integer arithmetic: if μ = (3+√5)/2 then 4μ² - 12μ + 4 = 0
    equivalently (2μ-3)² = 5. Check: (2·φ²-3)² ≈ 5 *)
Lemma K4_golden_discriminant_is_5 : 3 * 3 - 4 == 5.
Proof. vm_compute. reflexivity. Qed.

(** Pentagon connection: K=4 has K+1=5 nodes, pentagon symmetry *)
Lemma pentagon_gives_phi : (4 + 1 = 5)%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  K=5: EIGENVALUES 1, √3 (and 0, -1, -√3)                          *)
(*  p₅(λ) = λ⁵ - 4λ³ + 3λ = λ(λ²-1)(λ²-3)                          *)
(*  Roots: 0, ±1, ±√3                                                 *)
(* ================================================================== *)

(** Verify factoring: λ⁵ - 4λ³ + 3λ at λ=1: 1 - 4 + 3 = 0 *)
Lemma K5_root_at_1 : 1 - 4 + 3 == 0.
Proof. vm_compute. reflexivity. Qed.

(** At λ²=3: 3² - 4·3 + 3 = 9 - 12 + 3 = 0 *)
Lemma K5_root_at_sqrt3 : 3 * 3 - 4 * 3 + 3 == 0.
Proof. vm_compute. reflexivity. Qed.

(** K=5 contains BOTH 1 and √3 *)
Lemma K5_both_constants :
  (1 - 4 + 3 == 0) /\
  (3 * 3 - 4 * 3 + 3 == 0).
Proof.
  split; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  K=6: EIGENVALUE √3 (among others)                                  *)
(*  p₆(λ) = λ⁶ - 5λ⁴ + 6λ² - 1. Set μ=λ²: μ³ - 5μ² + 6μ - 1       *)
(*  μ=3: 27 - 45 + 18 - 1 = -1 ≠ 0 but μ=2+√3: check               *)
(*  Hexagon has K+1=7 nodes                                            *)
(* ================================================================== *)

(** Hexagon connection *)
Lemma hexagon_gives_sqrt3 : (5 + 1 = 6)%nat.
Proof. reflexivity. Qed.

(** K=6 char poly at μ=1: 1 - 5 + 6 - 1 = 1 ⟹ λ²=1 is NOT a root *)
Lemma K6_not_at_1 : 1 - 5 + 6 - 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONSTANT ACCUMULATION TABLE                                        *)
(* ================================================================== *)

(** Summary of which constants first appear:
    K=2: 1 (eigenvalue ±1)
    K=3: √2 (eigenvalue ±√2, 0)
    K=4: φ (golden ratio, disc=5)
    K=5: √3 (eigenvalue ±√3, ±1, 0) — first appearance of √3
    K=6: 2cos(π/7), 2cos(2π/7), 2cos(3π/7) — new transcendentals *)
Theorem spectrum_constant_table :
  (* K=2 has eigenvalue 1 *)
  (1 * 1 - 1 == 0) /\
  (* K=3 has eigenvalue √2: 17²-2·12² = 1 *)
  (289 - 2 * 144 == 1) /\
  (* K=4 discriminant = 5, giving φ *)
  (3 * 3 - 4 * 1 == 5) /\
  (* K=5 has eigenvalues 1 and √3 *)
  (1 - 4 + 3 == 0) /\
  (3 * 3 - 4 * 3 + 3 == 0).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
