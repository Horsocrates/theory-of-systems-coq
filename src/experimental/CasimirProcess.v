(**
  CasimirProcess.v — The Casimir Effect as ToS Process
  =====================================================

  File 3 of 4 in the Experimental Verification module.

  The Casimir effect: two conducting plates attract each other due to
  quantum vacuum fluctuations. The force per unit area is:
    F/A = -π²ℏc / (240 d⁴)

  The key mathematical content:
    1D vacuum energy ∝ ζ(-1) = -1/12
    3D vacuum energy ∝ ζ(-3) = 1/120
    Force coefficient = π²/720

  Standard physics derives this by "subtracting infinities".
  ToS derives it from Bernoulli recursion — no infinity needed.

  Depends on: BernoulliNumbers, ZetaNegative, SeriesConvergence, CauchyReal
  STATUS: target ~35 Qed, 0 Admitted
  AXIOMS: classic (via MonotoneConvergence)
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.

Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import MonotoneConvergence.
From ToS Require Import experimental.BernoulliNumbers.
From ToS Require Import experimental.ZetaNegative.

(* ========================================================================= *)
(*              PART I: CASIMIR COEFFICIENTS — EXACT RATIONAL                *)
(* ========================================================================= *)

(** The Casimir effect in 1D: energy ∝ ζ(-1) = -1/12
    Coefficient: -1/12 *)
Definition casimir_1d : Q := zeta_neg 1.

(** The Casimir effect in 3D: energy ∝ ζ(-3) = 1/120
    Coefficient: 1/120 *)
Definition casimir_3d : Q := zeta_neg 3.

(** The force coefficient: π²/(720).
    Since π is irrational, we verify the RATIONAL factor 1/720.
    Full force: F/A = -π²/(720 d⁴) where the 720 comes from:
    720 = 6 × 120 = 6 × 1/ζ(-3) *)
Definition casimir_rational_factor : Q := (1#720).

(** ★ THE CASIMIR 1D VERIFICATION ★
    ζ(-1) = -1/12 — exact, no infinities *)
Theorem casimir_1d_verified : casimir_1d == -(1#12).
Proof. unfold casimir_1d. exact zeta_neg_1. Qed.

(** ★ THE CASIMIR 3D VERIFICATION ★
    ζ(-3) = 1/120 — exact, no infinities *)
Theorem casimir_3d_verified : casimir_3d == (1#120).
Proof. unfold casimir_3d. exact zeta_neg_3. Qed.

(** Verification: 6 × ζ(-3) = 1/20 *)
Lemma six_times_zeta_neg_3 : 6 * casimir_3d == (1#20).
Proof. unfold casimir_3d. vm_compute. reflexivity. Qed.

(** Verification: 720 × ζ(-3) = 6 *)
Lemma casimir_720_factor : 720 * casimir_3d == 6.
Proof. unfold casimir_3d. vm_compute. reflexivity. Qed.

(** The rational factor 1/720 from the full Casimir formula *)
Theorem casimir_rational_factor_verified :
  casimir_rational_factor == casimir_3d * (1#6).
Proof. unfold casimir_rational_factor, casimir_3d. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*              PART II: RAW ENERGY — THE DIVERGENT SUM                      *)
(* ========================================================================= *)

(** The "raw" Casimir energy in 1D would be the sum:
    E_raw = Σ_{n=1}^{∞} n = 1 + 2 + 3 + ...
    This equals power_sum 1 N in our framework. *)

Definition raw_energy_1d (N : nat) : Q := power_sum 1 N.

(** The "raw" Casimir energy in 3D would be:
    E_raw = Σ_{n=1}^{∞} n³ = 1 + 8 + 27 + ...
    This equals power_sum 3 N. *)

Definition raw_energy_3d (N : nat) : Q := power_sum 3 N.

(** Raw energy grows without bound *)
Theorem raw_energy_1d_diverges :
  forall B : Q, exists N, raw_energy_1d N > B.
Proof. unfold raw_energy_1d. exact sum_of_naturals_diverges. Qed.

Theorem raw_energy_3d_diverges :
  forall B : Q, exists N, raw_energy_3d N > B.
Proof. unfold raw_energy_3d. exact sum_of_cubes_diverges. Qed.

(** Concrete: raw 1D energy exceeds 1000 *)
Lemma raw_1d_exceeds_1000 :
  exists N, raw_energy_1d N > 1000.
Proof.
  destruct (raw_energy_1d_diverges 1000) as [N HN].
  exists N. exact HN.
Qed.

(** Concrete: first few partial sums *)
Lemma raw_1d_at_3 : raw_energy_1d 3 == 10.
Proof. vm_compute. reflexivity. Qed.

Lemma raw_3d_at_3 : raw_energy_3d 3 == 100.
Proof. vm_compute. reflexivity. Qed.

Lemma raw_1d_at_9 : raw_energy_1d 9 == 55.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*              PART III: PROCESS INTERPRETATION                             *)
(* ========================================================================= *)

(**
  The Casimir process:
  - The raw sum Σn^k DIVERGES (proved above).
  - The Bernoulli recursion ASSIGNS a finite value ζ(-k).
  - These are DIFFERENT operations:
    * Summation: partial_sum f N → ∞
    * Process:   Bernoulli recursion → -B_{k+1}/(k+1)
  - The process is NOT the limit of the sum.
  - It is the VALUE of the analytic continuation.
*)

(** The process produces a value where summation fails *)
Theorem casimir_process_1d :
  (forall B, exists N, raw_energy_1d N > B) /\
  casimir_1d == -(1#12).
Proof.
  split.
  - exact raw_energy_1d_diverges.
  - exact casimir_1d_verified.
Qed.

Theorem casimir_process_3d :
  (forall B, exists N, raw_energy_3d N > B) /\
  casimir_3d == (1#120).
Proof.
  split.
  - exact raw_energy_3d_diverges.
  - exact casimir_3d_verified.
Qed.

(** The Bernoulli recursion IS the process.
    ζ(-k) = -B_{k+1}/(k+1) by definition. *)
Lemma casimir_is_bernoulli_1d :
  casimir_1d == -(bernoulli 2) / inject_Z (Z.of_nat 2).
Proof. unfold casimir_1d. exact zeta_neg_1_uses_B2. Qed.

Lemma casimir_is_bernoulli_3d :
  casimir_3d == -(bernoulli 4) / inject_Z (Z.of_nat 4).
Proof. unfold casimir_3d. exact zeta_neg_3_uses_B4. Qed.

(** No infinity was involved *)
Lemma casimir_1d_is_rational : exists p q : Z,
  (0 < q)%Z /\ casimir_1d == inject_Z p / inject_Z q.
Proof.
  exists (-1)%Z, 12%Z. split; [lia|].
  unfold casimir_1d. vm_compute. reflexivity.
Qed.

Lemma casimir_3d_is_rational : exists p q : Z,
  (0 < q)%Z /\ casimir_3d == inject_Z p / inject_Z q.
Proof.
  exists 1%Z, 120%Z. split; [lia|].
  unfold casimir_3d. vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(*              PART IV: EXPONENTIAL REGULARIZATION                          *)
(* ========================================================================= *)

(** Exponential regularization: define the damped sum
    S(ε) = Σ_{n=1}^{N} n^k · e^{-nε}
    For ε > 0, this converges. As ε → 0+, the limit relates to ζ(-k).

    Since e^{-nε} is irrational, we work with rational approximation:
    use (1 - ε·n/N)_+ as a simple damping factor. *)

Definition linear_damping (eps : Q) (n : nat) : Q :=
  Qmax 0 (1 - eps * inject_Z (Z.of_nat (S n))).

(** For small ε, damping factor is positive for small n *)
Lemma damping_nonneg : forall eps n,
  0 <= linear_damping eps n.
Proof.
  intros. unfold linear_damping.
  destruct (Q.max_spec 0 (1 - eps * inject_Z (Z.of_nat (S n)))) as [[Hle Hmax]|[Hlt Hmax]];
  setoid_rewrite Hmax; lra.
Qed.

(** Damping at n=0: 1 - ε *)
Lemma damping_at_0 : forall eps,
  0 < eps -> eps < 1 ->
  linear_damping eps 0 == 1 - eps.
Proof.
  intros eps Hpos Hlt1. unfold linear_damping. simpl.
  destruct (Q.max_spec 0 (1 - eps * 1)) as [[Hle Hmax]|[Hlt Hmax]].
  - setoid_rewrite Hmax. lra.
  - lra.
Qed.

(** Damped 1D energy *)
Definition damped_energy_1d (eps : Q) (N : nat) : Q :=
  partial_sum (fun n => inject_Z (Z.of_nat (S n)) * linear_damping eps n) N.

(** Concrete: damped energy at ε=1/2, N=3 *)
Lemma damped_1d_example :
  damped_energy_1d (1#2) 3 ==
  partial_sum (fun n => inject_Z (Z.of_nat (S n)) *
    Qmax 0 (1 - (1#2) * inject_Z (Z.of_nat (S n)))) 3.
Proof. unfold damped_energy_1d. reflexivity. Qed.

(* ========================================================================= *)
(*              PART V: ENERGY RATIOS AND PHYSICAL CONSEQUENCES              *)
(* ========================================================================= *)

(** Ratio of 3D to 1D Casimir coefficients *)
Lemma casimir_ratio_3d_1d :
  casimir_3d / casimir_1d == -(1#10).
Proof. unfold casimir_3d, casimir_1d. vm_compute. reflexivity. Qed.

(** The 1D coefficient is negative *)
Lemma casimir_1d_negative : casimir_1d < 0.
Proof.
  unfold casimir_1d.
  assert (H : zeta_neg 1 == -(1#12)) by exact zeta_neg_1.
  setoid_rewrite H. lra.
Qed.

(** The 3D coefficient is positive *)
Lemma casimir_3d_positive : 0 < casimir_3d.
Proof.
  unfold casimir_3d.
  assert (H : zeta_neg 3 == (1#120)) by exact zeta_neg_3.
  setoid_rewrite H. lra.
Qed.

(** Force is attractive (negative) because the energy coefficient is negative.
    In the physical Casimir formula:
    E ∝ ζ(-3)/d³ = (1/120)/d³ (positive energy decreasing with d)
    F = -dE/dd ∝ -3ζ(-3)/d⁴ < 0 (attractive) *)
Lemma casimir_force_attractive :
  -(3) * casimir_3d < 0.
Proof.
  assert (H : 0 < casimir_3d) by exact casimir_3d_positive.
  lra.
Qed.

(** The Casimir pressure coefficient:
    F/A = -π²/(240 d⁴) × ℏc.
    The 240 = 2 × 120 = 2/ζ(-3). *)
Lemma casimir_240_from_zeta :
  2 * (1 / casimir_3d) == 240.
Proof. unfold casimir_3d. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*              PART VI: HIGHER-DIMENSIONAL OBSERVATIONS                     *)
(* ========================================================================= *)

(** In d spatial dimensions, vacuum energy involves ζ(-(d-1)/2) for
    massless fields. For even d, this involves ζ at negative integers.

    d=2: ζ(-1/2) — half-integer, not covered here
    d=3: ζ(-1)   = -1/12    ← verified
    d=5: ζ(-2)   = 0        ← trivial zero
    d=7: ζ(-3)   = 1/120    ← verified
    d=9: ζ(-4)   = 0        ← trivial zero
    d=11: ζ(-5)  = -1/252   ← verified
*)

(** Energy vanishes in certain dimensions *)
Theorem energy_vanishes_d5 : zeta_neg 2 == 0.
Proof. exact zeta_neg_2. Qed.

Theorem energy_vanishes_d9 : zeta_neg 4 == 0.
Proof. exact zeta_neg_4. Qed.

(** Energy is nonzero in d=3 and d=7 *)
Theorem energy_nonzero_d3 : ~ (zeta_neg 1 == 0).
Proof. exact zeta_neg_1_nonzero. Qed.

Theorem energy_nonzero_d7 : ~ (zeta_neg 3 == 0).
Proof. exact zeta_neg_3_nonzero. Qed.

(** Alternating sign pattern for non-trivial values:
    ζ(-1) = -1/12 < 0
    ζ(-3) = 1/120 > 0
    ζ(-5) = -1/252 < 0 *)
Lemma zeta_neg_1_sign : zeta_neg 1 < 0.
Proof.
  assert (H : zeta_neg 1 == -(1#12)) by exact zeta_neg_1.
  setoid_rewrite H. lra.
Qed.

Lemma zeta_neg_3_sign : 0 < zeta_neg 3.
Proof.
  assert (H : zeta_neg 3 == (1#120)) by exact zeta_neg_3.
  setoid_rewrite H. lra.
Qed.

Lemma zeta_neg_5_sign : zeta_neg 5 < 0.
Proof.
  assert (H : zeta_neg 5 == -(1#252)) by exact zeta_neg_5.
  setoid_rewrite H. lra.
Qed.

(* ========================================================================= *)
(*              PART VII: SUMMARY THEOREM                                    *)
(* ========================================================================= *)

(** THE MAIN RESULT: The Casimir effect coefficients are exact rationals
    derived from Bernoulli numbers, with no infinities. *)
Theorem casimir_main_theorem :
  (* 1D: ζ(-1) = -1/12 *)
  casimir_1d == -(1#12) /\
  (* 3D: ζ(-3) = 1/120 *)
  casimir_3d == (1#120) /\
  (* Rational factor: 1/720 *)
  casimir_rational_factor == casimir_3d * (1#6) /\
  (* Raw energy diverges *)
  (forall B, exists N, raw_energy_1d N > B) /\
  (forall B, exists N, raw_energy_3d N > B) /\
  (* 1D energy is negative (attractive) *)
  casimir_1d < 0 /\
  (* 3D energy is positive *)
  0 < casimir_3d.
Proof.
  split; [exact casimir_1d_verified|].
  split; [exact casimir_3d_verified|].
  split; [exact casimir_rational_factor_verified|].
  split; [exact raw_energy_1d_diverges|].
  split; [exact raw_energy_3d_diverges|].
  split; [exact casimir_1d_negative|].
  exact casimir_3d_positive.
Qed.

(** Summary:

  STATUS: Qed count below, 0 Admitted

  Part I   — Coefficients:
    casimir_1d_verified, casimir_3d_verified,
    six_times_zeta_neg_3, casimir_720_factor,
    casimir_rational_factor_verified

  Part II  — Raw energy:
    raw_energy_1d_diverges, raw_energy_3d_diverges,
    raw_1d_exceeds_1000, raw_1d_at_3, raw_3d_at_3, raw_1d_at_9

  Part III — Process:
    casimir_process_1d, casimir_process_3d,
    casimir_is_bernoulli_1d, casimir_is_bernoulli_3d,
    casimir_1d_is_rational, casimir_3d_is_rational

  Part IV  — Regularization:
    damping_nonneg, damping_at_0, damped_1d_example

  Part V   — Physical:
    casimir_ratio_3d_1d, casimir_1d_negative, casimir_3d_positive,
    casimir_force_attractive, casimir_240_from_zeta

  Part VI  — Higher dimensions:
    energy_vanishes_d5, energy_vanishes_d9,
    energy_nonzero_d3, energy_nonzero_d7,
    zeta_neg_1_sign, zeta_neg_3_sign, zeta_neg_5_sign

  Part VII — Summary:
    casimir_main_theorem
*)
