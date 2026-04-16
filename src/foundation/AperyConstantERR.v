(** * AperyConstantERR.v -- Apery constant zeta(3) in E/R/R framework

    STATUS: 18 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: April 2026

    ===================================================================
    THE APERY CONSTANT AS A PROCESS (NOT AN ELEMENT)
    ===================================================================

    zeta(3) = Sum_{n=1}^infty 1/n^3 ~ 1.2020569...

    Apery (1979) proved zeta(3) is IRRATIONAL. In P4 terms: zeta(3)
    cannot be a completed Element -- it has no representation as p/q
    for any integers p, q. But it IS a well-defined R-rule (a process
    generating rational approximations).

    This file makes explicit the E/R/R decomposition:

      E-formula (Elements, L1):
        Each partial sum s(N) = Sum_{n=1}^N 1/n^3 is a rational Q.
        Each is a concrete Element; the limit is not.

      R-formula (Roles, L4):
        zeta(3) appears as a coefficient in:
          - QED electron g-2 (alpha^3 contribution)
          - Stefan-Boltzmann integrand moments
          - BCS superconductivity gap ratios
          - Dirichlet L-function L(chi_0, 3)
        These are its ROLES in physics.

      R-formula (Rules, L5):
        Two convergent processes give the same limit:
          (a) Standard:  s(N+1) = s(N) + 1/(N+1)^3      (slow, 1/N^2 rate)
          (b) Apery:     a(N+1) = a(N) + (5/2)*(-1)^N
                                  /((N+1)^3 * C(2(N+1), N+1))  (fast)

    ===================================================================
    NEW INSIGHTS FROM THE THREE-FORMULA VIEW
    ===================================================================

    (1) IRRATIONALITY = NON-ELEMENT. Apery's theorem formally says
        zeta(3) cannot be packaged as a P4 Element. But it REMAINS
        a legitimate E/R/R object: the spectrum of rational partial
        sums plus a rule that generates them.

    (2) MULTIPLICITY OF R-RULES. The standard and Apery rules yield
        the same "limit" while differing as processes. Convergence
        rate is a property of the rule, not of the limit.

    (3) THREE-DIMENSIONAL SIGNATURE. zeta(3) naturally arises in
        3D inverse-cube sums (dipole-dipole, graviton propagator).
        The constant is the NUMERICAL SIGNATURE of cubic structure.

    ===================================================================
    VERIFIABLE NUMBERS
    ===================================================================

    Partial sums (exact rationals):
      s(1) = 1
      s(2) = 9/8       = 1.125
      s(3) = 251/216   ~ 1.1620
      s(4) = 2035/1728 ~ 1.1777
      s(5) = 256103/216000 ~ 1.1857

    Apery partial sums:
      a(1) = 5/4       = 1.250
      a(2) = 115/96    ~ 1.1979
      a(3) = 1039/864  ~ 1.2025

    Observed zeta(3) ~ 1.2020569.
    Apery a(3) matches observed to 0.04% after only 3 terms.
    Standard s(5) still has 1.3% error after 5 terms.
*)

From Stdlib Require Import QArith Qabs ZArith List PeanoNat Lia.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  SECTION 1: E-FORMULA -- partial sums as rational Elements       *)
(* ================================================================ *)

(** Reciprocal cube 1/n^3 as a Q value (0 for n=0). *)
Definition inv_cube (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | _ =>
      let q := inject_Z (Z.of_nat n) in
      1 / (q * q * q)
  end.

(** Standard partial sum s(N) = Sum_{n=1}^N 1/n^3. *)
Fixpoint zeta3_partial (N : nat) : Q :=
  match N with
  | 0%nat => 0
  | S n => zeta3_partial n + inv_cube (S n)
  end.

(* --- Concrete rational values --- *)

Theorem zeta3_s1 : zeta3_partial 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta3_s2 : zeta3_partial 2 == 9 # 8.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta3_s3 : zeta3_partial 3 == 251 # 216.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta3_s4 : zeta3_partial 4 == 2035 # 1728.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta3_s5 : zeta3_partial 5 == 256103 # 216000.
Proof. vm_compute. reflexivity. Qed.

(* --- Rational bounds --- *)

(** Rational bracket for s(5): 1185/1000 < s(5) < 1186/1000.
    Observed: s(5) = 256103/216000 ~ 1.1857. *)
Theorem zeta3_s5_above_1185 : (1185 # 1000) < zeta3_partial 5.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta3_s5_below_1186 : zeta3_partial 5 < 1186 # 1000.
Proof. vm_compute. reflexivity. Qed.

(** The standard series at N=5 is still BELOW 6/5 = 1.2
    (it needs ~10 terms to cross 1.2).  This shows slow convergence. *)
Theorem zeta3_s5_below_6_5 : zeta3_partial 5 < (6 # 5).
Proof. vm_compute. reflexivity. Qed.

(** Partial sum s(3) is strictly less than s(4): monotone increase. *)
Theorem zeta3_s3_below_s4 : zeta3_partial 3 < zeta3_partial 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SECTION 2: R-FORMULA RULES -- Apery acceleration                *)
(* ================================================================ *)

(** Apery partial sums (first 3), computed directly as rationals.
    These come from the identity
      zeta(3) = (5/2) * Sum_{n>=1} (-1)^(n-1) / (n^3 * C(2n, n))
    but we supply the values concretely so the file stays in pure Q. *)

(** a(1) = (5/2) * 1/(1 * 2) = 5/4. *)
Definition apery_1 : Q := 5 # 4.

(** a(2) = a(1) - (5/2) * 1/(8 * 6) = 5/4 - 5/96 = 115/96. *)
Definition apery_2 : Q := 115 # 96.

(** a(3) = a(2) + (5/2) * 1/(27 * 20) = 115/96 + 1/216 = 1039/864. *)
Definition apery_3 : Q := 1039 # 864.

(** Explicit relationship between successive Apery partial sums. *)
Theorem apery_2_value : apery_2 == apery_1 - (5 # 96).
Proof. unfold apery_1, apery_2. vm_compute. reflexivity. Qed.

Theorem apery_3_value : apery_3 == apery_2 + (1 # 216).
Proof. unfold apery_2, apery_3. vm_compute. reflexivity. Qed.

(* --- Apery converges much faster than standard --- *)

(** Apery a(2) is above 1.197 but below 1.198. *)
Theorem apery_2_above_1197 : (1197 # 1000) < apery_2.
Proof. unfold apery_2. vm_compute. reflexivity. Qed.

Theorem apery_2_below_1198 : apery_2 < 1198 # 1000.
Proof. unfold apery_2. vm_compute. reflexivity. Qed.

(** Apery a(3) is above 1.202 but below 1.203. *)
Theorem apery_3_above_1202 : (1202 # 1000) < apery_3.
Proof. unfold apery_3. vm_compute. reflexivity. Qed.

Theorem apery_3_below_1203 : apery_3 < 1203 # 1000.
Proof. unfold apery_3. vm_compute. reflexivity. Qed.

(* --- Apery vs standard: comparison at step 3 --- *)

(** After 3 terms, standard partial sum s(3) is well BELOW 1.2. *)
Theorem standard_s3_below_apery_3 : zeta3_partial 3 < apery_3.
Proof. unfold apery_3. vm_compute. reflexivity. Qed.

(** Standard s(3) ~ 1.1620, off from observed 1.2021 by ~3.3%. *)
Theorem standard_s3_below_12 : zeta3_partial 3 < (12 # 10).
Proof. vm_compute. reflexivity. Qed.

(** Apery a(3) is within 0.001 of the observed value 1.2020569. *)
Theorem apery_3_brackets_observed :
  (1202 # 1000) < apery_3 /\ apery_3 < (1203 # 1000).
Proof.
  split. { apply apery_3_above_1202. } apply apery_3_below_1203.
Qed.

(* ================================================================ *)
(*  SECTION 3: GRAND THEOREM                                         *)
(* ================================================================ *)

(** All the Apery facts that can be machine-checked in Q. *)
Theorem apery_constant_err :
  (* E-formula: partial sums as exact rationals *)
  zeta3_partial 1 == 1 /\
  zeta3_partial 2 == 9 # 8 /\
  zeta3_partial 3 == 251 # 216 /\
  zeta3_partial 5 == 256103 # 216000 /\
  (* Standard series is monotone *)
  zeta3_partial 3 < zeta3_partial 4 /\
  (* Standard s(5) is still below 6/5 -- slow convergence *)
  zeta3_partial 5 < (6 # 5) /\
  (* Apery acceleration: 3 rational values *)
  apery_1 == 5 # 4 /\
  apery_2 == 115 # 96 /\
  apery_3 == 1039 # 864 /\
  (* Apery a(3) brackets the observed value *)
  (1202 # 1000) < apery_3 /\
  apery_3 < 1203 # 1000 /\
  (* Apery already outperforms standard at N=3 *)
  zeta3_partial 3 < apery_3.
Proof.
  split. { apply zeta3_s1. }
  split. { apply zeta3_s2. }
  split. { apply zeta3_s3. }
  split. { apply zeta3_s5. }
  split. { apply zeta3_s3_below_s4. }
  split. { apply zeta3_s5_below_6_5. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { apply apery_3_above_1202. }
  split. { apply apery_3_below_1203. }
  apply standard_s3_below_apery_3.
Qed.

(**
   ==================================================================
   VERIFIABLE PREDICTIONS (cross-check with published data)
   ==================================================================

   (1) STANDARD SERIES CONVERGENCE RATE.
       Error after N terms is approximately 1/(2 N^2) (integral test).
       N=5:  expected error ~1/50 = 0.02, observed ~0.016 (matches).
       Check: tabulate 1 + 1/8 + ... + 1/N^3 for large N.

   (2) APERY ACCELERATION FACTOR.
       After 3 terms Apery is correct to 0.04%.
       After 3 terms standard is correct to 3.3%.
       Ratio: Apery ~80x better per term.
       Check: any symbolic algebra package verifies this.

   (3) zeta(3) IN PHYSICS.
       Electron g-2 in QED: a_e = alpha/(2 pi) - 0.328 * (alpha/pi)^2
                                + 1.181 * (alpha/pi)^3 - ...
       The coefficient 1.181 contains zeta(3) through
         A_3 = 83/72 * pi^2 * zeta(3) + ...
       This is CALCULATED, not fitted. Match with measurements:
         experiment: a_e = 0.00115965218...
         theory:     a_e = 0.00115965218... (matches to 10 digits).

   (4) STEFAN-BOLTZMANN RELATED.
       Integral int_0^infty x^2 / (e^x - 1) dx = 2 * zeta(3).
       This is the integrand for photon number density in black-body
       radiation. In cosmology gives photon-to-baryon ratio.

   ==================================================================
   CONNECTION TO OUR FRAMEWORK
   ==================================================================

   The Apery constant highlights what P4 allows vs. forbids:

     ALLOWED:  every partial sum s(N) as an Element
               the Apery rule as an R-formula (process)
               the "ROLES" of zeta(3) in physics (as coefficients)
               rational brackets like [1.202, 1.203]

     FORBIDDEN: the "completed value" zeta(3) as a single Element
                (Apery's irrationality proof blocks any p/q form)
                any claim of equality zeta(3) = <specific rational>

   E/R/R view: zeta(3) exists as a PROCESS and as a ROLE, but not
   as an ELEMENT. This is exactly what P4 predicts for irrationals.
*)
