(** * AnomalyExhaustive.v -- SM passes; a SAMPLE of alternatives fails -- NOT an exhaustive search
       (honesty rollback June 2026: "exhaustive search" was an over-claim; the TRUE box-exhaustive
        scan with per-rule counts lives in AnomalyLatticeDial.v: 1317 -> 11 -> exactly {SM, u<->d swap})
    Elements: check_anomaly, alt_test_*, sm_unique_among_tested
    Roles:    Verify SM passes linear+cubic; a handful of natural alternatives fail
    Rules:    linear+cubic with Y1=1/6 fixed; ~5 tested alternatives (a SAMPLE, not a scan)
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026  (exhaustiveness-honesty rollback: June 2026)

    HONEST STATUS: this file proves (a) the SM charges satisfy the linear+cubic conditions and
    (b) a SAMPLE of ~5 natural alternative assignments (Y1 fixed at 1/6) fails the cubic.  It
    does NOT establish exhaustiveness or uniqueness: linear+cubic ALONE leave an 11-point
    solution set even on the [-8..8]/6 lattice (AnomalyLatticeDial.dial_grav_cubic — incl.
    exotics like (-1,-1,0,0)/6); the pinning to exactly {SM, u<->d swap} needs the NON-ABELIAN
    conditions [SU(3)]^2 U(1) and [SU(2)]^2 U(1) — see AnomalyLatticeDial.dial_all_exact and
    the algebraic forcing in ChargeLatticeTheory.v.  The theorem name sm_unique_among_tested
    states the honest scope: among TESTED.
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  ANOMALY CONDITIONS (replicated from ChiralAnomalyUniqueness)        *)
(* ================================================================== *)

(** For [3,2,1] content with multiplicities 6,3,3,2,1:
    Linear: 6Y1 + 3Y2 + 3Y3 + 2Y4 + Y5 = 0
    Cubic:  6Y1^3 + 3Y2^3 + 3Y3^3 + 2Y4^3 + Y5^3 = 0 *)

Definition linear_cond (Y1 Y2 Y3 Y4 Y5 : Q) : Prop :=
  6*Y1 + 3*Y2 + 3*Y3 + 2*Y4 + Y5 == 0.

Definition cubic_cond (Y1 Y2 Y3 Y4 Y5 : Q) : Prop :=
  6*Y1*Y1*Y1 + 3*Y2*Y2*Y2 + 3*Y3*Y3*Y3 + 2*Y4*Y4*Y4 + Y5*Y5*Y5 == 0.

Definition check_anomaly (Y1 Y2 Y3 Y4 : Q) : Prop :=
  let Y5 := -(6*Y1 + 3*Y2 + 3*Y3 + 2*Y4) in
  linear_cond Y1 Y2 Y3 Y4 Y5 /\
  cubic_cond Y1 Y2 Y3 Y4 Y5.

(* ================================================================== *)
(*  SM SOLUTION                                                         *)
(* ================================================================== *)

(** SM charges: Y = (1/6, -2/3, 1/3, -1/2, 1) *)
Lemma sm_Y5_value :
  -(6*(1#6) + 3*(-(2#3)) + 3*(1#3) + 2*(-(1#2))) == 1.
Proof. ring. Qed.

Theorem sm_satisfies_linear :
  linear_cond (1#6) (-(2#3)) (1#3) (-(1#2)) 1.
Proof. unfold linear_cond. ring. Qed.

Theorem sm_satisfies_cubic :
  cubic_cond (1#6) (-(2#3)) (1#3) (-(1#2)) 1.
Proof. unfold cubic_cond. ring. Qed.

Theorem sm_is_solution :
  check_anomaly (1#6) (-(2#3)) (1#3) (-(1#2)).
Proof.
  unfold check_anomaly. split.
  - unfold linear_cond. ring.
  - unfold cubic_cond. ring.
Qed.

(* ================================================================== *)
(*  ALL-EQUAL CHARGES: TRIVIAL                                          *)
(* ================================================================== *)

(** If Y1 = Y2 = Y3 = Y4 = Y5 = Y (all equal charges):
    Linear: (6+3+3+2+1)*Y = 15*Y = 0 -> Y = 0, all charges zero. *)

Theorem all_equal_trivial : forall Y,
  linear_cond Y Y Y Y Y ->
  Y == 0.
Proof.
  intros Y H. unfold linear_cond in H. lra.
Qed.

(* ================================================================== *)
(*  SYSTEMATIC ALTERNATIVES WITH Y1 = 1/6                               *)
(* ================================================================== *)

(** Test: Y2=0, Y3=0, Y4=0 -> Y5 = -1 *)
(** Cubic: 6*(1/6)^3 + 0 + 0 + 0 + (-1)^3 = 1/36 - 1 != 0 *)
Lemma alt_000_fails_cubic :
  ~ cubic_cond (1#6) 0 0 0 (-1).
Proof.
  unfold cubic_cond. intro H.
  assert (Habs : 6 * (1 # 6) * (1 # 6) * (1 # 6) +
    3 * 0 * 0 * 0 + 3 * 0 * 0 * 0 + 2 * 0 * 0 * 0 +
    -1 * -1 * -1 == -(35 # 36)) by ring.
  lra.
Qed.

(** Test: Y2=-1, Y3=1, Y4=0 -> Y5 = -(6*(1/6) + 3*(-1) + 3*1 + 0) = -1 *)
Lemma alt_m1_1_0_Y5 :
  -(6*(1#6) + 3*(-1) + 3*1 + 2*0) == -1.
Proof. ring. Qed.

Lemma alt_m1_1_0_fails_cubic :
  ~ cubic_cond (1#6) (-1) 1 0 (-1).
Proof.
  unfold cubic_cond. intro H.
  assert (Habs : 6 * (1 # 6) * (1 # 6) * (1 # 6) +
    3 * -1 * -1 * -1 + 3 * 1 * 1 * 1 + 2 * 0 * 0 * 0 +
    -1 * -1 * -1 == -(35 # 36)) by ring.
  lra.
Qed.

(** Test: Y2=1/3, Y3=-1/3, Y4=0 -> Y5 = -(6*(1/6) + 0 + 0 + 0) = -1 *)
Lemma alt_third_mthird_0_fails_cubic :
  ~ cubic_cond (1#6) (1#3) (-(1#3)) 0 (-1).
Proof.
  unfold cubic_cond. intro H.
  assert (Habs : 6 * (1 # 6) * (1 # 6) * (1 # 6) +
    3 * (1#3) * (1#3) * (1#3) + 3 * (-(1#3)) * (-(1#3)) * (-(1#3)) +
    2 * 0 * 0 * 0 + -1 * -1 * -1 == -(35 # 36)) by ring.
  lra.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

(** With Y1 = 1/6 fixed, the SM charges are the UNIQUE solution
    among tested alternatives with all |Yi| <= 1 and Yi in Z/6.
    A complete enumeration over all Z/6-valued charges has ~7^4 = 2401
    cases. We test the most natural alternatives. *)

Theorem sm_unique_among_tested :
  (* SM satisfies both conditions *)
  check_anomaly (1#6) (-(2#3)) (1#3) (-(1#2)) /\
  (* All-equal forces Y = 0 *)
  (forall Y, linear_cond Y Y Y Y Y -> Y == 0) /\
  (* Alternatives fail cubic *)
  ~ cubic_cond (1#6) 0 0 0 (-1) /\
  ~ cubic_cond (1#6) (-1) 1 0 (-1) /\
  ~ cubic_cond (1#6) (1#3) (-(1#3)) 0 (-1).
Proof.
  split; [|split; [|split; [|split]]].
  - exact sm_is_solution.
  - exact all_equal_trivial.
  - exact alt_000_fails_cubic.
  - exact alt_m1_1_0_fails_cubic.
  - exact alt_third_mthird_0_fails_cubic.
Qed.
