(** * TwoCenterVerify.v -- Verification of two-center integral values
    Elements: overlap_rational, kinetic_rational, nuclear_rational,
              s_pade_at_1, s_pade_at_2
    Roles:    Cross-check all integrals are consistent rational values
    Rules:    All via vm_compute + reflexivity, additional s_pade checks
    Status:   Stdlib/molecule
    STATUS: 9 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.molecule.TwoCenterIntegrals.

Open Scope Q_scope.

(* ================================================================== *)
(*  CROSS-VERIFICATION OF ALL INTEGRALS AT α=1, R=3/2, s=7/31        *)
(* ================================================================== *)

(** Verify overlap integral is a proper fraction *)
Lemma overlap_rational : overlap_AB 1 (3#2) (7#31) == 91#124.
Proof. exact S_AB_value. Qed.

(** Verify kinetic integral *)
Lemma kinetic_rational : kinetic_AB 1 (3#2) (7#31) == 49#248.
Proof. exact T_AB_value. Qed.

(** Verify nuclear attraction integral *)
Lemma nuclear_rational : nuclear_AB 1 (3#2) (7#31) == -(35#62).
Proof. exact V_AB_value. Qed.

(** Verify one-center integrals *)
Lemma onecenter_kinetic : kinetic_AA 1 == 1#2.
Proof. exact T_AA_value. Qed.

Lemma onecenter_nuclear : nuclear_AA 1 == -(1).
Proof. exact V_AA_value. Qed.

(* ================================================================== *)
(*  s_pade AT OTHER R VALUES                                           *)
(* ================================================================== *)

(** s_pade(1,1) = (12-6+1)/(12+6+1) = 7/19 *)
Lemma s_pade_at_1 : s_pade 1 1 == 7#19.
Proof. unfold s_pade. vm_compute. reflexivity. Qed.

(** s_pade(1,2) = (12-12+4)/(12+12+4) = 4/28 = 1/7 *)
Lemma s_pade_at_2 : s_pade 1 2 == 1#7.
Proof. unfold s_pade. vm_compute. reflexivity. Qed.

(** s_pade monotonically decreasing in R: s(1,1) > s(1,3/2) > s(1,2) *)
Lemma s_pade_decreasing :
  s_pade 1 2 < s_pade 1 (3#2) /\ s_pade 1 (3#2) < s_pade 1 1.
Proof.
  rewrite s_pade_at_2, s_value, s_pade_at_1.
  split; lra.
Qed.

(** All s_pade values are between 0 and 1 *)
Lemma s_pade_range :
  0 < s_pade 1 1 /\ s_pade 1 1 < 1 /\
  0 < s_pade 1 2 /\ s_pade 1 2 < 1.
Proof.
  rewrite s_pade_at_1, s_pade_at_2.
  repeat split; lra.
Qed.
