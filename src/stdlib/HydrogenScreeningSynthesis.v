(** * HydrogenScreeningSynthesis.v — Grand synthesis of screening phenomena
    Elements: screened_ratio, symmetry_breaking, phase transition, reentrance
    Roles:    Unifies screening (File 4), breaking (File 5), transition (File 6)
    Rules:    Non-monotone ratio + peaked breaking + reentrant transition = full picture
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Qabs Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.HydrogenScreening.
From ToS Require Import stdlib.HydrogenSymmetryBreaking.
From ToS Require Import stdlib.HydrogenPhaseTransition.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Screening + Breaking consistency                           *)
(* ================================================================== *)

Lemma synthesis_no_screening_no_breaking :
  screened_ratio 0 == 2500#10000 /\ symmetry_breaking 0 == 0.
Proof.
  split.
  - exact screened_ratio_0.
  - exact breaking_zero.
Qed.

Lemma synthesis_minimum_maximum :
  screened_ratio 10 == 2450#10000 /\ symmetry_breaking 10 == 50#10000.
Proof.
  split.
  - exact screened_ratio_10.
  - exact breaking_max.
Qed.

(* ================================================================== *)
(*  Part II: Full picture — monotonicity + phase + bounds              *)
(* ================================================================== *)

Lemma synthesis_decreasing_phase :
  screened_ratio 0 > screened_ratio 1 /\ is_symmetric 0 = true.
Proof.
  split.
  - exact screening_decreases_0_1.
  - exact phase_zero_symmetric.
Qed.

Lemma synthesis_broken_phase :
  screened_ratio 10 < screened_ratio 5 /\ is_symmetric 10 = false.
Proof.
  split.
  - exact minimum_at_10.
  - exact phase_10_broken.
Qed.

Lemma synthesis_recovery :
  screened_ratio 10 < screened_ratio 20 /\ is_symmetric 50 = true.
Proof.
  split.
  - exact screening_increases_10_20.
  - exact phase_50_symmetric.
Qed.

(* ================================================================== *)
(*  Part III: Grand reentrance theorem                                 *)
(* ================================================================== *)

Lemma synthesis_reentrant :
  exists r1 r2 r3 : nat,
    (r1 < r2)%nat /\ (r2 < r3)%nat /\
    is_symmetric r1 = true /\
    is_symmetric r2 = false /\
    is_symmetric r3 = true.
Proof. exact reentrant_transition. Qed.

Lemma synthesis_breaking_bounded :
  symmetry_breaking 10 < 1#100.
Proof. exact breaking_bounded_max. Qed.

Lemma synthesis_large_limit :
  Qabs (screened_ratio 50 - (1#4)) < 1#100.
Proof. exact limit_large_screening_close. Qed.
