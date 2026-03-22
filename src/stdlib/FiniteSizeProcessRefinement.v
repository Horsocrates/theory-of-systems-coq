(** * FiniteSizeProcessRefinement.v -- Process Refinement and Finite-Size Matters
    Elements: Finite-size significance thresholds, correction magnitudes
    Roles:    Show that finite-size effects are quantitatively significant
    Rules:    At small N/K, corrections exceed 5% — refinement is necessary
    Status:   Stdlib
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa ZArith Lia.
Open Scope Q_scope.

(* ================================================================== *)
(*  SIGNIFICANCE THRESHOLDS                                            *)
(*  A correction is "significant" if > 5% of the quantity              *)
(* ================================================================== *)

Definition significant_threshold : Q := 1#20.

(* ================================================================== *)
(*  ISING: 43% correction at N=3                                      *)
(*  21952/50653 > 43/100: check 21952*100 > 43*50653                   *)
(*  2195200 > 2178079: YES                                             *)
(* ================================================================== *)

Lemma ising_N3_significant : (21952 * 100 > 43 * 50653)%Z.
Proof. lia. Qed.

Lemma ising_N3_above_threshold :
  (21952#50653) > significant_threshold.
Proof. unfold significant_threshold, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ISING: 25% correction at N=5                                      *)
(*  17210368/69343957 > 24/100: check 17210368*100 > 24*69343957       *)
(*  1721036800 > 1664254968: YES                                       *)
(* ================================================================== *)

Lemma ising_N5_significant : (17210368 * 100 > 24 * 69343957)%Z.
Proof. lia. Qed.

Lemma ising_N5_above_threshold :
  (17210368#69343957) > significant_threshold.
Proof. unfold significant_threshold, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  BOX: 6% correction at K=2                                         *)
(*  |correction_K2| = 79/1296 > 1/20 = 5%                             *)
(*  79/1296 > 1/20: check 79*20 > 1296: 1580 > 1296: YES              *)
(* ================================================================== *)

Lemma box_K2_significant : (79 * 20 > 1296)%Z.
Proof. lia. Qed.

Lemma box_K2_above_threshold : (79#1296) > significant_threshold.
Proof. unfold significant_threshold, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  WALK: P(3) = 5/16 = 31.25% of P(1) = 1/2                         *)
(*  5/16 > 5/100 trivially                                            *)
(* ================================================================== *)

Lemma walk_P3_above_threshold : (5#16) > significant_threshold.
Proof. unfold significant_threshold, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SPACING: 18% relative deviation at K=5                             *)
(*  101/560 > 1/20: check 101*20 > 560: 2020 > 560: YES               *)
(* ================================================================== *)

Lemma spacing_K5_above_threshold : (101#560) > significant_threshold.
Proof. unfold significant_threshold, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem finite_size_matters :
  (21952 * 100 > 43 * 50653)%Z /\
  (17210368 * 100 > 24 * 69343957)%Z /\
  (79 * 20 > 1296)%Z /\
  (79#1296) > significant_threshold /\
  (101#560) > significant_threshold.
Proof.
  split; [exact ising_N3_significant|].
  split; [exact ising_N5_significant|].
  split; [exact box_K2_significant|].
  split; [exact box_K2_above_threshold|].
  exact spacing_K5_above_threshold.
Qed.
