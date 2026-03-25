(** * NISTSynthesis.v -- Grand synthesis of NIST comparison results
    Elements: nist_grand_synthesis, prediction_quality
    Roles:    Combines NIST_Splitting and ScreeningFit results
    Rules:    Imports NIST_Splitting, ScreeningFit. All Qed, no Admitted.
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.NIST_Splitting.
From ToS Require Import stdlib.ScreeningFit.

Open Scope Q_scope.

(* ================================================================== *)
(*  PREDICTION QUALITY METRICS                                          *)
(* ================================================================== *)

(** All predictions are positive *)
Lemma all_predictions_positive :
  our_delta_He > 0 /\ our_delta_Li > 0 /\ our_delta_Be > 0.
Proof.
  rewrite our_delta_He_val, our_delta_Li_val, our_delta_Be_val.
  split; [| split]; lra.
Qed.

(** All NIST values are positive *)
Lemma all_nist_positive :
  nist_splitting_He > 0 /\ nist_splitting_Li > 0 /\ nist_splitting_Be > 0.
Proof.
  unfold nist_splitting_He, nist_splitting_Li, nist_splitting_Be.
  split; [| split]; lra.
Qed.

(** He error < Be is trivially true since Be error = 0 doesn't help.
    But He error < Li error is meaningful *)
Lemma he_better_than_li : Qabs he_diff < Qabs li_diff.
Proof. exact error_grows_with_z. Qed.

(** Best prediction: Be (exact) *)
Lemma best_prediction_be : nist_splitting_Be == our_delta_Be.
Proof. exact be_exact_match. Qed.

(* ================================================================== *)
(*  SCREENING MODEL EVALUATION                                         *)
(* ================================================================== *)

(** Screening works for Z=2 and Z=4, fails for Z=3 *)
Theorem screening_pattern :
  Qabs he_diff < 1#100 /\
  nist_splitting_Be == our_delta_Be /\
  Qabs li_diff > 1#1000.
Proof. exact screening_verdict. Qed.

(** Predictions are in right ballpark: all between 0 and 1 *)
Lemma predictions_bounded :
  our_delta_He < 1 /\ our_delta_Li < 1 /\ our_delta_Be < 1.
Proof.
  rewrite our_delta_He_val, our_delta_Li_val, our_delta_Be_val.
  split; [| split]; lra.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

(** Complete NIST comparison story *)
Theorem nist_grand_synthesis :
  (* He: prediction close to NIST *)
  Qabs he_diff < 1 # 100 /\
  (* Be: exact match *)
  nist_splitting_Be == our_delta_Be /\
  (* Li: model needs refinement *)
  our_delta_Li < nist_splitting_Li /\
  (* Error pattern: He < Li *)
  Qabs he_diff < Qabs li_diff.
Proof.
  split; [| split; [| split]].
  - exact he_close_to_nist.
  - exact be_exact_match.
  - exact li_underprediction.
  - exact error_grows_with_z.
Qed.

Theorem prediction_quality :
  (* All positive *)
  our_delta_He > 0 /\
  our_delta_Li > 0 /\
  (* Best: Be exact *)
  nist_splitting_Be == our_delta_Be /\
  (* Good: He close *)
  Qabs he_diff < 1#100.
Proof.
  rewrite our_delta_He_val, our_delta_Li_val.
  split; [| split; [| split]].
  - lra.
  - lra.
  - exact be_exact_match.
  - exact he_close_to_nist.
Qed.
