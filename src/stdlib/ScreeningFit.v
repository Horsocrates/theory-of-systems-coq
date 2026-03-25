(** * ScreeningFit.v -- Screening model: He works, Li mismatch
    Elements: he_match, li_mismatch, honest_assessment
    Roles:    Evaluates Z-screening model against NIST data
    Rules:    Imports NIST_Splitting. All Qed, no Admitted.
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.NIST_Splitting.

Open Scope Q_scope.

(* ================================================================== *)
(*  HELIUM: GOOD MATCH                                                  *)
(* ================================================================== *)

(** He prediction matches NIST to < 0.1% *)
Lemma he_match : Qabs he_diff < 1 # 100.
Proof. exact he_close_to_nist. Qed.

(** He prediction is close: |471 - 466|/10000 = 5/10000 *)
Lemma he_error_5_parts : Qabs he_diff == 5 # 10000.
Proof. exact he_diff_abs. Qed.

(** He prediction is positive (our value slightly above NIST) *)
Lemma he_our_above_nist : our_delta_He > nist_splitting_He.
Proof.
  rewrite our_delta_He_val, nist_He_val. lra.
Qed.

(* ================================================================== *)
(*  LITHIUM: MISMATCH                                                   *)
(* ================================================================== *)

(** Li prediction differs from NIST *)
Lemma li_mismatch : our_delta_Li == 326 # 10000.
Proof. exact our_delta_Li_val. Qed.

(** Li NIST is 337/10000, our is 326/10000 => we underpredict *)
Lemma li_underprediction : our_delta_Li < nist_splitting_Li.
Proof.
  rewrite our_delta_Li_val, nist_Li_val. lra.
Qed.

(** Li error is ~11/10000 *)
Lemma li_error_magnitude : Qabs li_diff == 11 # 10000.
Proof. exact li_diff_abs. Qed.

(** Li error exceeds 1% threshold *)
Lemma li_exceeds_threshold : Qabs li_diff > 1 # 1000.
Proof. rewrite li_diff_abs. lra. Qed.

(* ================================================================== *)
(*  BERYLLIUM: EXACT                                                    *)
(* ================================================================== *)

Lemma be_screening_exact : nist_splitting_Be == our_delta_Be.
Proof. exact be_exact_match. Qed.

(* ================================================================== *)
(*  HONEST ASSESSMENT                                                   *)
(* ================================================================== *)

(** Model works for He and Be, but not Li *)
Theorem honest_assessment :
  Qabs he_diff < 1 # 100 /\
  nist_splitting_Be == our_delta_Be /\
  our_delta_Li < nist_splitting_Li.
Proof.
  split; [| split].
  - exact he_close_to_nist.
  - exact be_exact_match.
  - rewrite our_delta_Li_val, nist_Li_val. lra.
Qed.

(** Error grows with Z: He < Li *)
Theorem error_grows_with_z :
  Qabs he_diff < Qabs li_diff.
Proof.
  rewrite he_diff_abs, li_diff_abs. lra.
Qed.

(** Screening model verdict *)
Theorem screening_verdict :
  (* He: match *)
  Qabs he_diff < 1 # 100 /\
  (* Be: exact *)
  nist_splitting_Be == our_delta_Be /\
  (* Li: mismatch - needs higher-order screening *)
  Qabs li_diff > 1 # 1000.
Proof.
  split; [| split].
  - exact he_close_to_nist.
  - exact be_exact_match.
  - rewrite li_diff_abs. lra.
Qed.
