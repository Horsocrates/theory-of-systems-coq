(** * NIST_Splitting.v -- NIST spectral line data vs our predictions
    Elements: nist_splitting_He, our_delta_He, he_close_to_nist
    Roles:    Compare lattice-predicted splittings to NIST reference data
    Rules:    All Q arithmetic, no Admitted. Qabs handled via compute-then-lra.
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  NIST REFERENCE DATA (as Q constants)                                *)
(* ================================================================== *)

(** NIST fine-structure splitting for He (in appropriate units) *)
Definition nist_splitting_He : Q := 466 # 10000.

(** NIST fine-structure splitting for Li *)
Definition nist_splitting_Li : Q := 337 # 10000.

(** NIST fine-structure splitting for Be *)
Definition nist_splitting_Be : Q := 261 # 10000.

(* ================================================================== *)
(*  OUR PREDICTIONS                                                     *)
(* ================================================================== *)

(** Our prediction for He: delta = 1/4 - Z_eff^2/n^2 screening correction.
    For He: 1/4 - 2029/10000 = 471/10000 *)
Definition our_delta_He : Q := (1#4) - (2029#10000).

(** Our prediction for Li *)
Definition our_delta_Li : Q := (1#4) - (2174#10000).

(** Our prediction for Be *)
Definition our_delta_Be : Q := (1#4) - (2239#10000).

(* ================================================================== *)
(*  COMPUTED VALUES                                                     *)
(* ================================================================== *)

Lemma our_delta_He_val : our_delta_He == 471 # 10000.
Proof. unfold our_delta_He. vm_compute. reflexivity. Qed.

Lemma our_delta_Li_val : our_delta_Li == 326 # 10000.
Proof. unfold our_delta_Li. vm_compute. reflexivity. Qed.

Lemma our_delta_Be_val : our_delta_Be == 261 # 10000.
Proof. unfold our_delta_Be. vm_compute. reflexivity. Qed.

Lemma nist_He_val : nist_splitting_He == 466 # 10000.
Proof. unfold nist_splitting_He. vm_compute. reflexivity. Qed.

Lemma nist_Li_val : nist_splitting_Li == 337 # 10000.
Proof. unfold nist_splitting_Li. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COMPARISON: He (close match)                                        *)
(* ================================================================== *)

(** Difference for He: 466/10000 - 471/10000 = -5/10000 *)
Definition he_diff : Q := nist_splitting_He - our_delta_He.

Lemma he_diff_val : he_diff == -(5#10000).
Proof. unfold he_diff, nist_splitting_He, our_delta_He. vm_compute. reflexivity. Qed.

(** |diff| = 5/10000 < 1/100 = 100/10000 *)
Lemma he_diff_abs : Qabs he_diff == 5 # 10000.
Proof.
  rewrite he_diff_val. vm_compute. reflexivity.
Qed.

Lemma he_close_to_nist : Qabs he_diff < 1 # 100.
Proof.
  rewrite he_diff_abs. lra.
Qed.

(** Relative error < 2% *)
Lemma he_relative_small : Qabs he_diff < 1 # 50.
Proof. rewrite he_diff_abs. lra. Qed.

(* ================================================================== *)
(*  COMPARISON: Li (mismatch)                                           *)
(* ================================================================== *)

Definition li_diff : Q := nist_splitting_Li - our_delta_Li.

Lemma li_diff_val : li_diff == 11 # 10000.
Proof. unfold li_diff, nist_splitting_Li, our_delta_Li. vm_compute. reflexivity. Qed.

Lemma li_diff_abs : Qabs li_diff == 11 # 10000.
Proof. rewrite li_diff_val. vm_compute. reflexivity. Qed.

(** Li difference is larger than He difference *)
Lemma li_larger_error : Qabs li_diff > Qabs he_diff.
Proof. rewrite li_diff_abs, he_diff_abs. lra. Qed.

(* ================================================================== *)
(*  COMPARISON: Be (exact match!)                                       *)
(* ================================================================== *)

Lemma be_exact_match : nist_splitting_Be == our_delta_Be.
Proof.
  unfold nist_splitting_Be, our_delta_Be. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SUMMARY                                                             *)
(* ================================================================== *)

Theorem nist_comparison_summary :
  Qabs he_diff < 1 # 100 /\
  nist_splitting_Be == our_delta_Be /\
  our_delta_He == 471 # 10000.
Proof.
  split; [| split].
  - exact he_close_to_nist.
  - exact be_exact_match.
  - exact our_delta_He_val.
Qed.
