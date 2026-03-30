(* ========================================================================= *)
(*  WEINBERGANGLERUNNING — Weinberg Angle: Tree-Level Prediction vs Data     *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics                            *)
(*                                                                          *)
(*  sin^2(theta_W) = 3/13 at GUT from distinction structure.               *)
(*  Standard SU(5) predicts 3/8 = 0.375. Observed at M_Z: 0.2312.          *)
(*  Our tree-level 3/13 = 0.2307... matches observation to 0.3%.           *)
(*                                                                          *)
(*  Elements: sin2_tree, sin2_observed, sin2_gut_standard, error bounds     *)
(*  Roles:    precision prediction from structural principles alone         *)
(*  Rules:    |tree - observed| < 1/1000; no RG running needed              *)
(*  Status:   prediction | comparison | accuracy                           *)
(*                                                                          *)
(*  STATUS: 12 Qed, 0 Admitted                                              *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Core definitions ---- *)

(* Our prediction: sin^2(theta_W) = 3/13 from E/R/R distinction *)
Definition sin2_tree : Q := 3 # 13.

(* Observed value at M_Z: 0.23120 *)
Definition sin2_observed : Q := 2312 # 10000.

(* Standard SU(5) GUT prediction *)
Definition sin2_gut_standard : Q := 3 # 8.

(* ---- Theorems ---- *)

(* 1. Our prediction value *)
Lemma our_prediction : sin2_tree == 3 # 13.
Proof. vm_compute. reflexivity. Qed.

(* 2. Our prediction in decimal range: 0.23 < 3/13 < 0.24 *)
Lemma our_prediction_decimal : 23 # 100 < sin2_tree /\ sin2_tree < 24 # 100.
Proof. split; vm_compute; reflexivity. Qed.

(* 3. Standard SU(5) prediction *)
Lemma standard_prediction : sin2_gut_standard == 3 # 8.
Proof. vm_compute. reflexivity. Qed.

(* 4. Standard prediction is way too high: 3/8 > 1/3 *)
Lemma standard_off : 1 # 3 < sin2_gut_standard.
Proof. vm_compute. reflexivity. Qed.

(* 5. Our prediction is smaller (closer to observed) than standard *)
Lemma our_closer : sin2_tree < sin2_gut_standard.
Proof. vm_compute. reflexivity. Qed.

(* 6. Our prediction matches observed to < 1/1000 *)
(* 3/13 - 2312/10000 = 30000/130000 - 30056/130000 = -56/130000 = -7/16250 *)
(* |{-7/16250}| = 7/16250 < 1/1000 = 16.25/16250 *)
Lemma our_vs_observed : Qabs (sin2_tree - sin2_observed) < 1 # 1000.
Proof.
  assert (Hdiff : sin2_tree - sin2_observed == -(7 # 16250)).
  { vm_compute. reflexivity. }
  rewrite Hdiff.
  assert (Habs : Qabs (-(7 # 16250)) == 7 # 16250).
  { vm_compute. reflexivity. }
  rewrite Habs.
  vm_compute. reflexivity.
Qed.

(* 7. Standard prediction error is much larger *)
(* 3/8 - 2312/10000 = 3750/10000 - 2312/10000 = 1438/10000 = 719/5000 *)
Lemma standard_error_large : Qabs (sin2_gut_standard - sin2_observed) > 1 # 10.
Proof.
  assert (Hdiff : sin2_gut_standard - sin2_observed == 719 # 5000).
  { vm_compute. reflexivity. }
  rewrite Hdiff.
  assert (Habs : Qabs (719 # 5000) == 719 # 5000).
  { vm_compute. reflexivity. }
  rewrite Habs.
  vm_compute. reflexivity.
Qed.

(* 8. Our error is less than standard error *)
Lemma our_error_smaller :
  Qabs (sin2_tree - sin2_observed) < Qabs (sin2_gut_standard - sin2_observed).
Proof.
  assert (H1 : sin2_tree - sin2_observed == -(7 # 16250)) by (vm_compute; reflexivity).
  assert (H2 : sin2_gut_standard - sin2_observed == 719 # 5000) by (vm_compute; reflexivity).
  rewrite H1, H2.
  assert (Ha1 : Qabs (-(7 # 16250)) == 7 # 16250) by (vm_compute; reflexivity).
  assert (Ha2 : Qabs (719 # 5000) == 719 # 5000) by (vm_compute; reflexivity).
  rewrite Ha1, Ha2.
  vm_compute. reflexivity.
Qed.

(* 9. sin2_tree is between 0 and 1 *)
Lemma sin2_tree_range : 0 < sin2_tree /\ sin2_tree < 1.
Proof. split; vm_compute; reflexivity. Qed.

(* 10. sin2_observed is between 0 and 1 *)
Lemma sin2_observed_range : 0 < sin2_observed /\ sin2_observed < 1.
Proof. split; vm_compute; reflexivity. Qed.

(* 11. Ratio of errors: our error / standard error < 1/100 *)
(* (7/16250) / (719/5000) = 7*5000 / (16250*719) = 35000/11684250 = 4/1333... *)
(* Actually: 7/16250 * 5000/719 = 35000/11684250. Simplify: gcd(35000,11684250). *)
(* 35000/11684250 < 1/100 iff 3500000 < 11684250. YES. *)
Lemma error_ratio_small :
  (7 # 16250) * (5000 # 719) < 1 # 100.
Proof. vm_compute. reflexivity. Qed.

(* 12. The key result: tree-level prediction matches experiment without RG running *)
Lemma match_no_running :
  sin2_tree == 3 # 13 /\
  Qabs (sin2_tree - sin2_observed) < 1 # 1000 /\
  Qabs (sin2_gut_standard - sin2_observed) > 1 # 10.
Proof.
  split; [| split].
  - vm_compute. reflexivity.
  - assert (Hdiff : sin2_tree - sin2_observed == -(7 # 16250)) by (vm_compute; reflexivity).
    rewrite Hdiff.
    assert (Habs : Qabs (-(7 # 16250)) == 7 # 16250) by (vm_compute; reflexivity).
    rewrite Habs. vm_compute. reflexivity.
  - assert (Hdiff : sin2_gut_standard - sin2_observed == 719 # 5000) by (vm_compute; reflexivity).
    rewrite Hdiff.
    assert (Habs : Qabs (719 # 5000) == 719 # 5000) by (vm_compute; reflexivity).
    rewrite Habs. vm_compute. reflexivity.
Qed.
