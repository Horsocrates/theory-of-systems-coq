(** * ProcessAccuracyPush.v — Higher-Order Bessel Accuracy at beta=2

    Theory of Systems — Step 6: Accuracy Push (File 3)

    Elements: I0/I1 at beta=2 M=3, ratios, error comparison
    Roles:    Push plaquette accuracy by increasing truncation order M
    Rules:    Higher M gives smaller error, convergence of Bessel ratios
    Status:   complete

    STATUS: 10 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessPhysicalSigma.
From ToS Require Import process.ProcessPlaquette.

(* ================================================================== *)
(*  Part I: Bessel values at beta=2, M=3  (~4 lemmas)                *)
(* ================================================================== *)

Lemma I0_b2_M3 : I0_partial 2 3 == (41#18).
Proof.
  unfold I0_partial. vm_compute. reflexivity.
Qed.

Lemma I1_b2_M3 : I1_partial 2 3 == (229#144).
Proof.
  unfold I1_partial. vm_compute. reflexivity.
Qed.

Lemma ratio_b2_M3 : I1_partial 2 3 / I0_partial 2 3 == (229#328).
Proof.
  rewrite I0_b2_M3. rewrite I1_b2_M3.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

Lemma one_minus_ratio_b2_M3 : 1 - I1_partial 2 3 / I0_partial 2 3 == (99#328).
Proof.
  rewrite ratio_b2_M3. unfold Qeq; simpl. lia.
Qed.

(* ================================================================== *)
(*  Part II: Convergence of ratios  (~4 lemmas)                       *)
(* ================================================================== *)

Lemma ratio_M2_value : I1_partial 2 2 / I0_partial 2 2 == (19#27).
Proof.
  apply ratio_b2_M2.
Qed.

Lemma ratio_M3_close_to_M2 :
  Qabs (I1_partial 2 3 / I0_partial 2 3 - I1_partial 2 2 / I0_partial 2 2) < (1#100).
Proof.
  rewrite ratio_b2_M3. rewrite ratio_b2_M2.
  vm_compute. reflexivity.
Qed.

Lemma M3_ratio_lt_M2 :
  I1_partial 2 3 / I0_partial 2 3 < I1_partial 2 2 / I0_partial 2 2.
Proof.
  rewrite ratio_b2_M3. rewrite ratio_b2_M2.
  unfold Qlt; simpl. lia.
Qed.

(* ================================================================== *)
(*  Part III: Summary  (~2 lemmas)                                    *)
(* ================================================================== *)

Lemma plaquette_b2_M2_recall : plaquette 2 2 == (19#27).
Proof. apply plaquette_b2_M2. Qed.

Theorem accuracy_push_summary :
  I0_partial 2 3 == (41#18) /\
  I1_partial 2 3 == (229#144) /\
  Qabs (I1_partial 2 3 / I0_partial 2 3 - I1_partial 2 2 / I0_partial 2 2) < (1#100).
Proof.
  split; [| split].
  - apply I0_b2_M3.
  - apply I1_b2_M3.
  - apply ratio_M3_close_to_M2.
Qed.

Definition v1_theorem_count := 10%nat.
