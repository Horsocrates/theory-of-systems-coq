(** * CreditScoring.v -- Credit Scoring Models as ToS Systems

    Theory of Systems -- Verified Standard Library (Batch 6)

    Elements: features (list Q), weights (list Q), scores (Q)
    Roles:    feature -> Input, weight -> Importance, score -> Output, threshold -> Gate
    Rules:    weighted sum scoring (constitution), threshold classification
    Status:   approved | denied | review | invalid_input

    Connection: Statistics.v -- weighted_sum for scoring
    Connection: ConvexAnalysis.v -- scoring as convex combination

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import stdlib.Statistics.

(* ========================================================================= *)
(* CORE DEFINITIONS                                                          *)
(* ========================================================================= *)

(** Credit decision type *)
Inductive CreditDecision := Approved | Denied | Review.

(** Classify a score against approval and denial thresholds.
    - score >= approve_thresh  =>  Approved
    - score <= deny_thresh     =>  Denied
    - otherwise                =>  Review *)
Definition classify_score (score approve_thresh deny_thresh : Q) : CreditDecision :=
  if Qle_bool approve_thresh score then Approved
  else if Qle_bool score deny_thresh then Denied
  else Review.

(** Credit model record *)
Record CreditModel := mkCreditModel {
  cm_weights : list Q;
  cm_approve : Q;
  cm_deny    : Q
}.

(** Compute credit score as weighted sum of features and model weights *)
Definition credit_score (model : CreditModel) (features : list Q) : Q :=
  weighted_sum features (cm_weights model).

(** Make a credit decision for given features *)
Definition credit_decide (model : CreditModel) (features : list Q) : CreditDecision :=
  classify_score (credit_score model features) (cm_approve model) (cm_deny model).

(** Clamp a value to [0, 1] *)
Definition clamp_01 (x : Q) : Q := Qmax 0 (Qmin x 1).

(** A feature is valid if it lies in [0, 1] *)
Definition valid_feature (x : Q) : Prop := 0 <= x /\ x <= 1.

(** All weights are non-negative *)
Definition nonneg_weights (ws : list Q) : Prop := Forall (fun w => 0 <= w) ws.

(** Decidable equality for CreditDecision *)
Definition CreditDecision_eq_dec (d1 d2 : CreditDecision) : {d1 = d2} + {d1 <> d2}.
Proof.
  decide equality.
Defined.

(* ========================================================================= *)
(* THEOREMS: classify_score                                                  *)
(* ========================================================================= *)

(** Theorem 1: If approve_thresh <= score, classification is Approved *)
Lemma classify_approved : forall score approve_thresh deny_thresh,
  approve_thresh <= score ->
  classify_score score approve_thresh deny_thresh = Approved.
Proof.
  intros score approve_thresh deny_thresh H.
  unfold classify_score.
  destruct (Qle_bool approve_thresh score) eqn:Hle.
  - reflexivity.
  - apply Qle_bool_iff in H. rewrite H in Hle. discriminate.
Qed.

(** Theorem 2: If score <= deny_thresh and deny_thresh < approve_thresh, classification is Denied *)
Lemma classify_denied : forall score approve_thresh deny_thresh,
  score <= deny_thresh ->
  deny_thresh < approve_thresh ->
  classify_score score approve_thresh deny_thresh = Denied.
Proof.
  intros score approve_thresh deny_thresh Hsd Hda.
  unfold classify_score.
  destruct (Qle_bool approve_thresh score) eqn:Hle.
  - apply Qle_bool_iff in Hle. lra.
  - destruct (Qle_bool score deny_thresh) eqn:Hle2.
    + reflexivity.
    + apply Qle_bool_iff in Hsd. rewrite Hsd in Hle2. discriminate.
Qed.

(** Theorem 3: If score is strictly between deny and approve, result is Review *)
Lemma classify_review : forall score approve_thresh deny_thresh,
  deny_thresh < score ->
  score < approve_thresh ->
  classify_score score approve_thresh deny_thresh = Review.
Proof.
  intros score approve_thresh deny_thresh Hds Hsa.
  unfold classify_score.
  destruct (Qle_bool approve_thresh score) eqn:Hle1.
  - apply Qle_bool_iff in Hle1. lra.
  - destruct (Qle_bool score deny_thresh) eqn:Hle2.
    + apply Qle_bool_iff in Hle2. lra.
    + reflexivity.
Qed.

(* ========================================================================= *)
(* THEOREMS: credit_score                                                    *)
(* ========================================================================= *)

(** Theorem 4: credit_score on empty features is 0 *)
Lemma credit_score_nil : forall model,
  credit_score model [] == 0.
Proof.
  intro model. unfold credit_score. simpl.
  destruct (cm_weights model); reflexivity.
Qed.

(** Theorem 5: credit_score with singleton lists *)
Lemma credit_score_singleton : forall w f a d,
  credit_score (mkCreditModel [w] a d) [f] == f * w.
Proof.
  intros w f a d. unfold credit_score. simpl. ring.
Qed.

(** Theorem 6: credit_score with two-element lists *)
Lemma credit_score_two : forall w1 w2 f1 f2 a d,
  credit_score (mkCreditModel [w1; w2] a d) [f1; f2] == f1 * w1 + f2 * w2.
Proof.
  intros. unfold credit_score. simpl. ring.
Qed.

(** Theorem 7: credit_score with empty weights is 0 *)
Lemma credit_score_empty_weights : forall a d fs,
  credit_score (mkCreditModel [] a d) fs == 0.
Proof.
  intros a d fs. unfold credit_score. simpl.
  destruct fs; reflexivity.
Qed.

(** Theorem 8: credit_score with three-element lists *)
Lemma credit_score_three : forall w1 w2 w3 f1 f2 f3 a d,
  credit_score (mkCreditModel [w1; w2; w3] a d) [f1; f2; f3] ==
    f1 * w1 + f2 * w2 + f3 * w3.
Proof.
  intros. unfold credit_score. simpl. ring.
Qed.

(* ========================================================================= *)
(* THEOREMS: clamp_01                                                        *)
(* ========================================================================= *)

(** Theorem 9: clamp_01 always produces a value in [0, 1] *)
Lemma clamp_01_in_range : forall x, 0 <= clamp_01 x /\ clamp_01 x <= 1.
Proof.
  intro x. unfold clamp_01.
  destruct (Q.max_spec 0 (Qmin x 1)) as [[Hlt Hmax] | [Hle Hmax]];
  rewrite Hmax;
  destruct (Q.min_spec x 1) as [[Hlt2 Hmin] | [Hle2 Hmin]];
  try rewrite Hmin;
  split; lra.
Qed.

(** Theorem 10: clamp_01 is identity on [0, 1] *)
Lemma clamp_01_id : forall x,
  0 <= x -> x <= 1 -> clamp_01 x == x.
Proof.
  intros x H0 H1. unfold clamp_01.
  destruct (Q.max_spec 0 (Qmin x 1)) as [[Hlt Hmax] | [Hle Hmax]];
  rewrite Hmax;
  destruct (Q.min_spec x 1) as [[Hlt2 Hmin] | [Hle2 Hmin]];
  try rewrite Hmin;
  lra.
Qed.

(** Theorem 11: clamp_01 maps values <= 0 to 0 *)
Lemma clamp_01_low : forall x,
  x <= 0 -> clamp_01 x == 0.
Proof.
  intros x Hx. unfold clamp_01.
  destruct (Q.max_spec 0 (Qmin x 1)) as [[Hlt Hmax] | [Hle Hmax]];
  rewrite Hmax;
  destruct (Q.min_spec x 1) as [[Hlt2 Hmin] | [Hle2 Hmin]];
  try rewrite Hmin;
  lra.
Qed.

(** Theorem 12: clamp_01 maps values >= 1 to 1 *)
Lemma clamp_01_high : forall x,
  1 <= x -> clamp_01 x == 1.
Proof.
  intros x Hx. unfold clamp_01.
  destruct (Q.max_spec 0 (Qmin x 1)) as [[Hlt Hmax] | [Hle Hmax]];
  rewrite Hmax;
  destruct (Q.min_spec x 1) as [[Hlt2 Hmin] | [Hle2 Hmin]];
  try rewrite Hmin;
  lra.
Qed.

(** Theorem 13: clamp_01 is idempotent *)
Lemma clamp_01_idempotent : forall x,
  clamp_01 (clamp_01 x) == clamp_01 x.
Proof.
  intro x.
  destruct (clamp_01_in_range x) as [H0 H1].
  apply clamp_01_id; assumption.
Qed.

(* ========================================================================= *)
(* THEOREMS: nonneg_weights                                                  *)
(* ========================================================================= *)

(** Theorem 14: empty list has nonneg_weights *)
Lemma nonneg_weights_nil : nonneg_weights [].
Proof.
  unfold nonneg_weights. constructor.
Qed.

(** Theorem 15: nonneg_weights cons iff *)
Lemma nonneg_weights_cons : forall w ws,
  nonneg_weights (w :: ws) <-> 0 <= w /\ nonneg_weights ws.
Proof.
  intros w ws. unfold nonneg_weights.
  split.
  - intro H. inversion H; subst. split; assumption.
  - intros [Hw Hws]. constructor; assumption.
Qed.

(* ========================================================================= *)
(* THEOREMS: valid_feature                                                   *)
(* ========================================================================= *)

(** Theorem 16: clamp_01 always produces a valid feature *)
Lemma valid_feature_clamp : forall x, valid_feature (clamp_01 x).
Proof.
  intro x. unfold valid_feature.
  apply clamp_01_in_range.
Qed.

(** Theorem 17: 0 is a valid feature *)
Lemma valid_feature_zero : valid_feature 0.
Proof.
  unfold valid_feature. lra.
Qed.

(** Theorem 18: 1 is a valid feature *)
Lemma valid_feature_one : valid_feature 1.
Proof.
  unfold valid_feature. lra.
Qed.

(* ========================================================================= *)
(* THEOREMS: credit_decide determinism and concrete examples                 *)
(* ========================================================================= *)

(** Theorem 19: credit_decide is deterministic (trivial by function purity) *)
Lemma credit_decide_deterministic : forall m fs,
  credit_decide m fs = credit_decide m fs.
Proof.
  intros m fs. reflexivity.
Qed.

(** Theorem 20: Concrete model approves high-scoring features.
    Model: weights=[1;1], approve=3/2, deny=1/2.
    Features: [1; 1]. Score = 1*1+1*1 = 2 >= 3/2 -> Approved *)
Lemma concrete_model_approve :
  credit_decide (mkCreditModel [1; 1] (3#2) (1#2)) [1; 1] = Approved.
Proof.
  unfold credit_decide, credit_score, classify_score. simpl.
  reflexivity.
Qed.

(** Theorem 21: Concrete model denies low-scoring features.
    Model: weights=[1;1], approve=3/2, deny=1/2.
    Features: [0; 0]. Score = 0 <= 1/2 -> Denied *)
Lemma concrete_model_deny :
  credit_decide (mkCreditModel [1; 1] (3#2) (1#2)) [0; 0] = Denied.
Proof.
  unfold credit_decide, credit_score, classify_score. simpl.
  reflexivity.
Qed.

(** Theorem 22: Concrete model puts borderline in review.
    Model: weights=[1;1], approve=3/2, deny=1/2.
    Features: [1/2; 1/2]. Score = 1 which is between 1/2 and 3/2 -> Review *)
Lemma concrete_model_review :
  credit_decide (mkCreditModel [1; 1] (3#2) (1#2)) [1#2; 1#2] = Review.
Proof.
  unfold credit_decide, credit_score, classify_score. simpl.
  reflexivity.
Qed.
