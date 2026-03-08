(** * DomainExamples.v -- Cross-Domain Integration Examples (Batch 6)

    Theory of Systems -- Verified Standard Library (Batch 6)

    Cross-module examples demonstrating connections between
    credit scoring, neural networks, text analysis, time series,
    and formal verification.

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import stdlib.Statistics.
From ToS Require Import stdlib.CreditScoring.
From ToS Require Import stdlib.NeuralNet.
From ToS Require Import stdlib.TextAnalysis.
From ToS Require Import stdlib.TimeSeries.
From ToS Require Import stdlib.FormalVerification.

(* ========================================================================= *)
(* CROSS-MODULE THEOREMS                                                     *)
(* ========================================================================= *)

(** Theorem 1: Credit scoring is a special case of neural network computation.
    credit_score with weights [w1;w2] and features [f1;f2] equals
    neuron_linear [w1;w2] [f1;f2] 0 -- i.e., a zero-bias neuron. *)
Lemma credit_via_neuron : forall w1 w2 f1 f2 a d,
  credit_score (mkCreditModel [w1; w2] a d) [f1; f2] ==
  neuron_linear [w1; w2] [f1; f2] 0.
Proof.
  intros. unfold credit_score, neuron_linear. simpl. ring.
Qed.

(** Theorem 2: For 0 <= x <= 1, relu and clamp_01 agree.
    Both functions preserve values already in [0,1]. *)
Lemma relu_clamp_agree_nonneg : forall x,
  0 <= x -> x <= 1 -> relu x == clamp_01 x.
Proof.
  intros x H0 H1.
  rewrite relu_pos by assumption.
  rewrite clamp_01_id by assumption.
  reflexivity.
Qed.

(** Theorem 3: count_token on a singleton document [t] for that token is 1. *)
Lemma doc_count_total : forall t,
  count_token t [t] = 1%nat.
Proof.
  intro t. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Theorem 4: const_ts c at time 0 equals c. *)
Lemma const_ts_reuse : forall c,
  const_ts c 0%nat = c.
Proof.
  intro c. reflexivity.
Qed.

(** Theorem 5: Excluded middle is a valid formula.
    (p \/ ~p) holds for all valuations. *)
Lemma verification_excluded_middle :
  valid (FOr (FVar 0%nat) (FNot (FVar 0%nat))).
Proof.
  unfold valid. intro v. simpl.
  destruct (v 0%nat); reflexivity.
Qed.

(** Theorem 6: Modus ponens as entailment.
    ((p -> q) /\ p) entails q. *)
Lemma verification_modus_ponens :
  entails (FAnd (FImpl (FVar 0%nat) (FVar 1%nat)) (FVar 0%nat)) (FVar 1%nat).
Proof.
  unfold entails. intros v H. simpl in *.
  destruct (v 0%nat); destruct (v 1%nat); simpl in *; auto; discriminate.
Qed.

(** Theorem 7: neuron_relu output is always non-negative,
    reusing the existing lemma. *)
Lemma nn_nonneg_score : forall ws xs b,
  0 <= neuron_relu ws xs b.
Proof.
  intros ws xs b. apply neuron_relu_nonneg.
Qed.

(** Theorem 8: Concrete credit model approves via neuron computation.
    Model: weights=[1;1], approve=3/2, deny=1/2.
    Features: [1;1]. neuron_linear [1;1] [1;1] 0 = 2 >= 3/2 => Approved. *)
Lemma credit_nn_approve :
  credit_decide (mkCreditModel [1; 1] (3#2) (1#2)) [1; 1] = Approved.
Proof.
  unfold credit_decide, credit_score, classify_score. simpl. reflexivity.
Qed.

(** Theorem 9: clamp_01 always produces a valid_feature,
    reusing the existing lemma. *)
Lemma clamp_valid_feature : forall x,
  valid_feature (clamp_01 x).
Proof.
  intro x. apply valid_feature_clamp.
Qed.

(** Theorem 10: bow_vector on empty vocab is nil,
    reusing the existing lemma. *)
Lemma text_bow_len : forall doc,
  bow_vector [] doc = [].
Proof.
  intro doc. apply bow_vector_nil.
Qed.

(** Theorem 11: Double negation elimination is a valid formula.
    ~~p -> p is a classical tautology. *)
Lemma double_neg_valid :
  valid (FImpl (FNot (FNot (FVar 0%nat))) (FVar 0%nat)).
Proof.
  unfold valid. intro v. simpl.
  destruct (v 0%nat); reflexivity.
Qed.

(** Theorem 12: Moving average of a constant series equals the constant.
    Reuses const_ts_ma_1 from TimeSeries.v. *)
Lemma ma_of_const : forall c t,
  moving_avg (const_ts c) 1 t == c.
Proof.
  intros c t. apply const_ts_ma_1.
Qed.

(** Theorem 13: Credit scoring through general weighted_sum equals
    the Statistics.weighted_sum directly. Shows the pipeline:
    Statistics -> CreditScoring -> NeuralNet are all weighted sums. *)
Lemma credit_score_is_weighted_sum : forall ws a d fs,
  credit_score (mkCreditModel ws a d) fs == weighted_sum fs ws.
Proof.
  intros ws a d fs. unfold credit_score. reflexivity.
Qed.

(** Theorem 14: Conjunction of two valid formulas is valid.
    If p and q are both tautologies, then p /\ q is also a tautology.
    Connects entailment and validity concepts from FormalVerification. *)
Lemma valid_and_combine : forall f1 f2,
  valid f1 -> valid f2 -> valid (FAnd f1 f2).
Proof.
  unfold valid. intros f1 f2 H1 H2 v. simpl.
  rewrite H1, H2. reflexivity.
Qed.
