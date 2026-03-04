(* ========================================================================= *)
(*              PROBABILITY THEORY AND BAYESIAN FALLACY DETECTION            *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  PURPOSE: Constructive probability theory over Q with Bayes' theorem      *)
(*  and formal proofs that three classical probabilistic fallacies are       *)
(*  structurally detectable.                                                 *)
(*                                                                           *)
(*  CONTENTS:                                                                *)
(*    1. Probability space (axiomatic, over Q)                               *)
(*    2. Conditional probability                                             *)
(*    3. Bayes' theorem                                                      *)
(*    4. Independence                                                        *)
(*    5. Fallacy detection theorems:                                         *)
(*       - Base rate fallacy: P(H|E) = P(E|H) implies P(H) = P(E)          *)
(*       - Conjunction fallacy: P(A and B) <= P(A)                          *)
(*       - Gambler's fallacy: independence is preserved across trials        *)
(*                                                                           *)
(*  STATUS: 12 Qed, 0 Admitted (100%)                                       *)
(*                                                                           *)
(*  AXIOMS: NONE - fully constructive over Q                                 *)
(*                                                                           *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Open Scope Q_scope.

(* ========================================================================= *)
(* AUXILIARY LEMMA: deriving strict positivity from non-negativity + nonzero  *)
(* ========================================================================= *)

Lemma Qnonneg_nonzero_pos : forall x : Q, 0 <= x -> ~ (x == 0) -> 0 < x.
Proof.
  intros x Hle Hneq.
  apply Qle_lt_or_eq in Hle.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply Hneq. symmetry. exact Heq.
Qed.

(* ========================================================================= *)
(* SECTION 1: PROBABILITY SPACE OVER Q                                       *)
(* ========================================================================= *)

(**
  We define a probability space axiomatically using a Section with Variables.

  Events are abstract identifiers. The probability function P maps
  events to rationals in [0,1]. Conjunction of events is represented
  by a separate function that returns the conjunction event identifier.
*)

Section ProbabilitySpace.

  (** Event type: abstract identifiers *)
  Variable Event : Type.

  (** Probability function *)
  Variable P : Event -> Q.

  (** Special events *)
  Variable omega : Event.  (* certain event *)

  (** Conjunction: for any two events, there is a conjunction event *)
  Variable conj_event : Event -> Event -> Event.

  (** Axiom: probabilities are non-negative *)
  Hypothesis P_nonneg : forall e : Event, 0 <= P e.

  (** Axiom: probabilities are at most 1 *)
  Hypothesis P_le_one : forall e : Event, P e <= 1.

  (** Axiom: certain event has probability 1 *)
  Hypothesis P_omega : P omega == 1.

  (** Axiom: conjunction is bounded by each component (monotonicity) *)
  Hypothesis P_conj_le_left : forall A B : Event, P (conj_event A B) <= P A.
  Hypothesis P_conj_le_right : forall A B : Event, P (conj_event A B) <= P B.

  (** Axiom: conjunction is commutative in probability *)
  Hypothesis P_conj_comm : forall A B : Event, P (conj_event A B) == P (conj_event B A).

  (* ======================================================================= *)
  (* SECTION 2: CONDITIONAL PROBABILITY                                      *)
  (* ======================================================================= *)

  (**
    Conditional probability: P(A|B) = P(A and B) / P(B)
    Only defined when P(B) <> 0.
  *)

  Definition cond_prob (A B : Event) (HB : ~ (P B == 0)) : Q :=
    P (conj_event A B) / P B.

  (** Conditional probability is non-negative *)
  Lemma cond_prob_nonneg : forall A B (HB : ~ (P B == 0)),
    0 <= cond_prob A B HB.
  Proof.
    intros A B HB.
    unfold cond_prob, Qdiv.
    apply Qle_shift_div_l.
    - apply Qnonneg_nonzero_pos; [apply P_nonneg | exact HB].
    - rewrite Qmult_0_l.
      apply Qle_trans with (y := P (conj_event A B)).
      + apply P_nonneg.
      + apply Qle_refl.
  Qed.

  (** Conditional probability is at most 1 *)
  Lemma cond_prob_le_one : forall A B (HB : ~ (P B == 0)),
    cond_prob A B HB <= 1.
  Proof.
    intros A B HB.
    unfold cond_prob, Qdiv.
    apply Qle_shift_div_r.
    - apply Qnonneg_nonzero_pos; [apply P_nonneg | exact HB].
    - rewrite Qmult_1_l.
      apply P_conj_le_right.
  Qed.

  (* ======================================================================= *)
  (* SECTION 3: BAYES' THEOREM                                               *)
  (* ======================================================================= *)

  (**
    Bayes' theorem:
      P(H|E) = P(E|H) * P(H) / P(E)

    Proof: Both sides equal P(H and E) / P(E), using commutativity
    of conjunction and algebraic cancellation of P(H).
  *)

  Theorem bayes_rule : forall H E
    (HE_pos : ~ (P E == 0))
    (HH_pos : ~ (P H == 0)),
    cond_prob H E HE_pos == (cond_prob E H HH_pos) * P H / P E.
  Proof.
    intros H E HE_pos HH_pos.
    unfold cond_prob, Qdiv.
    (* LHS: P(conj H E) * / P(E) *)
    (* RHS: (P(conj E H) * / P(H)) * P(H) * / P(E) *)
    rewrite (P_conj_comm H E).
    field.
    split.
    - intro Habs. apply HE_pos. exact Habs.
    - intro Habs. apply HH_pos. exact Habs.
  Qed.

  (* ======================================================================= *)
  (* SECTION 4: INDEPENDENCE                                                  *)
  (* ======================================================================= *)

  (**
    Two events A, B are independent iff P(A and B) = P(A) * P(B).
  *)

  Definition independent (A B : Event) : Prop :=
    P (conj_event A B) == P A * P B.

  (** Independence is symmetric *)
  Lemma independent_sym : forall A B,
    independent A B -> independent B A.
  Proof.
    intros A B Hind.
    unfold independent in *.
    rewrite P_conj_comm.
    rewrite Qmult_comm.
    exact Hind.
  Qed.

  (** If A and B are independent and P(B) > 0, then P(A|B) = P(A) *)
  Lemma independent_cond : forall A B (HB : ~ (P B == 0)),
    independent A B ->
    cond_prob A B HB == P A.
  Proof.
    intros A B HB Hind.
    unfold cond_prob, independent, Qdiv in *.
    rewrite Hind.
    field.
    exact HB.
  Qed.

  (* ======================================================================= *)
  (* SECTION 5: PROBABILISTIC FALLACY DETECTION                              *)
  (* ======================================================================= *)

  (**
    FALLACY 1: BASE RATE FALLACY (Prosecutor's Fallacy)

    The base rate fallacy confuses P(H|E) with P(E|H).
    These are equal ONLY when P(H) = P(E) (given P(H&E) > 0).

    Formally: if P(H|E) == P(E|H), P(H) > 0, P(E) > 0, P(H&E) > 0,
    then P(H) == P(E).

    The condition P(H&E) > 0 prevents the trivial case where both
    conditional probabilities are zero regardless of marginals.
  *)

  Theorem base_rate_fallacy_detected : forall H E
    (HE_pos : ~ (P E == 0))
    (HH_pos : ~ (P H == 0)),
    ~ (P (conj_event H E) == 0) ->
    cond_prob H E HE_pos == cond_prob E H HH_pos ->
    P H == P E.
  Proof.
    intros H E HE_pos HH_pos Hconj_nz Hcond.
    unfold cond_prob, Qdiv in Hcond.
    (* Hcond: P(conj H E) * / P E == P(conj E H) * / P H *)
    (* By commutativity: P(conj H E) == P(conj E H) *)
    (* So: P(conj H E) * / P E == P(conj H E) * / P H *)
    (* Cancel P(conj H E) (nonzero): / P E == / P H *)
    (* Therefore P E == P H *)
    assert (HPH : 0 < P H) by (apply Qnonneg_nonzero_pos; [apply P_nonneg | exact HH_pos]).
    assert (HPE : 0 < P E) by (apply Qnonneg_nonzero_pos; [apply P_nonneg | exact HE_pos]).
    assert (HPHE : 0 < P (conj_event H E)).
    { apply Qnonneg_nonzero_pos; [apply P_nonneg | exact Hconj_nz]. }
    (* Multiply both sides by P E * P H to clear denominators *)
    (* P(conj H E) * /P E == P(conj E H) * /P H *)
    (* => P(conj H E) * P H == P(conj E H) * P E *)
    (* => P(conj H E) * P H == P(conj H E) * P E  (by comm) *)
    (* => P H == P E  (cancel nonzero P(conj H E)) *)
    rewrite (P_conj_comm H E) in Hcond.
    (* Now Hcond: P(conj E H) * / P E == P(conj E H) * / P H *)
    (* Use Qmult_inj_l: ~ z == 0 -> z * x == z * y <-> x == y *)
    assert (Hconj_EH_nz : ~ (P (conj_event E H) == 0)).
    { intro Heq. apply Hconj_nz. rewrite P_conj_comm. exact Heq. }
    rewrite Qmult_inj_l in Hcond; [| exact Hconj_EH_nz].
    (* Hcond: / P E == / P H *)
    (* Now: /P E == /P H implies P E == P H *)
    (* Use Qinv_involutive: / / q == q *)
    rewrite <- (Qinv_involutive (P E)).
    rewrite <- (Qinv_involutive (P H)).
    rewrite Hcond.
    apply Qeq_refl.
  Qed.

  (**
    FALLACY 2: CONJUNCTION FALLACY

    The conjunction fallacy asserts P(A and B) > P(A) for some events,
    which violates basic probability axioms (monotonicity).

    We prove: P(A and B) <= P(A) always holds.
    Therefore any claim P(A and B) > P(A) is structurally detectable
    as a fallacy.
  *)

  Theorem conjunction_fallacy_detected : forall A B,
    P (conj_event A B) <= P A.
  Proof.
    intros A B.
    apply P_conj_le_left.
  Qed.

  (**
    Corollary: claiming P(A and B) > P(A) leads to contradiction.
  *)

  Theorem conjunction_fallacy_absurd : forall A B,
    P (conj_event A B) > P A -> False.
  Proof.
    intros A B Hgt.
    assert (Hle := P_conj_le_left A B).
    apply Qlt_not_le in Hgt.
    exact (Hgt Hle).
  Qed.

  (**
    FALLACY 3: GAMBLER'S FALLACY

    The gambler's fallacy assumes that past outcomes of independent events
    affect future probabilities. We formalize this as:

    If events A and B are independent, then knowing B occurred does not
    change the probability of A. That is, P(A|B) = P(A).

    This means independence is PRESERVED: observing B gives no information
    about A. Claiming otherwise is the gambler's fallacy.
  *)

  Theorem gamblers_fallacy_detected : forall A B
    (HB : ~ (P B == 0)),
    independent A B ->
    cond_prob A B HB == P A.
  Proof.
    intros A B HB Hind.
    apply independent_cond.
    exact Hind.
  Qed.

  (**
    Corollary: If A, B independent, claiming P(A|B) <> P(A) is absurd.
  *)

  Theorem gamblers_fallacy_absurd : forall A B
    (HB : ~ (P B == 0)),
    independent A B ->
    ~ (cond_prob A B HB == P A) -> False.
  Proof.
    intros A B HB Hind Hneq.
    apply Hneq.
    apply gamblers_fallacy_detected.
    exact Hind.
  Qed.

  (**
    BONUS: Bayes asymmetry detector (contrapositive of base rate fallacy).

    If P(H) <> P(E), then P(H|E) <> P(E|H).
  *)

  Theorem bayes_asymmetry : forall H E
    (HE_pos : ~ (P E == 0))
    (HH_pos : ~ (P H == 0)),
    ~ (P (conj_event H E) == 0) ->
    ~ (P H == P E) ->
    ~ (cond_prob H E HE_pos == cond_prob E H HH_pos).
  Proof.
    intros H E HE_pos HH_pos Hconj_nz Hneq Hcond.
    apply Hneq.
    exact (base_rate_fallacy_detected H E HE_pos HH_pos Hconj_nz Hcond).
  Qed.

End ProbabilitySpace.

(* ========================================================================= *)
(* SECTION 6: VERIFICATION                                                    *)
(* ========================================================================= *)

(**
  All theorems are now universally quantified over the probability space.
  Print Assumptions verifies: 0 axioms (fully constructive).
*)

Check bayes_rule.
Check base_rate_fallacy_detected.
Check conjunction_fallacy_detected.
Check conjunction_fallacy_absurd.
Check gamblers_fallacy_detected.
Check gamblers_fallacy_absurd.
Check bayes_asymmetry.

Print Assumptions bayes_rule.
Print Assumptions base_rate_fallacy_detected.
Print Assumptions conjunction_fallacy_detected.
Print Assumptions gamblers_fallacy_detected.
Print Assumptions bayes_asymmetry.
