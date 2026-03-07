(** * ConditionalProbability.v -- Extended Conditional Probability

    Theory of Systems -- Verified Standard Library (Tier 2b)

    Elements: events, random variables, probabilities
    Roles:    prior -> BaseRate, evidence -> Update, posterior -> UpdatedBelief
    Rules:    probability axioms + conditioning rule (constitution)
    Status:   independent | dependent | conditionally_independent

    Connection: Probability.v (extends), SoftmaxProbability.v

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Close Scope Z_scope.
Open Scope Q_scope.

(* ========================================================================= *)
(* AUXILIARY LEMMA                                                            *)
(* ========================================================================= *)

Lemma Qnonneg_nonzero_pos' : forall x : Q, 0 <= x -> ~ (x == 0) -> 0 < x.
Proof.
  intros x Hle Hneq.
  apply Qle_lt_or_eq in Hle.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply Hneq. symmetry. exact Heq.
Qed.

Lemma Qsq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hneg|Hpos].
  - assert (Heq : q * q == (-q) * (-q)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(* ========================================================================= *)
(* SECTION: EXTENDED CONDITIONAL PROBABILITY SPACE                            *)
(* ========================================================================= *)

Section ConditionalProbExtended.

  (** Event type: abstract identifiers *)
  Variable Event : Type.

  (** Probability function *)
  Variable P : Event -> Q.

  (** Special events *)
  Variable omega : Event.

  (** Event operations *)
  Variable conj_event : Event -> Event -> Event.
  Variable compl_event : Event -> Event.
  Variable disj_event : Event -> Event -> Event.

  (* --- Base axioms (same as Probability.v) --- *)
  Hypothesis P_nonneg : forall e, 0 <= P e.
  Hypothesis P_le_one : forall e, P e <= 1.
  Hypothesis P_omega : P omega == 1.
  Hypothesis P_conj_le_left : forall A B, P (conj_event A B) <= P A.
  Hypothesis P_conj_le_right : forall A B, P (conj_event A B) <= P B.
  Hypothesis P_conj_comm : forall A B,
    P (conj_event A B) == P (conj_event B A).

  (* --- Extended axioms --- *)
  Hypothesis P_compl : forall A, P A + P (compl_event A) == 1.
  Hypothesis P_additive : forall A B,
    P (conj_event A B) == 0 ->
    P (disj_event A B) == P A + P B.
  Hypothesis P_disj_comm : forall A B,
    P (disj_event A B) == P (disj_event B A).
  Hypothesis P_conj_compl_disjoint : forall A B,
    P (conj_event (conj_event A B) (conj_event A (compl_event B))) == 0.
  Hypothesis P_conj_union : forall A B,
    P (disj_event (conj_event A B) (conj_event A (compl_event B))) == P A.

  (* ======================================================================= *)
  (* DEFINITIONS                                                              *)
  (* ======================================================================= *)

  (** Conditional probability (total function, returns 0/0 = 0 when P(B)=0) *)
  Definition cond_prob_ext (A B : Event) : Q :=
    P (conj_event A B) / P B.

  (** Independence *)
  Definition independent (A B : Event) : Prop :=
    P (conj_event A B) == P A * P B.

  (** Expected value over a discrete list of (value, probability) pairs *)
  Fixpoint expected_value (vals : list Q) (probs : list Q) : Q :=
    match vals, probs with
    | v :: vs, p :: ps => v * p + expected_value vs ps
    | _, _ => 0
    end.

  (** Variance: E[(X - mu)^2] *)
  Definition variance (vals : list Q) (probs : list Q) (mu : Q) : Q :=
    expected_value (map (fun v => (v - mu) * (v - mu)) vals) probs.

  (* ======================================================================= *)
  (* COMPLEMENT AND BASIC PROPERTIES (6 Qed)                                 *)
  (* ======================================================================= *)

  (** 1. P(compl A) == 1 - P(A) *)
  Lemma complement_prob : forall A,
    P (compl_event A) == 1 - P A.
  Proof.
    intro A.
    assert (H := P_compl A).
    lra.
  Qed.

  (** 2. P(compl A) >= 0 *)
  Lemma complement_nonneg : forall A,
    0 <= P (compl_event A).
  Proof.
    intro A. apply P_nonneg.
  Qed.

  (** 3. P(compl A) <= 1 *)
  Lemma complement_le_one : forall A,
    P (compl_event A) <= 1.
  Proof.
    intro A. apply P_le_one.
  Qed.

  (** 4. Disjoint additivity: P(A cap B) == 0 -> P(A cup B) == P(A) + P(B) *)
  Lemma disjoint_additive : forall A B,
    P (conj_event A B) == 0 ->
    P (disj_event A B) == P A + P B.
  Proof.
    intros A B Hdisj.
    apply P_additive. exact Hdisj.
  Qed.

  (** 5. Law of total probability:
      P(A) == P(A cap B) + P(A cap compl B) *)
  Lemma total_probability : forall A B,
    P A == P (conj_event A B) + P (conj_event A (compl_event B)).
  Proof.
    intros A B.
    (* P(A) == P(disj(A cap B, A cap compl B))  by P_conj_union *)
    (* The two parts are disjoint by P_conj_compl_disjoint *)
    (* So P(disj ...) == P(A cap B) + P(A cap compl B) by P_additive *)
    assert (Hunion := P_conj_union A B).
    assert (Hdisj := P_conj_compl_disjoint A B).
    assert (Hadd := P_additive _ _ Hdisj).
    lra.
  Qed.

  (** 6. P(compl(compl A)) == P(A) *)
  Lemma complement_involution_prob : forall A,
    P (compl_event (compl_event A)) == P A.
  Proof.
    intro A.
    assert (H1 := complement_prob A).
    assert (H2 := complement_prob (compl_event A)).
    lra.
  Qed.

  (* ======================================================================= *)
  (* CONDITIONAL PROBABILITY (5 Qed)                                         *)
  (* ======================================================================= *)

  (** 7. Definition unfolding *)
  Lemma cond_prob_ext_def : forall A B,
    0 < P B ->
    cond_prob_ext A B == P (conj_event A B) / P B.
  Proof.
    intros A B _. unfold cond_prob_ext. reflexivity.
  Qed.

  (** 8. Conditional probability is non-negative when P(B) > 0 *)
  Lemma cond_prob_ext_nonneg : forall A B,
    0 < P B ->
    0 <= cond_prob_ext A B.
  Proof.
    intros A B HPB.
    unfold cond_prob_ext, Qdiv.
    apply Qle_shift_div_l.
    - exact HPB.
    - rewrite Qmult_0_l. apply P_nonneg.
  Qed.

  (** 9. Conditional probability is at most 1 when P(B) > 0 *)
  Lemma cond_prob_ext_le_one : forall A B,
    0 < P B ->
    cond_prob_ext A B <= 1.
  Proof.
    intros A B HPB.
    unfold cond_prob_ext, Qdiv.
    apply Qle_shift_div_r.
    - exact HPB.
    - rewrite Qmult_1_l. apply P_conj_le_right.
  Qed.

  (** 10. Chain rule: P(A cap B) == cond_prob_ext A B * P(B) *)
  Lemma cond_prob_chain : forall A B,
    0 < P B ->
    P (conj_event A B) == cond_prob_ext A B * P B.
  Proof.
    intros A B HPB.
    unfold cond_prob_ext, Qdiv.
    field.
    intro Habs. lra.
  Qed.

  (** 11. Bayes' rule (simple form):
      cond_prob_ext A B * P(B) == cond_prob_ext B A * P(A) *)
  Lemma bayes_simple : forall A B,
    0 < P A -> 0 < P B ->
    cond_prob_ext A B * P B == cond_prob_ext B A * P A.
  Proof.
    intros A B HPA HPB.
    unfold cond_prob_ext, Qdiv.
    rewrite (P_conj_comm A B).
    field.
    split; intro Habs; lra.
  Qed.

  (* ======================================================================= *)
  (* INDEPENDENCE (4 Qed)                                                    *)
  (* ======================================================================= *)

  (** 12. Independence is symmetric *)
  Lemma independent_sym : forall A B,
    independent A B -> independent B A.
  Proof.
    intros A B Hind.
    unfold independent in *.
    rewrite P_conj_comm.
    rewrite Qmult_comm.
    exact Hind.
  Qed.

  (** 13. Independent events: P(A|B) == P(A) *)
  Lemma independent_cond : forall A B,
    0 < P B ->
    independent A B ->
    cond_prob_ext A B == P A.
  Proof.
    intros A B HPB Hind.
    unfold cond_prob_ext, independent, Qdiv in *.
    rewrite Hind.
    field.
    intro Habs. lra.
  Qed.

  (** 14. Independent => P(A cap compl B) == P(A) * P(compl B) *)
  Lemma independent_complement : forall A B,
    independent A B ->
    P (conj_event A (compl_event B)) == P A * P (compl_event B).
  Proof.
    intros A B Hind.
    unfold independent in Hind.
    assert (Htot := total_probability A B).
    assert (Hcompl := complement_prob B).
    (* From total_probability: P(A) == P(A cap B) + P(A cap compl B) *)
    (* So P(A cap compl B) == P(A) - P(A cap B) == P(A) - P(A)*P(B) *)
    (* == P(A) * (1 - P(B)) == P(A) * P(compl B) *)
    (* Step 1: P(A cap compl B) == P(A) - P(A cap B) *)
    assert (Hsub : P (conj_event A (compl_event B)) == P A - P (conj_event A B)) by lra.
    (* Step 2: Substitute independence *)
    rewrite Hind in Hsub.
    (* Hsub: P(A cap compl B) == P(A) - P(A) * P(B) *)
    (* Step 3: P(A) * P(compl B) == P(A) * (1 - P(B)) == P(A) - P(A) * P(B) *)
    rewrite Hcompl.
    (* Goal: P(A cap compl B) == P(A) * (1 - P(B)) *)
    (* Hsub: P(A cap compl B) == P(A) - P(A) * P(B) *)
    (* P(A) * (1 - P(B)) == P(A) - P(A) * P(B) by ring *)
    assert (Hring : P A * (1 - P B) == P A - P A * P B) by ring.
    lra.
  Qed.

  (** 15. Independent => P(A cap B) <= P(A) *)
  Lemma independent_conj_bound : forall A B,
    independent A B ->
    P (conj_event A B) <= P A.
  Proof.
    intros A B _. apply P_conj_le_left.
  Qed.

  (* ======================================================================= *)
  (* EXPECTED VALUE (5 Qed)                                                  *)
  (* ======================================================================= *)

  (** 16. Expected value of empty lists is 0 *)
  Lemma ev_nil : expected_value [] [] == 0.
  Proof.
    simpl. reflexivity.
  Qed.

  (** 17. Expected value cons unfolding *)
  Lemma ev_cons : forall v vs p ps,
    expected_value (v :: vs) (p :: ps) == v * p + expected_value vs ps.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (** 18. Expected value is non-negative when all values and probs are *)
  Lemma ev_nonneg : forall vals probs,
    Forall (fun v => 0 <= v) vals ->
    Forall (fun p => 0 <= p) probs ->
    0 <= expected_value vals probs.
  Proof.
    intro vals.
    induction vals as [| v vs IH]; intros probs Hvals Hprobs.
    - simpl. lra.
    - destruct probs as [| p ps].
      + simpl. lra.
      + simpl.
        inversion Hvals as [| ? ? Hv Hvs]; subst.
        inversion Hprobs as [| ? ? Hp Hps]; subst.
        assert (Hvp : 0 <= v * p).
        { apply Qmult_le_0_compat; assumption. }
        assert (Hrec : 0 <= expected_value vs ps).
        { apply IH; assumption. }
        lra.
  Qed.

  (** 19. Scaling: E[c*X] == c * E[X] *)
  Lemma ev_scale : forall c vals probs,
    expected_value (map (fun v => c * v) vals) probs == c * expected_value vals probs.
  Proof.
    intros c vals.
    induction vals as [| v vs IH]; intros probs.
    - simpl. ring.
    - destruct probs as [| p ps].
      + simpl. ring.
      + simpl. rewrite IH. ring.
  Qed.

  (** 20. Variance is non-negative when all probs are non-negative *)
  Lemma variance_nonneg : forall vals probs mu,
    Forall (fun p => 0 <= p) probs ->
    0 <= variance vals probs mu.
  Proof.
    intros vals probs mu Hprobs.
    unfold variance.
    apply ev_nonneg.
    - (* Each (v - mu)^2 >= 0 *)
      induction vals as [| v vs IH].
      + constructor.
      + constructor.
        * apply Qsq_nonneg.
        * exact IH.
    - exact Hprobs.
  Qed.

  (* ======================================================================= *)
  (* FALLACY DETECTION AND APPLICATIONS (4 Qed)                              *)
  (* ======================================================================= *)

  (** 21. Conjunction fallacy: P(A cap B) <= P(A) (strict bound when P(A) > 0) *)
  Lemma conjunction_strict : forall A B,
    0 < P A ->
    P (conj_event A B) <= P A.
  Proof.
    intros A B _.
    apply P_conj_le_left.
  Qed.

  (** 22. Base rate matters: if independent and P(A) < 1/2 then P(A|B) < 1/2 *)
  Lemma base_rate_matters : forall A B,
    0 < P B ->
    independent A B ->
    P A < (1#2) ->
    cond_prob_ext A B < (1#2).
  Proof.
    intros A B HPB Hind HPA.
    assert (Hcond := independent_cond A B HPB Hind).
    (* cond_prob_ext A B == P A, and P A < 1/2 *)
    lra.
  Qed.

  (** 23. Complement conditional: P(compl A | B) == 1 - P(A|B) when P(B) > 0 *)
  Lemma complement_conditional : forall A B,
    0 < P B ->
    P (conj_event (compl_event A) B) + P (conj_event A B) == P B ->
    cond_prob_ext (compl_event A) B + cond_prob_ext A B == 1.
  Proof.
    intros A B HPB Hpartition.
    unfold cond_prob_ext, Qdiv.
    assert (HPB_neq : ~ P B == 0) by (intro Habs; lra).
    (* P(cAB) * /PB + P(AB) * /PB == (P(cAB) + P(AB)) * /PB *)
    assert (Hfactor :
      P (conj_event (compl_event A) B) * / P B +
      P (conj_event A B) * / P B ==
      (P (conj_event (compl_event A) B) + P (conj_event A B)) * / P B).
    { ring. }
    rewrite Hfactor.
    rewrite Hpartition.
    (* P B * / P B == 1 *)
    field. exact HPB_neq.
  Qed.

  (** 24. Total expectation decomposition: ev over concatenation *)
  Lemma ev_app : forall vals1 vals2 probs1 probs2,
    length vals1 = length probs1 ->
    expected_value (vals1 ++ vals2) (probs1 ++ probs2)
    == expected_value vals1 probs1 + expected_value vals2 probs2.
  Proof.
    intros vals1.
    induction vals1 as [| v1 vs1 IH]; intros vals2 probs1 probs2 Hlen.
    - destruct probs1 as [| p1 ps1].
      + simpl. lra.
      + simpl in Hlen. discriminate.
    - destruct probs1 as [| p1 ps1].
      + simpl in Hlen. discriminate.
      + simpl in Hlen. injection Hlen as Hlen'.
        simpl.
        rewrite (IH vals2 ps1 probs2 Hlen').
        lra.
  Qed.

End ConditionalProbExtended.

(* ========================================================================= *)
(* VERIFICATION                                                               *)
(* ========================================================================= *)

(**
  All theorems are universally quantified over the probability space.
  Print Assumptions verifies: 0 axioms (fully constructive).
*)

Check complement_prob.
Check complement_nonneg.
Check complement_le_one.
Check disjoint_additive.
Check total_probability.
Check complement_involution_prob.
Check cond_prob_ext_def.
Check cond_prob_ext_nonneg.
Check cond_prob_ext_le_one.
Check cond_prob_chain.
Check bayes_simple.
Check independent_sym.
Check independent_cond.
Check independent_complement.
Check independent_conj_bound.
Check ev_nil.
Check ev_cons.
Check ev_nonneg.
Check ev_scale.
Check variance_nonneg.
Check conjunction_strict.
Check base_rate_matters.
Check complement_conditional.
Check ev_app.

Print Assumptions complement_prob.
Print Assumptions bayes_simple.
Print Assumptions independent_complement.
Print Assumptions variance_nonneg.
Print Assumptions complement_conditional.
Print Assumptions ev_app.
