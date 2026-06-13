(** * KnowledgeError.v — error by ORIGIN: a staged taxonomy of where the knowledge pipeline can go
      wrong (registration / unpacking / confidence / false source), with the deep result that a
      faithful pipeline does NOT guarantee truth

    Built on the AUTHOR'S taxonomy of error origins (2026-06-13).  Errors are not a single thing;
    they ENTER at different stages of the pipeline источник -> данные -> информация -> знание:

      (E1) REGISTRATION error  (источник -> данные): the channel / filter corrupts the data at the
                               moment of recording.                         [KnowledgeInteraction]
      (E2) UNPACKING error     (данные -> информация): the extraction of information from the data is
                               wrong — two sub-origins: the PERCEPTION filter, or the MENTAL
                               (reasoning) step.                            [KnowledgeInformation]
      (E3) CONFIDENCE error    (информация -> знание): accepting as knowledge WITHOUT fulfilling the
                               ЗДО — the overclaim.  A STATUS error, not a value error.
                                                                            [KnowledgeBelief.overclaim]
      (E4) FALSE-SOURCE error  (the source itself): every processing step was FAITHFUL, yet the result
                               is false BECAUSE the input was false.  No internal discipline catches
                               this — knowledge is only as true as its source.

    Two deep facts fall out: (a) a FAITHFUL pipeline does NOT guarantee truth — with all transforms
    faithful, the output is true IFF the source is true (faithful_pipeline_not_sufficient): processing
    transmits truth, it does not create it; (b) the confidence error is ORTHOGONAL to value: a CORRECT
    value held without ЗДО is a TRUE BELIEF, not knowledge (true_belief_is_not_knowledge — the Gettier
    point).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      R-pipeline (L5 order): knowledge forms by an ORDERED chain источник -> данные -> информация ->
                 знание; each stage is a transform.
      R-fidelity: each stage is faithful (preserves) or faulty (corrupts); an error ENTERS at a stage.
      R-source-dependence (L4 ground): the truth of the output rests on the source — faithful
                 processing TRANSMITS truth but cannot CREATE it (E4).
      R-status (ЗДО): confidence = classification by ground; accepting without ЗДО is a STATUS error
                 (E3), orthogonal to the value.
    Roles (L4): the source = the truth-bearer; reg = registration (channel/filter); perc = the
      perception filter; ment = the mental/reasoning step; the confidence flag = the ЗДО acceptance;
      held_value = the result; error = the divergence; the origin = the faulty stage (or the false
      source).
    Elements (L1+P4): the carried content V; truth, source : V; the stage transforms; ground_met;
      the claimed class.
    P4 diagnostic (could it be otherwise?):
      An error localizes to ONE of five fault points (registration / perception / mental / confidence
      / false-source).  E4 is special: a faithful pipeline does NOT guarantee truth (truth <-> source
      true), so no internal discipline catches a false source.  E3 is orthogonal: a true value can be
      ungrounded (true belief =/= knowledge).  Each stage is an independent point of corruption; the
      source is upstream of all of them — so the taxonomy cannot collapse.
    Honesty wall:
      "perception / mental / confidence" is the INTERPRETATION; the formal shadow is staged transforms
      with per-stage fidelity plus a status flag.  The bridges (registration -> KnowledgeInteraction,
      unpacking -> KnowledgeInformation, confidence E3 -> KnowledgeBelief.overclaim) are in prose.
      The deep core — a faithful pipeline does not guarantee truth — is the honest statement that
      knowledge is only as true as its source.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Bool.

Section Error.
Context {V : Type}.
Variable truth  : V.     (* the actual fact *)
Variable source : V.     (* what the source bears (= truth unless E4) *)
Variable reg  : V -> V.   (* registration: channel / filter *)
Variable perc : V -> V.   (* perception filter *)
Variable ment : V -> V.   (* mental / reasoning *)
Variable ground_met : bool.   (* is the ЗДО for knowledge fulfilled? *)

(** A stage is FAITHFUL when it preserves its content; faulty when it changes it. *)
Definition faithful (f : V -> V) : Prop := forall x, f x = x.

(** The value finally held = source pushed through registration, perception, mental. *)
Definition held_value : V := ment (perc (reg source)).

Definition value_correct : Prop := held_value = truth.
Definition value_error   : Prop := held_value <> truth.

Lemma value_error_iff : value_error <-> ~ value_correct.
Proof. unfold value_error, value_correct. tauto. Qed.

(** ★ The clean pipeline: a true source through faithful stages yields the truth. *)
Theorem clean_pipeline_correct :
  source = truth -> faithful reg -> faithful perc -> faithful ment -> value_correct.
Proof.
  intros Hs Hr Hp Hm. unfold value_correct, held_value.
  rewrite (Hm (perc (reg source))), (Hp (reg source)), (Hr source). exact Hs.
Qed.

(* ===================================================================== *)
(*  E1 — registration error (channel / filter corrupts the data)          *)
(* ===================================================================== *)

(** ★ E1: the registration stage corrupts (reg source =/= truth) while the later stages are
    faithful — the held value is wrong.  Origin: the channel / filter. *)
Theorem registration_error :
  faithful perc -> faithful ment -> reg source <> truth -> ~ value_correct.
Proof.
  intros Hp Hm Hreg Hc. unfold value_correct, held_value in Hc.
  rewrite (Hm (perc (reg source))), (Hp (reg source)) in Hc. apply Hreg. exact Hc.
Qed.

(* ===================================================================== *)
(*  E2 — unpacking error (perception filter / mental)                     *)
(* ===================================================================== *)

(** ★ E2a: the PERCEPTION filter corrupts (perc (reg source) =/= truth) with the mental stage
    faithful — the held value is wrong.  Origin: the perception filter. *)
Theorem perception_error :
  faithful ment -> perc (reg source) <> truth -> ~ value_correct.
Proof.
  intros Hm Hperc Hc. unfold value_correct, held_value in Hc.
  rewrite (Hm (perc (reg source))) in Hc. apply Hperc. exact Hc.
Qed.

(** ★ E2b: the MENTAL step corrupts — its input was correct (perc (reg source) = truth) but its
    output is not — so the error originates AT the mental stage.  Origin: the reasoning. *)
Theorem mental_error :
  perc (reg source) = truth -> ment (perc (reg source)) <> truth -> ~ value_correct.
Proof.
  intros Hin Hout Hc. unfold value_correct, held_value in Hc. apply Hout. exact Hc.
Qed.

(* ===================================================================== *)
(*  E4 — false source (faithful processing, false input)                  *)
(* ===================================================================== *)

(** ★ E4: every stage is FAITHFUL, yet the result is false because the SOURCE is false. *)
Theorem false_input_error :
  faithful reg -> faithful perc -> faithful ment -> source <> truth -> ~ value_correct.
Proof.
  intros Hr Hp Hm Hsrc Hc. unfold value_correct, held_value in Hc.
  rewrite (Hm (perc (reg source))), (Hp (reg source)), (Hr source) in Hc.
  apply Hsrc. exact Hc.
Qed.

(** ★★★ THE DEEP RESULT: a FAITHFUL pipeline does NOT guarantee truth.  With all transforms
    faithful, the output is correct IFF the source is true — processing TRANSMITS truth, it does not
    CREATE it.  No internal discipline catches a false source; knowledge is only as true as its
    source. *)
Theorem faithful_pipeline_not_sufficient :
  faithful reg -> faithful perc -> faithful ment ->
  (value_correct <-> source = truth).
Proof.
  intros Hr Hp Hm. unfold value_correct, held_value.
  rewrite (Hm (perc (reg source))), (Hp (reg source)), (Hr source). tauto.
Qed.

(* ===================================================================== *)
(*  E3 — confidence error (status, not value): true belief =/= knowledge  *)
(* ===================================================================== *)

(** The confidence error: claiming knowledge without the ЗДО (= KnowledgeBelief.overclaim). *)
Definition confidence_error (claimed_knowledge : bool) : Prop :=
  claimed_knowledge = true /\ ground_met = false.

(** ★★ E3 is ORTHOGONAL to value: a CORRECT value held WITHOUT ЗДО is a TRUE BELIEF, not knowledge.
    Value-truth =/= knowledge-status (the Gettier point). *)
Theorem true_belief_is_not_knowledge :
  value_correct -> ground_met = false -> value_correct /\ confidence_error true.
Proof. intros Hv Hg. split; [ exact Hv | split; [ reflexivity | exact Hg ] ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE — the five fault points                                       *)
(* ===================================================================== *)

(** ★★★ Error by origin: (E1) registration, (E2a) perception, (E2b) mental, (E4) false source — each
    breaks the value; (E3) confidence breaks the status even when the value is correct.  Five
    distinct fault points along one ordered pipeline. *)
Theorem error_origins_capstone :
  (faithful perc -> faithful ment -> reg source <> truth -> ~ value_correct)             (* E1 *)
  /\ (faithful ment -> perc (reg source) <> truth -> ~ value_correct)                    (* E2a *)
  /\ (perc (reg source) = truth -> ment (perc (reg source)) <> truth -> ~ value_correct) (* E2b *)
  /\ (faithful reg -> faithful perc -> faithful ment -> source <> truth -> ~ value_correct) (* E4 *)
  /\ (value_correct -> ground_met = false -> value_correct /\ confidence_error true).    (* E3 *)
Proof.
  split; [ exact registration_error | ].
  split; [ exact perception_error | ].
  split; [ exact mental_error | ].
  split; [ exact false_input_error | exact true_belief_is_not_knowledge ].
Qed.

End Error.

Print Assumptions error_origins_capstone.
Print Assumptions faithful_pipeline_not_sufficient.
Print Assumptions true_belief_is_not_knowledge.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Error by ORIGIN along the pipeline источник->данные->информация->знание:   *)
(*  (E1) registration_error (channel/filter), (E2a) perception_error,         *)
(*  (E2b) mental_error, (E4) false_input_error — each breaks the value;       *)
(*  (E3) confidence (true_belief_is_not_knowledge) breaks the status even when *)
(*  the value is correct (Gettier).  Deep core: a faithful pipeline does NOT  *)
(*  guarantee truth (faithful_pipeline_not_sufficient: correct <-> source     *)
(*  true) — processing transmits truth, never creates it; knowledge is only   *)
(*  as true as its source.  Direction (2) error layer; bridges to            *)
(*  KnowledgeInteraction / KnowledgeInformation / KnowledgeBelief in prose.   *)
(* ========================================================================= *)
