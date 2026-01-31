(* ========================================================================= *)
(*        DOMAIN VIOLATIONS: COMPLETE TAXONOMY (Article 5)                  *)
(*                                                                          *)
(*  Formal specification of all 105 Type 2 fallacies across six domains.    *)
(*  Complete catalog from "Domain Violations: A Systematic Taxonomy"        *)
(*                                                                          *)
(*  Author: Horsocrates | Version: 2.0 | Date: January 2026                 *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Import ListNotations.

(* ========================================================================= *)
(*                    PART I: DOMAIN STRUCTURE                              *)
(* ========================================================================= *)

Inductive Domain : Type :=
  | D1_Recognition : Domain
  | D2_Clarification : Domain
  | D3_FrameworkSelection : Domain
  | D4_Comparison : Domain
  | D5_Inference : Domain
  | D6_Reflection : Domain.

Definition domain_index (d : Domain) : nat :=
  match d with
  | D1_Recognition => 1
  | D2_Clarification => 2
  | D3_FrameworkSelection => 3
  | D4_Comparison => 4
  | D5_Inference => 5
  | D6_Reflection => 6
  end.

(* ========================================================================= *)
(*                    PART II: FAILURE MODES BY DOMAIN                      *)
(* ========================================================================= *)

(** Domain 1: Recognition - 5 failure modes, 26 fallacies *)
Inductive D1_FailureMode : Type :=
  | D1_ObjectDeformation : D1_FailureMode      (* A → A' : 2 fallacies *)
  | D1_ObjectSubstitution : D1_FailureMode     (* A → B : 16 fallacies *)
  | D1_DataFiltration : D1_FailureMode         (* Selective : 5 fallacies *)
  | D1_Projection : D1_FailureMode             (* Imposing : 2 fallacies *)
  | D1_SourceDistortion : D1_FailureMode.      (* Corrupted : 1 fallacy *)

(** Domain 2: Clarification - 4 failure modes, 13 fallacies *)
Inductive D2_FailureMode : Type :=
  | D2_MeaningDrift : D2_FailureMode           (* 7 fallacies *)
  | D2_HiddenAgent : D2_FailureMode            (* 1 fallacy *)
  | D2_IncompleteAnalysis : D2_FailureMode     (* 3 fallacies *)
  | D2_ExcessiveAnalysis : D2_FailureMode.     (* 2 fallacies *)

(** Domain 3: Framework Selection - 3 failure modes, 16 fallacies *)
Inductive D3_FailureMode : Type :=
  | D3_CategoryMismatch : D3_FailureMode       (* 3 fallacies *)
  | D3_IrrelevantCriterion : D3_FailureMode    (* 9 fallacies *)
  | D3_FrameworkForResult : D3_FailureMode.    (* 4 fallacies *)

(** Domain 4: Comparison - 3 failure modes, 8 fallacies *)
Inductive D4_FailureMode : Type :=
  | D4_FalseEquation : D4_FailureMode          (* 4 fallacies *)
  | D4_UnstableCriteria : D4_FailureMode       (* 3 fallacies *)
  | D4_ComparisonWithNonexistent : D4_FailureMode. (* 1 fallacy *)

(** Domain 5: Inference - 4 failure modes, 20 fallacies *)
Inductive D5_FailureMode : Type :=
  | D5_LogicalGap : D5_FailureMode             (* 1 fallacy *)
  | D5_CausalError : D5_FailureMode            (* 7 fallacies *)
  | D5_ChainError : D5_FailureMode             (* 2 fallacies *)
  | D5_ScaleError : D5_FailureMode.            (* 10 fallacies *)

(** Domain 6: Reflection - 4 failure modes, 22 fallacies *)
Inductive D6_FailureMode : Type :=
  | D6_IllusionOfCompletion : D6_FailureMode   (* 6 fallacies *)
  | D6_SelfAssessmentDistortion : D6_FailureMode (* 2 fallacies *)
  | D6_PastInvestmentInfluence : D6_FailureMode  (* 2 fallacies *)
  | D6_ImmunizationFromTesting : D6_FailureMode. (* 12 fallacies *)

(** Unified failure mode type *)
Inductive FailureMode : Type :=
  | FM_D1 : D1_FailureMode -> FailureMode
  | FM_D2 : D2_FailureMode -> FailureMode
  | FM_D3 : D3_FailureMode -> FailureMode
  | FM_D4 : D4_FailureMode -> FailureMode
  | FM_D5 : D5_FailureMode -> FailureMode
  | FM_D6 : D6_FailureMode -> FailureMode.

Definition failure_mode_domain (fm : FailureMode) : Domain :=
  match fm with
  | FM_D1 _ => D1_Recognition
  | FM_D2 _ => D2_Clarification
  | FM_D3 _ => D3_FrameworkSelection
  | FM_D4 _ => D4_Comparison
  | FM_D5 _ => D5_Inference
  | FM_D6 _ => D6_Reflection
  end.

(* ========================================================================= *)
(*                    PART III: FALLACY IDENTIFIERS                         *)
(* ========================================================================= *)

(** Domain 1: Recognition - 26 fallacies *)
Inductive D1_Fallacy : Type :=
  (* 2.1.1 Object Deformation (2) *)
  | F_StrawMan | F_RedHerring
  (* 2.1.2 Object Substitution (16) *)
  | F_AdHominem | F_ArgumentFromMotives | F_BloodThickerThanWater
  | F_GuiltByAssociation | F_IdentityFallacy | F_JustPlainFolks
  | F_NameCalling | F_OlfactoryRhetoric | F_Othering | F_Paternalism
  | F_ReductioAdHitlerum | F_RomanticRebel | F_StarPower | F_TonePolicing
  | F_TransferNameDropping | F_TuQuoque
  (* 2.1.3 Data Filtration (5) *)
  | F_AvailabilityBias | F_DisciplinaryBlinders | F_HalfTruth
  | F_LyingWithStatistics | F_NIMBYFallacy
  (* 2.1.4 Projection (2) *)
  | F_MindReading | F_PollyannaPrinciple
  (* 2.1.5 Source Distortion (1) *)
  | F_Brainwashing.

(** Domain 2: Clarification - 13 fallacies *)
Inductive D2_Fallacy : Type :=
  (* 2.2.1 Meaning Drift (7) *)
  | F_ActionsHaveConsequences | F_DiminishedResponsibility | F_Equivocation
  | F_EtymologicalFallacy | F_HeroesAll | F_PoliticalCorrectness | F_Reification
  (* 2.2.2 Hidden Agent (1) *)
  | F_PassiveVoiceFallacy
  (* 2.2.3 Incomplete Analysis (3) *)
  | F_EitherOrReasoning | F_PlainTruthFallacy | F_Reductionism
  (* 2.2.4 Excessive Analysis (2) *)
  | F_Overexplanation | F_SnowJob.

(** Domain 3: Framework Selection - 16 fallacies *)
Inductive D3_Fallacy : Type :=
  (* 2.3.1 Category Mismatch (3) *)
  | F_EschatologicalFallacy | F_MeasurabilityFallacy | F_ProcrusteanFallacy
  (* 2.3.2 Irrelevant Criterion (9) *)
  | F_Ableism | F_AffectiveFallacy | F_AppealToNature | F_AppealToTradition
  | F_BandwagonFallacy | F_CostBias | F_EForEffort | F_Mortification | F_SoldiersHonor
  (* 2.3.3 Framework for Result (4) *)
  | F_BigButFallacy | F_MoralLicensing | F_MoralSuperiority | F_MovingGoalposts.

(** Domain 4: Comparison - 8 fallacies *)
Inductive D4_Fallacy : Type :=
  (* 2.4.1 False Equation (4) *)
  | F_FalseAnalogy | F_ScoringFallacy | F_SimpletonsFallacy | F_TwoSidesFallacy
  (* 2.4.2 Unstable Criteria (3) *)
  | F_FundamentalAttributionError | F_MovingGoalpostsD4 | F_WorstNegatesTheBad
  (* 2.4.3 Comparison with Nonexistent (1) *)
  | F_HeroBusting.

(** Domain 5: Inference - 20 fallacies *)
Inductive D5_Fallacy : Type :=
  (* 2.5.1 Logical Gap (1) *)
  | F_NonSequitur
  (* 2.5.2 Causal Error (7) *)
  | F_JobsComforter | F_MagicalThinking | F_Personalization
  | F_PositiveThinkingFallacy | F_PostHoc | F_Scapegoating | F_TrustYourGut
  (* 2.5.3 Chain Error (2) *)
  | F_ExcludedMiddle | F_SlipperySlope
  (* 2.5.4 Scale Error (10) *)
  | F_ArgumentFromConsequences | F_ArgumentFromIgnorance | F_ArgumentumExSilentio
  | F_DrawYourOwnConclusion | F_HoylesFallacy | F_Overgeneralization
  | F_SilentMajority | F_WhereTheresSmoke | F_WisdomOfTheCrowd | F_WorstCaseFallacy.

(** Domain 6: Reflection - 22 fallacies *)
Inductive D6_Fallacy : Type :=
  (* 2.6.1 Illusion of Completion (6) *)
  | F_AppealToClosure | F_DefaultBias | F_Essentializing
  | F_LawOfUnintendedConsequences | F_NothingNewUnderTheSun | F_ParalysisOfAnalysis
  (* 2.6.2 Self-Assessment Distortion (2) *)
  | F_DunningKrugerEffect | F_SunkCostFallacy
  (* 2.6.3 Past Investment Influence (2) *)
  | F_ArgumentFromInertia | F_Defensiveness
  (* 2.6.4 Immunization from Testing (12) *)
  | F_ArgumentFromIncredulity | F_CallingCards | F_DeliberateIgnorance
  | F_FinishTheJob | F_FreeSpeechFallacy | F_MagicWandFallacy | F_MYOB
  | F_NonRecognition | F_SendingTheWrongMessage | F_TheyreAllCrooks
  | F_ThirdPersonEffect | F_Venting.

(** Unified fallacy type *)
Inductive Fallacy : Type :=
  | Fallacy_D1 : D1_Fallacy -> Fallacy
  | Fallacy_D2 : D2_Fallacy -> Fallacy
  | Fallacy_D3 : D3_Fallacy -> Fallacy
  | Fallacy_D4 : D4_Fallacy -> Fallacy
  | Fallacy_D5 : D5_Fallacy -> Fallacy
  | Fallacy_D6 : D6_Fallacy -> Fallacy.

(* ========================================================================= *)
(*                    PART IV: FAILURE MODE ASSIGNMENT                      *)
(* ========================================================================= *)

Definition d1_failure_mode (f : D1_Fallacy) : D1_FailureMode :=
  match f with
  | F_StrawMan | F_RedHerring => D1_ObjectDeformation
  | F_AdHominem | F_ArgumentFromMotives | F_BloodThickerThanWater
  | F_GuiltByAssociation | F_IdentityFallacy | F_JustPlainFolks
  | F_NameCalling | F_OlfactoryRhetoric | F_Othering | F_Paternalism
  | F_ReductioAdHitlerum | F_RomanticRebel | F_StarPower | F_TonePolicing
  | F_TransferNameDropping | F_TuQuoque => D1_ObjectSubstitution
  | F_AvailabilityBias | F_DisciplinaryBlinders | F_HalfTruth
  | F_LyingWithStatistics | F_NIMBYFallacy => D1_DataFiltration
  | F_MindReading | F_PollyannaPrinciple => D1_Projection
  | F_Brainwashing => D1_SourceDistortion
  end.

Definition d2_failure_mode (f : D2_Fallacy) : D2_FailureMode :=
  match f with
  | F_ActionsHaveConsequences | F_DiminishedResponsibility | F_Equivocation
  | F_EtymologicalFallacy | F_HeroesAll | F_PoliticalCorrectness
  | F_Reification => D2_MeaningDrift
  | F_PassiveVoiceFallacy => D2_HiddenAgent
  | F_EitherOrReasoning | F_PlainTruthFallacy | F_Reductionism => D2_IncompleteAnalysis
  | F_Overexplanation | F_SnowJob => D2_ExcessiveAnalysis
  end.

Definition d3_failure_mode (f : D3_Fallacy) : D3_FailureMode :=
  match f with
  | F_EschatologicalFallacy | F_MeasurabilityFallacy 
  | F_ProcrusteanFallacy => D3_CategoryMismatch
  | F_Ableism | F_AffectiveFallacy | F_AppealToNature | F_AppealToTradition
  | F_BandwagonFallacy | F_CostBias | F_EForEffort | F_Mortification
  | F_SoldiersHonor => D3_IrrelevantCriterion
  | F_BigButFallacy | F_MoralLicensing | F_MoralSuperiority
  | F_MovingGoalposts => D3_FrameworkForResult
  end.

Definition d4_failure_mode (f : D4_Fallacy) : D4_FailureMode :=
  match f with
  | F_FalseAnalogy | F_ScoringFallacy | F_SimpletonsFallacy
  | F_TwoSidesFallacy => D4_FalseEquation
  | F_FundamentalAttributionError | F_MovingGoalpostsD4
  | F_WorstNegatesTheBad => D4_UnstableCriteria
  | F_HeroBusting => D4_ComparisonWithNonexistent
  end.

Definition d5_failure_mode (f : D5_Fallacy) : D5_FailureMode :=
  match f with
  | F_NonSequitur => D5_LogicalGap
  | F_JobsComforter | F_MagicalThinking | F_Personalization
  | F_PositiveThinkingFallacy | F_PostHoc | F_Scapegoating
  | F_TrustYourGut => D5_CausalError
  | F_ExcludedMiddle | F_SlipperySlope => D5_ChainError
  | F_ArgumentFromConsequences | F_ArgumentFromIgnorance
  | F_ArgumentumExSilentio | F_DrawYourOwnConclusion | F_HoylesFallacy
  | F_Overgeneralization | F_SilentMajority | F_WhereTheresSmoke
  | F_WisdomOfTheCrowd | F_WorstCaseFallacy => D5_ScaleError
  end.

Definition d6_failure_mode (f : D6_Fallacy) : D6_FailureMode :=
  match f with
  | F_AppealToClosure | F_DefaultBias | F_Essentializing
  | F_LawOfUnintendedConsequences | F_NothingNewUnderTheSun
  | F_ParalysisOfAnalysis => D6_IllusionOfCompletion
  | F_DunningKrugerEffect | F_SunkCostFallacy => D6_SelfAssessmentDistortion
  | F_ArgumentFromInertia | F_Defensiveness => D6_PastInvestmentInfluence
  | F_ArgumentFromIncredulity | F_CallingCards | F_DeliberateIgnorance
  | F_FinishTheJob | F_FreeSpeechFallacy | F_MagicWandFallacy | F_MYOB
  | F_NonRecognition | F_SendingTheWrongMessage | F_TheyreAllCrooks
  | F_ThirdPersonEffect | F_Venting => D6_ImmunizationFromTesting
  end.

Definition fallacy_failure_mode (f : Fallacy) : FailureMode :=
  match f with
  | Fallacy_D1 f1 => FM_D1 (d1_failure_mode f1)
  | Fallacy_D2 f2 => FM_D2 (d2_failure_mode f2)
  | Fallacy_D3 f3 => FM_D3 (d3_failure_mode f3)
  | Fallacy_D4 f4 => FM_D4 (d4_failure_mode f4)
  | Fallacy_D5 f5 => FM_D5 (d5_failure_mode f5)
  | Fallacy_D6 f6 => FM_D6 (d6_failure_mode f6)
  end.

Definition fallacy_domain (f : Fallacy) : Domain :=
  failure_mode_domain (fallacy_failure_mode f).

(* ========================================================================= *)
(*                    PART V: COUNTING AND VERIFICATION                     *)
(* ========================================================================= *)

Definition all_D1 : list D1_Fallacy := [
  F_StrawMan; F_RedHerring;
  F_AdHominem; F_ArgumentFromMotives; F_BloodThickerThanWater;
  F_GuiltByAssociation; F_IdentityFallacy; F_JustPlainFolks;
  F_NameCalling; F_OlfactoryRhetoric; F_Othering; F_Paternalism;
  F_ReductioAdHitlerum; F_RomanticRebel; F_StarPower; F_TonePolicing;
  F_TransferNameDropping; F_TuQuoque;
  F_AvailabilityBias; F_DisciplinaryBlinders; F_HalfTruth;
  F_LyingWithStatistics; F_NIMBYFallacy;
  F_MindReading; F_PollyannaPrinciple;
  F_Brainwashing
].

Definition all_D2 : list D2_Fallacy := [
  F_ActionsHaveConsequences; F_DiminishedResponsibility; F_Equivocation;
  F_EtymologicalFallacy; F_HeroesAll; F_PoliticalCorrectness; F_Reification;
  F_PassiveVoiceFallacy;
  F_EitherOrReasoning; F_PlainTruthFallacy; F_Reductionism;
  F_Overexplanation; F_SnowJob
].

Definition all_D3 : list D3_Fallacy := [
  F_EschatologicalFallacy; F_MeasurabilityFallacy; F_ProcrusteanFallacy;
  F_Ableism; F_AffectiveFallacy; F_AppealToNature; F_AppealToTradition;
  F_BandwagonFallacy; F_CostBias; F_EForEffort; F_Mortification; F_SoldiersHonor;
  F_BigButFallacy; F_MoralLicensing; F_MoralSuperiority; F_MovingGoalposts
].

Definition all_D4 : list D4_Fallacy := [
  F_FalseAnalogy; F_ScoringFallacy; F_SimpletonsFallacy; F_TwoSidesFallacy;
  F_FundamentalAttributionError; F_MovingGoalpostsD4; F_WorstNegatesTheBad;
  F_HeroBusting
].

Definition all_D5 : list D5_Fallacy := [
  F_NonSequitur;
  F_JobsComforter; F_MagicalThinking; F_Personalization;
  F_PositiveThinkingFallacy; F_PostHoc; F_Scapegoating; F_TrustYourGut;
  F_ExcludedMiddle; F_SlipperySlope;
  F_ArgumentFromConsequences; F_ArgumentFromIgnorance; F_ArgumentumExSilentio;
  F_DrawYourOwnConclusion; F_HoylesFallacy; F_Overgeneralization;
  F_SilentMajority; F_WhereTheresSmoke; F_WisdomOfTheCrowd; F_WorstCaseFallacy
].

Definition all_D6 : list D6_Fallacy := [
  F_AppealToClosure; F_DefaultBias; F_Essentializing;
  F_LawOfUnintendedConsequences; F_NothingNewUnderTheSun; F_ParalysisOfAnalysis;
  F_DunningKrugerEffect; F_SunkCostFallacy;
  F_ArgumentFromInertia; F_Defensiveness;
  F_ArgumentFromIncredulity; F_CallingCards; F_DeliberateIgnorance;
  F_FinishTheJob; F_FreeSpeechFallacy; F_MagicWandFallacy; F_MYOB;
  F_NonRecognition; F_SendingTheWrongMessage; F_TheyreAllCrooks;
  F_ThirdPersonEffect; F_Venting
].

(** Count verification - matches Article 5 exactly *)
Lemma D1_count : List.length all_D1 = 26. Proof. reflexivity. Qed.
Lemma D2_count : List.length all_D2 = 13. Proof. reflexivity. Qed.
Lemma D3_count : List.length all_D3 = 16. Proof. reflexivity. Qed.
Lemma D4_count : List.length all_D4 = 8. Proof. reflexivity. Qed.
Lemma D5_count : List.length all_D5 = 20. Proof. reflexivity. Qed.
Lemma D6_count : List.length all_D6 = 22. Proof. reflexivity. Qed.

Definition total_fallacies : nat :=
  List.length all_D1 + List.length all_D2 + List.length all_D3 +
  List.length all_D4 + List.length all_D5 + List.length all_D6.

Theorem total_is_105 : total_fallacies = 105.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART VI: E/R/R INTERPRETATION                         *)
(* ========================================================================= *)

Inductive ERR_Component : Type :=
  | ERR_Element : ERR_Component
  | ERR_Role : ERR_Component
  | ERR_Rule : ERR_Component.

Definition failure_mode_primary_corruption (fm : FailureMode) : ERR_Component :=
  match fm with
  | FM_D1 _ => ERR_Element
  | FM_D2 _ => ERR_Role
  | FM_D3 _ => ERR_Rule
  | FM_D4 D4_FalseEquation => ERR_Element
  | FM_D4 D4_UnstableCriteria => ERR_Rule
  | FM_D4 D4_ComparisonWithNonexistent => ERR_Element
  | FM_D5 _ => ERR_Rule
  | FM_D6 _ => ERR_Rule
  end.

Theorem D1_corrupts_elements : forall f : D1_Fallacy,
  failure_mode_primary_corruption (FM_D1 (d1_failure_mode f)) = ERR_Element.
Proof. intros f. reflexivity. Qed.

Theorem D2_corrupts_roles : forall f : D2_Fallacy,
  failure_mode_primary_corruption (FM_D2 (d2_failure_mode f)) = ERR_Role.
Proof. intros f. reflexivity. Qed.

Theorem D3_corrupts_rules : forall f : D3_Fallacy,
  failure_mode_primary_corruption (FM_D3 (d3_failure_mode f)) = ERR_Rule.
Proof. intros f. reflexivity. Qed.

Theorem D5_corrupts_rules : forall f : D5_Fallacy,
  failure_mode_primary_corruption (FM_D5 (d5_failure_mode f)) = ERR_Rule.
Proof. intros f. reflexivity. Qed.

Theorem D6_corrupts_rules : forall f : D6_Fallacy,
  failure_mode_primary_corruption (FM_D6 (d6_failure_mode f)) = ERR_Rule.
Proof. intros f. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART VII: DISTRIBUTION ANALYSIS                       *)
(* ========================================================================= *)

Definition domain_fallacy_count (d : Domain) : nat :=
  match d with
  | D1_Recognition => 26
  | D2_Clarification => 13
  | D3_FrameworkSelection => 16
  | D4_Comparison => 8
  | D5_Inference => 20
  | D6_Reflection => 22
  end.

Theorem D1_D6_largest : 
  domain_fallacy_count D1_Recognition >= domain_fallacy_count D2_Clarification /\
  domain_fallacy_count D1_Recognition >= domain_fallacy_count D3_FrameworkSelection /\
  domain_fallacy_count D1_Recognition >= domain_fallacy_count D4_Comparison /\
  domain_fallacy_count D1_Recognition >= domain_fallacy_count D5_Inference /\
  domain_fallacy_count D6_Reflection >= domain_fallacy_count D2_Clarification /\
  domain_fallacy_count D6_Reflection >= domain_fallacy_count D3_FrameworkSelection /\
  domain_fallacy_count D6_Reflection >= domain_fallacy_count D4_Comparison.
Proof. repeat split; simpl; lia. Qed.

Theorem D4_smallest :
  domain_fallacy_count D4_Comparison <= domain_fallacy_count D1_Recognition /\
  domain_fallacy_count D4_Comparison <= domain_fallacy_count D2_Clarification /\
  domain_fallacy_count D4_Comparison <= domain_fallacy_count D3_FrameworkSelection /\
  domain_fallacy_count D4_Comparison <= domain_fallacy_count D5_Inference /\
  domain_fallacy_count D4_Comparison <= domain_fallacy_count D6_Reflection.
Proof. repeat split; simpl; lia. Qed.

(* ========================================================================= *)
(*                    PART VIII: KEY THEOREMS                               *)
(* ========================================================================= *)

Theorem fallacy_unique_domain : forall f : Fallacy,
  exists d : Domain, fallacy_domain f = d.
Proof. intros f. exists (fallacy_domain f). reflexivity. Qed.

Theorem domain_failure_mode_consistent : forall f : Fallacy,
  failure_mode_domain (fallacy_failure_mode f) = fallacy_domain f.
Proof. intros f. unfold fallacy_domain. reflexivity. Qed.

Theorem failure_mode_corrupts_err : forall fm : FailureMode,
  failure_mode_primary_corruption fm = ERR_Element \/
  failure_mode_primary_corruption fm = ERR_Role \/
  failure_mode_primary_corruption fm = ERR_Rule.
Proof.
  intros fm.
  destruct fm as [d1 | d2 | d3 | d4 | d5 | d6].
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
  - destruct d4; try (left; reflexivity); right; right; reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
Qed.

(* ========================================================================= *)
(*                    SUMMARY                                               *)
(* ========================================================================= *)

(**
   COMPLETE DOMAIN VIOLATIONS FORMALIZATION (Article 5)
   ====================================================
   
   105 FALLACIES across 6 DOMAINS:
   
   D1 Recognition:      26 fallacies (25%) - 5 failure modes
   D2 Clarification:    13 fallacies (12%) - 4 failure modes  
   D3 Framework:        16 fallacies (15%) - 3 failure modes
   D4 Comparison:        8 fallacies (8%)  - 3 failure modes
   D5 Inference:        20 fallacies (19%) - 4 failure modes
   D6 Reflection:       22 fallacies (21%) - 4 failure modes
   
   TOTAL: 105 fallacies, 23 failure modes
   
   E/R/R PATTERN:
   - D1 → Elements (what is perceived)
   - D2 → Roles (how things are understood)
   - D3-D6 → Rules (how processing proceeds)
   
   DISTRIBUTION:
   - D1 + D6 largest: Foundation and self-reflection most vulnerable
   - D4 smallest: Comparison is most constrained operation
   
   All counts machine-verified to match Article 5 exactly.
*)

