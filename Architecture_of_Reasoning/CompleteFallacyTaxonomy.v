(* ========================================================================= *)
(*           COMPLETE FALLACY TAXONOMY: ALL 156 VIOLATIONS                  *)
(*                                                                          *)
(*  Full formalization of Articles 4 & 5: Architecture of Error             *)
(*                                                                          *)
(*  Type 1: Violations of Conditions (36)                                   *)
(*  Type 2: Domain Violations (105)                                         *)
(*  Type 3: Violations of Sequence (3)                                      *)
(*  Type 4: Syndromes (6)                                                   *)
(*  Type 5: Context-Dependent Methods (6)                                   *)
(*                                                                          *)
(*  TOTAL: 156 fallacies (~150 rounded in articles)                         *)
(*                                                                          *)
(*  Author: Horsocrates | Version: 1.0 | Date: January 2026                 *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ========================================================================= *)
(*                    PART I: TYPE 1 - VIOLATIONS OF CONDITIONS             *)
(* ========================================================================= *)

(**
   Type 1: Reasoning does not begin; manipulation/coercion takes its place.
   
   Subtype 1.A: Defective Questions (3)
   Subtype 1.B: Manipulations (33)
   
   TOTAL: 36 fallacies
*)

(** Subtype 1.A: Defective Questions *)
Inductive T1A_DefectiveQuestion : Type :=
  | T1A_ComplexQuestion : T1A_DefectiveQuestion    (* Loaded Question *)
  | T1A_Taboo : T1A_DefectiveQuestion              (* Dogmatism *)
  | T1A_VenueFallacy : T1A_DefectiveQuestion.      (* Wrong place/time *)

(** Subtype 1.B: Manipulations - by category *)
Inductive T1B_Manipulation : Type :=
  (* 1.B.1 Force (8) *)
  | T1B_AdBaculum : T1B_Manipulation
  | T1B_JustDoIt : T1B_Manipulation
  | T1B_NoDiscussion : T1B_Manipulation
  | T1B_PlausibleDeniability : T1B_Manipulation
  | T1B_ThePout : T1B_Manipulation
  | T1B_StandardVersion : T1B_Manipulation
  | T1B_ThousandFlowers : T1B_Manipulation
  | T1B_TINA : T1B_Manipulation
  (* 1.B.2 Pity (3) *)
  | T1B_AppealToPity : T1B_Manipulation
  | T1B_NarrativeFallacy : T1B_Manipulation
  | T1B_SaveTheChildren : T1B_Manipulation
  (* 1.B.3 Emotion (7) *)
  | T1B_ScareTactics : T1B_Manipulation
  | T1B_DogWhistle : T1B_Manipulation
  | T1B_FBomb : T1B_Manipulation
  | T1B_PlayingOnEmotion : T1B_Manipulation
  | T1B_Prosopology : T1B_Manipulation
  | T1B_ShoppingHungry : T1B_Manipulation
  | T1B_WeHaveToDoSomething : T1B_Manipulation
  (* 1.B.4 Benefit (1) *)
  | T1B_Bribery : T1B_Manipulation
  (* 1.B.5 Pressure (1) *)
  | T1B_Appeasement : T1B_Manipulation
  (* 1.B.6 False Authority (3) *)
  | T1B_AppealToHeaven : T1B_Manipulation
  | T1B_AdMysteriam : T1B_Manipulation
  | T1B_PseudoEsoteric : T1B_Manipulation
  (* 1.B.7 Disinformation (5) *)
  | T1B_BigLie : T1B_Manipulation
  | T1B_AlternativeTruth : T1B_Manipulation
  | T1B_Gaslighting : T1B_Manipulation
  | T1B_Infotainment : T1B_Manipulation
  | T1B_ScriptedMessage : T1B_Manipulation
  (* 1.B.8 Delegation (2) *)
  | T1B_BlindLoyalty : T1B_Manipulation
  | T1B_BigBrainLittleBrain : T1B_Manipulation
  (* 1.B.9 False Ethos (1) *)
  | T1B_AlphabetSoup : T1B_Manipulation
  (* 1.B.10 Bad Faith (2) *)
  | T1B_MalaFides : T1B_Manipulation
  | T1B_OctoberSurprise : T1B_Manipulation.

(** Manipulation subcategory *)
Inductive ManipulationCategory : Type :=
  | MC_Force : ManipulationCategory
  | MC_Pity : ManipulationCategory
  | MC_Emotion : ManipulationCategory
  | MC_Benefit : ManipulationCategory
  | MC_Pressure : ManipulationCategory
  | MC_FalseAuthority : ManipulationCategory
  | MC_Disinformation : ManipulationCategory
  | MC_Delegation : ManipulationCategory
  | MC_FalseEthos : ManipulationCategory
  | MC_BadFaith : ManipulationCategory.

Definition manipulation_category (m : T1B_Manipulation) : ManipulationCategory :=
  match m with
  | T1B_AdBaculum | T1B_JustDoIt | T1B_NoDiscussion | T1B_PlausibleDeniability
  | T1B_ThePout | T1B_StandardVersion | T1B_ThousandFlowers | T1B_TINA => MC_Force
  | T1B_AppealToPity | T1B_NarrativeFallacy | T1B_SaveTheChildren => MC_Pity
  | T1B_ScareTactics | T1B_DogWhistle | T1B_FBomb | T1B_PlayingOnEmotion
  | T1B_Prosopology | T1B_ShoppingHungry | T1B_WeHaveToDoSomething => MC_Emotion
  | T1B_Bribery => MC_Benefit
  | T1B_Appeasement => MC_Pressure
  | T1B_AppealToHeaven | T1B_AdMysteriam | T1B_PseudoEsoteric => MC_FalseAuthority
  | T1B_BigLie | T1B_AlternativeTruth | T1B_Gaslighting 
  | T1B_Infotainment | T1B_ScriptedMessage => MC_Disinformation
  | T1B_BlindLoyalty | T1B_BigBrainLittleBrain => MC_Delegation
  | T1B_AlphabetSoup => MC_FalseEthos
  | T1B_MalaFides | T1B_OctoberSurprise => MC_BadFaith
  end.

(** All Type 1.A fallacies *)
Definition all_T1A : list T1A_DefectiveQuestion := [
  T1A_ComplexQuestion; T1A_Taboo; T1A_VenueFallacy
].

(** All Type 1.B fallacies *)
Definition all_T1B : list T1B_Manipulation := [
  (* Force *)
  T1B_AdBaculum; T1B_JustDoIt; T1B_NoDiscussion; T1B_PlausibleDeniability;
  T1B_ThePout; T1B_StandardVersion; T1B_ThousandFlowers; T1B_TINA;
  (* Pity *)
  T1B_AppealToPity; T1B_NarrativeFallacy; T1B_SaveTheChildren;
  (* Emotion *)
  T1B_ScareTactics; T1B_DogWhistle; T1B_FBomb; T1B_PlayingOnEmotion;
  T1B_Prosopology; T1B_ShoppingHungry; T1B_WeHaveToDoSomething;
  (* Benefit *)
  T1B_Bribery;
  (* Pressure *)
  T1B_Appeasement;
  (* False Authority *)
  T1B_AppealToHeaven; T1B_AdMysteriam; T1B_PseudoEsoteric;
  (* Disinformation *)
  T1B_BigLie; T1B_AlternativeTruth; T1B_Gaslighting; 
  T1B_Infotainment; T1B_ScriptedMessage;
  (* Delegation *)
  T1B_BlindLoyalty; T1B_BigBrainLittleBrain;
  (* False Ethos *)
  T1B_AlphabetSoup;
  (* Bad Faith *)
  T1B_MalaFides; T1B_OctoberSurprise
].

Lemma T1A_count : length all_T1A = 3.
Proof. reflexivity. Qed.

Lemma T1B_count : length all_T1B = 33.
Proof. reflexivity. Qed.

Definition type1_total : nat := length all_T1A + length all_T1B.

Theorem type1_is_36 : type1_total = 36.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART II: TYPE 2 - DOMAIN VIOLATIONS                   *)
(* ========================================================================= *)

(**
   Type 2: Reasoning begins but fails within a specific domain.
   105 fallacies across 6 domains.
*)

Inductive Domain : Type :=
  | D1_Recognition : Domain
  | D2_Clarification : Domain
  | D3_FrameworkSelection : Domain
  | D4_Comparison : Domain
  | D5_Inference : Domain
  | D6_Reflection : Domain.

(** Domain 1: Recognition - 26 fallacies *)
Inductive D1_Fallacy : Type :=
  (* Object Deformation (2) *)
  | D1_StrawMan | D1_RedHerring
  (* Object Substitution (16) *)
  | D1_AdHominem | D1_ArgumentFromMotives | D1_BloodIsThicker
  | D1_GuiltByAssociation | D1_IdentityFallacy | D1_JustPlainFolks
  | D1_NameCalling | D1_OlfactoryRhetoric | D1_Othering
  | D1_Paternalism | D1_ReductioAdHitlerum | D1_RomanticRebel
  | D1_StarPower | D1_TonePolicing | D1_Transfer | D1_TuQuoque
  (* Data Filtration (5) *)
  | D1_AvailabilityBias | D1_DisciplinaryBlinders | D1_HalfTruth
  | D1_LyingWithStatistics | D1_NIMBYFallacy
  (* Projection (2) *)
  | D1_MindReading | D1_PollyannaPrinciple
  (* Source Distortion (1) *)
  | D1_Brainwashing.

(** Domain 2: Clarification - 13 fallacies *)
Inductive D2_Fallacy : Type :=
  (* Meaning Drift (7) *)
  | D2_ActionsHaveConsequences | D2_DiminishedResponsibility
  | D2_Equivocation | D2_EtymologicalFallacy | D2_HeroesAll
  | D2_PoliticalCorrectness | D2_Reification
  (* Hidden Agent (1) *)
  | D2_PassiveVoiceFallacy
  (* Incomplete Analysis (3) *)
  | D2_EitherOrReasoning | D2_PlainTruthFallacy | D2_Reductionism
  (* Excessive Analysis (2) *)
  | D2_Overexplanation | D2_SnowJob.

(** Domain 3: Framework Selection - 16 fallacies *)
Inductive D3_Fallacy : Type :=
  (* Category Mismatch (3) *)
  | D3_EschatologicalFallacy | D3_MeasurabilityFallacy | D3_ProcrusteanFallacy
  (* Irrelevant Criterion (9) *)
  | D3_Ableism | D3_AffectiveFallacy | D3_AppealToNature
  | D3_AppealToTradition | D3_Bandwagon | D3_CostBias
  | D3_EForEffort | D3_Mortification | D3_SoldiersHonor
  (* Framework for Result (4) *)
  | D3_BigButFallacy | D3_MoralLicensing | D3_MoralSuperiority
  | D3_MovingGoalposts.

(** Domain 4: Comparison - 8 fallacies *)
Inductive D4_Fallacy : Type :=
  (* False Equation (4) *)
  | D4_FalseAnalogy | D4_ScoringFallacy | D4_SimpletonsFallacy
  | D4_TwoSidesFallacy
  (* Unstable Criteria (3) *)
  | D4_FundamentalAttributionError | D4_MovingGoalpostsD4
  | D4_WorstNegatesTheBad
  (* Comparison with Nonexistent (1) *)
  | D4_HeroBusting.

(** Domain 5: Inference - 20 fallacies *)
Inductive D5_Fallacy : Type :=
  (* Logical Gap (1) *)
  | D5_NonSequitur
  (* Causal Error (7) *)
  | D5_JobsComforter | D5_MagicalThinking | D5_Personalization
  | D5_PositiveThinkingFallacy | D5_PostHoc | D5_Scapegoating
  | D5_TrustYourGut
  (* Chain Error (2) *)
  | D5_ExcludedMiddle | D5_SlipperySlope
  (* Scale Error (10) *)
  | D5_ArgumentFromConsequences | D5_ArgumentFromIgnorance
  | D5_ArgumentumExSilentio | D5_DrawYourOwnConclusion
  | D5_HoylesFallacy | D5_Overgeneralization | D5_SilentMajority
  | D5_WheresSmoke | D5_WisdomOfCrowd | D5_WorstCaseFallacy.

(** Domain 6: Reflection - 22 fallacies *)
Inductive D6_Fallacy : Type :=
  (* Illusion of Completion (6) *)
  | D6_AppealToClosure | D6_DefaultBias | D6_Essentializing
  | D6_LawOfUnintendedConsequences | D6_NothingNewUnderSun
  | D6_ParalysisOfAnalysis
  (* Self-Assessment Distortion (2) *)
  | D6_DunningKrugerEffect | D6_SunkCostFallacy
  (* Past Investment Influence (2) *)
  | D6_ArgumentFromInertia | D6_Defensiveness
  (* Immunization from Testing (12) *)
  | D6_ArgumentFromIncredulity | D6_CallingCards
  | D6_DeliberateIgnorance | D6_FinishTheJob | D6_FreeSpeechFallacy
  | D6_MagicWandFallacy | D6_MYOB | D6_NonRecognition
  | D6_SendingWrongMessage | D6_TheyreAllCrooks
  | D6_ThirdPersonEffect | D6_Venting.

(** Domain fallacy counts *)
Definition all_D1 : list D1_Fallacy := [
  D1_StrawMan; D1_RedHerring;
  D1_AdHominem; D1_ArgumentFromMotives; D1_BloodIsThicker;
  D1_GuiltByAssociation; D1_IdentityFallacy; D1_JustPlainFolks;
  D1_NameCalling; D1_OlfactoryRhetoric; D1_Othering;
  D1_Paternalism; D1_ReductioAdHitlerum; D1_RomanticRebel;
  D1_StarPower; D1_TonePolicing; D1_Transfer; D1_TuQuoque;
  D1_AvailabilityBias; D1_DisciplinaryBlinders; D1_HalfTruth;
  D1_LyingWithStatistics; D1_NIMBYFallacy;
  D1_MindReading; D1_PollyannaPrinciple;
  D1_Brainwashing
].

Definition all_D2 : list D2_Fallacy := [
  D2_ActionsHaveConsequences; D2_DiminishedResponsibility;
  D2_Equivocation; D2_EtymologicalFallacy; D2_HeroesAll;
  D2_PoliticalCorrectness; D2_Reification;
  D2_PassiveVoiceFallacy;
  D2_EitherOrReasoning; D2_PlainTruthFallacy; D2_Reductionism;
  D2_Overexplanation; D2_SnowJob
].

Definition all_D3 : list D3_Fallacy := [
  D3_EschatologicalFallacy; D3_MeasurabilityFallacy; D3_ProcrusteanFallacy;
  D3_Ableism; D3_AffectiveFallacy; D3_AppealToNature;
  D3_AppealToTradition; D3_Bandwagon; D3_CostBias;
  D3_EForEffort; D3_Mortification; D3_SoldiersHonor;
  D3_BigButFallacy; D3_MoralLicensing; D3_MoralSuperiority;
  D3_MovingGoalposts
].

Definition all_D4 : list D4_Fallacy := [
  D4_FalseAnalogy; D4_ScoringFallacy; D4_SimpletonsFallacy;
  D4_TwoSidesFallacy;
  D4_FundamentalAttributionError; D4_MovingGoalpostsD4;
  D4_WorstNegatesTheBad;
  D4_HeroBusting
].

Definition all_D5 : list D5_Fallacy := [
  D5_NonSequitur;
  D5_JobsComforter; D5_MagicalThinking; D5_Personalization;
  D5_PositiveThinkingFallacy; D5_PostHoc; D5_Scapegoating;
  D5_TrustYourGut;
  D5_ExcludedMiddle; D5_SlipperySlope;
  D5_ArgumentFromConsequences; D5_ArgumentFromIgnorance;
  D5_ArgumentumExSilentio; D5_DrawYourOwnConclusion;
  D5_HoylesFallacy; D5_Overgeneralization; D5_SilentMajority;
  D5_WheresSmoke; D5_WisdomOfCrowd; D5_WorstCaseFallacy
].

Definition all_D6 : list D6_Fallacy := [
  D6_AppealToClosure; D6_DefaultBias; D6_Essentializing;
  D6_LawOfUnintendedConsequences; D6_NothingNewUnderSun;
  D6_ParalysisOfAnalysis;
  D6_DunningKrugerEffect; D6_SunkCostFallacy;
  D6_ArgumentFromInertia; D6_Defensiveness;
  D6_ArgumentFromIncredulity; D6_CallingCards;
  D6_DeliberateIgnorance; D6_FinishTheJob; D6_FreeSpeechFallacy;
  D6_MagicWandFallacy; D6_MYOB; D6_NonRecognition;
  D6_SendingWrongMessage; D6_TheyreAllCrooks;
  D6_ThirdPersonEffect; D6_Venting
].

Lemma D1_count : length all_D1 = 26. Proof. reflexivity. Qed.
Lemma D2_count : length all_D2 = 13. Proof. reflexivity. Qed.
Lemma D3_count : length all_D3 = 16. Proof. reflexivity. Qed.
Lemma D4_count : length all_D4 = 8. Proof. reflexivity. Qed.
Lemma D5_count : length all_D5 = 20. Proof. reflexivity. Qed.
Lemma D6_count : length all_D6 = 22. Proof. reflexivity. Qed.

Definition type2_total : nat := 
  length all_D1 + length all_D2 + length all_D3 + 
  length all_D4 + length all_D5 + length all_D6.

Theorem type2_is_105 : type2_total = 105.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART III: TYPE 3 - VIOLATIONS OF SEQUENCE             *)
(* ========================================================================= *)

(**
   Type 3: Reasoning proceeds in wrong direction.
   3 primary patterns.
*)

Inductive T3_SequenceViolation : Type :=
  | T3_Rationalization : T3_SequenceViolation    (* Reverse: conclusion first *)
  | T3_CircularReasoning : T3_SequenceViolation  (* No progress *)
  | T3_ShiftingBurdenOfProof : T3_SequenceViolation. (* Role inversion *)

Definition all_T3 : list T3_SequenceViolation := [
  T3_Rationalization; T3_CircularReasoning; T3_ShiftingBurdenOfProof
].

Lemma T3_count : length all_T3 = 3.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART IV: TYPE 4 - SYNDROMES                           *)
(* ========================================================================= *)

(**
   Type 4: Systemic distortions pervading the entire process.
   6 syndromes in 2 groups.
*)

Inductive T4_Syndrome : Type :=
  (* Cognitive Dissonance Syndromes (3) *)
  | T4_ConfirmationBias : T4_Syndrome
  | T4_Compartmentalization : T4_Syndrome
  | T4_MotivatedReasoning : T4_Syndrome
  (* Systemic Distortion Syndromes (3) *)
  | T4_EchoChamber : T4_Syndrome
  | T4_CognitiveClosure : T4_Syndrome
  | T4_Groupthink : T4_Syndrome.

Inductive SyndromeCategory : Type :=
  | SC_CognitiveDissonance : SyndromeCategory
  | SC_SystemicDistortion : SyndromeCategory.

Definition syndrome_category (s : T4_Syndrome) : SyndromeCategory :=
  match s with
  | T4_ConfirmationBias | T4_Compartmentalization 
  | T4_MotivatedReasoning => SC_CognitiveDissonance
  | T4_EchoChamber | T4_CognitiveClosure 
  | T4_Groupthink => SC_SystemicDistortion
  end.

Definition all_T4 : list T4_Syndrome := [
  T4_ConfirmationBias; T4_Compartmentalization; T4_MotivatedReasoning;
  T4_EchoChamber; T4_CognitiveClosure; T4_Groupthink
].

Lemma T4_count : length all_T4 = 6.
Proof. reflexivity. Qed.

(** Syndrome characteristics *)
Definition syndrome_pervades_domains (s : T4_Syndrome) : bool := true.
Definition syndrome_self_reinforces (s : T4_Syndrome) : bool := true.
Definition syndrome_invisible_to_afflicted (s : T4_Syndrome) : bool := true.

(* ========================================================================= *)
(*                    PART V: TYPE 5 - CONTEXT-DEPENDENT METHODS            *)
(* ========================================================================= *)

(**
   Type 5: Methods valid in some contexts, fallacious in others.
   6 methods in 3 groups.
*)

Inductive T5_Method : Type :=
  (* Intuitive Cognition (2) *)
  | T5_TrustYourGut : T5_Method      (* Expert intuition *)
  | T5_AffectiveReasoning : T5_Method (* Emotion as value access *)
  (* Traditional Cognition (2) *)
  | T5_AppealToTradition : T5_Method  (* Accumulated wisdom *)
  | T5_AppealToNature : T5_Method     (* Evolutionary optimization *)
  (* Indirect Cognition (2) *)
  | T5_ArgumentFromSilence : T5_Method   (* Inference from absence *)
  | T5_ArgumentFromConsequences : T5_Method. (* Evaluation by outcomes *)

Inductive MethodCategory : Type :=
  | MethC_Intuitive : MethodCategory
  | MethC_Traditional : MethodCategory
  | MethC_Indirect : MethodCategory.

Definition method_category (m : T5_Method) : MethodCategory :=
  match m with
  | T5_TrustYourGut | T5_AffectiveReasoning => MethC_Intuitive
  | T5_AppealToTradition | T5_AppealToNature => MethC_Traditional
  | T5_ArgumentFromSilence | T5_ArgumentFromConsequences => MethC_Indirect
  end.

(** Validity conditions *)
Definition method_valid_condition (m : T5_Method) : nat :=  (* Placeholder *)
  match m with
  | T5_TrustYourGut => 1              (* Expert domain with feedback *)
  | T5_AffectiveReasoning => 2        (* Values/qualities context *)
  | T5_AppealToTradition => 3         (* Tested wisdom, stable conditions *)
  | T5_AppealToNature => 4            (* Evolutionary optimization *)
  | T5_ArgumentFromSilence => 5       (* Silence expected/informative *)
  | T5_ArgumentFromConsequences => 6  (* Ethics/policy context *)
  end.

Definition all_T5 : list T5_Method := [
  T5_TrustYourGut; T5_AffectiveReasoning;
  T5_AppealToTradition; T5_AppealToNature;
  T5_ArgumentFromSilence; T5_ArgumentFromConsequences
].

Lemma T5_count : length all_T5 = 6.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART VI: COMPLETE TAXONOMY                            *)
(* ========================================================================= *)

(** Unified fallacy type *)
Inductive FallacyType : Type :=
  | FT_Type1A : T1A_DefectiveQuestion -> FallacyType
  | FT_Type1B : T1B_Manipulation -> FallacyType
  | FT_Type2_D1 : D1_Fallacy -> FallacyType
  | FT_Type2_D2 : D2_Fallacy -> FallacyType
  | FT_Type2_D3 : D3_Fallacy -> FallacyType
  | FT_Type2_D4 : D4_Fallacy -> FallacyType
  | FT_Type2_D5 : D5_Fallacy -> FallacyType
  | FT_Type2_D6 : D6_Fallacy -> FallacyType
  | FT_Type3 : T3_SequenceViolation -> FallacyType
  | FT_Type4 : T4_Syndrome -> FallacyType
  | FT_Type5 : T5_Method -> FallacyType.

(** Total counts *)
Definition total_type1 : nat := length all_T1A + length all_T1B.
Definition total_type2 : nat := type2_total.
Definition total_type3 : nat := length all_T3.
Definition total_type4 : nat := length all_T4.
Definition total_type5 : nat := length all_T5.

Definition grand_total : nat := 
  total_type1 + total_type2 + total_type3 + total_type4 + total_type5.

(** Main theorem: Total is 156 *)
Theorem complete_taxonomy_156 : grand_total = 156.
Proof. reflexivity. Qed.

(** Breakdown *)
Theorem type_breakdown :
  total_type1 = 36 /\
  total_type2 = 105 /\
  total_type3 = 3 /\
  total_type4 = 6 /\
  total_type5 = 6.
Proof. repeat split; reflexivity. Qed.

(** Type 2 is 70% of non-context-dependent fallacies *)
(* 105 / (36 + 105 + 3 + 6) = 105 / 150 = 70% *)
Definition core_fallacies : nat := total_type1 + total_type2 + total_type3 + total_type4.

Theorem type2_is_70_percent : 
  core_fallacies = 150 /\ total_type2 * 100 / core_fallacies = 70.
Proof. split; reflexivity. Qed.

(* ========================================================================= *)
(*                    PART VII: DISTRIBUTION ANALYSIS                       *)
(* ========================================================================= *)

(** D1 and D6 are most vulnerable *)
Theorem D1_D6_most_fallacies :
  length all_D1 >= length all_D2 /\
  length all_D1 >= length all_D3 /\
  length all_D1 >= length all_D4 /\
  length all_D1 >= length all_D5 /\
  length all_D6 >= length all_D2 /\
  length all_D6 >= length all_D4.
Proof. repeat split; simpl; lia. Qed.

(** D4 has fewest fallacies *)
Theorem D4_most_constrained :
  length all_D4 <= length all_D1 /\
  length all_D4 <= length all_D2 /\
  length all_D4 <= length all_D3 /\
  length all_D4 <= length all_D5 /\
  length all_D4 <= length all_D6.
Proof. repeat split; simpl; lia. Qed.

(** Manipulation is largest Type 1 subcategory *)
Theorem manipulation_dominates_type1 :
  length all_T1B > length all_T1A * 10.
Proof. simpl. lia. Qed.

(* ========================================================================= *)
(*                    SUMMARY                                               *)
(* ========================================================================= *)

(**
   COMPLETE FALLACY TAXONOMY
   =========================
   
   TYPE 1: Violations of Conditions (36)
   - 1.A Defective Questions: 3
   - 1.B Manipulations: 33
     - Force: 8
     - Pity: 3
     - Emotion: 7
     - Benefit: 1
     - Pressure: 1
     - False Authority: 3
     - Disinformation: 5
     - Delegation: 2
     - False Ethos: 1
     - Bad Faith: 2
   
   TYPE 2: Domain Violations (105)
   - D1 Recognition: 26
   - D2 Clarification: 13
   - D3 Framework Selection: 16
   - D4 Comparison: 8
   - D5 Inference: 20
   - D6 Reflection: 22
   
   TYPE 3: Violations of Sequence (3)
   - Rationalization
   - Circular Reasoning
   - Shifting Burden of Proof
   
   TYPE 4: Syndromes (6)
   - Cognitive Dissonance: 3
   - Systemic Distortion: 3
   
   TYPE 5: Context-Dependent Methods (6)
   - Intuitive: 2
   - Traditional: 2
   - Indirect: 2
   
   GRAND TOTAL: 156 (~150 in articles)
   
   KEY THEOREMS:
   - complete_taxonomy_156: Total = 156
   - type2_is_70_percent: Type 2 = 70% of core fallacies
   - D1_D6_most_fallacies: Recognition and Reflection most vulnerable
   - D4_most_constrained: Comparison has fewest error modes
*)
