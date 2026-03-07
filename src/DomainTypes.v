(* ════════════════════════════════════════════════════════════
   DomainTypes.v — Formal types for the Regulus D1-D6 pipeline

   Architecture (3 operator levels):
     L3 Team Lead — plans, verifies, assembles (never computes)
     L2 D6        — ASK + REFLECT (never solves)
     L1 Worker    — D1-D5 (solves, one domain per turn)

   D6 is NOT a domain in the chain. D6 is the meta-operator.
   D6-ASK fires BEFORE D1.
   D6-REFLECT QUICK fires AFTER each domain.
   D6-REFLECT FULL fires AFTER D5 or on escalation.

   27 Qed/Defined, 0 Admitted
   ════════════════════════════════════════════════════════════ *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.

(** ═══════════════════════════════════
    SECTION A: E/R/R PRIMITIVES
    Elements / Roles / Rules — the structural backbone
    ═══════════════════════════════════ *)

(** Element levels (D1 hierarchy: data -> info -> quality -> character) *)
Inductive ElemLevel := EL_Data | EL_Info | EL_Quality | EL_Character.

Record ERR_Element := mkERR_Element {
  elem_id : nat;
  elem_content : nat;
  elem_level : ElemLevel;
}.

Inductive RoleTag :=
  RT_Given | RT_Unknown | RT_ConstraintExplicit | RT_ConstraintImplicit
  | RT_Context | RT_Option | RT_Definition.

Record ERR_Role := mkERR_Role {
  role_element_id : nat;
  role_tag : RoleTag;
  role_function : nat;          (* L4: WHY this element is here *)
}.

Inductive RuleSource := RS_Stated | RS_Implied | RS_DomainKnowledge.

Record ERR_Rule := mkERR_Rule {
  rule_id : nat;
  rule_connects : list nat;     (* element IDs *)
  rule_source : RuleSource;
}.

Record ERR_Dependency := mkERR_Dependency {
  dep_from : nat;
  dep_to : nat;
  dep_via_rule : nat;
}.

Inductive StatusTag :=
  ST_Known | ST_Unknown | ST_Constrained | ST_Free | ST_Dependent.

Record ERR_Status := mkERR_Status {
  status_elem_id : nat;
  status_tag : StatusTag;
}.

(** ═══════════════════════════════════
    SECTION B: D6-ASK (PRE-PIPELINE)
    Heidegger's Three Moments + Decomposition
    ═══════════════════════════════════ *)

Record D6_ASK_Output := mkD6_ASK_Output {
  (* Heidegger's Three Moments *)
  ask_gefragte : nat;           (* subject matter — WHAT is being asked about *)
  ask_befragte : nat;           (* source — WHERE to look for the answer *)
  ask_erfragte : nat;           (* sought-for — WHAT counts as answer + FORMAT *)

  (* Question decomposition *)
  ask_sub_questions : list nat;
  ask_serves_root : list (nat * bool);  (* sub_q_id, serves_root? *)
  ask_composition_test : bool;  (* if ALL sub-qs answered -> root answered? *)

  (* Attention directives *)
  ask_traps : list nat;         (* confusion risks *)
  ask_format_required : nat;    (* exact answer format *)

  (* Complexity assessment *)
  ask_complexity : nat;         (* 0=easy, 1=medium, 2=hard *)
  ask_task_type : nat;          (* computation|proof|classification|... *)
}.

(** ═══════════════════════════════════
    SECTION C: D1-D5 WORKER OUTPUTS
    Each domain nests the previous via _base field
    ═══════════════════════════════════ *)

(** D1: Recognition — E/R/R structure *)
Record D1_Output := mkD1_Output {
  d1_elements : list ERR_Element;
  d1_roles : list ERR_Role;
  d1_rules : list ERR_Rule;
  d1_status : list ERR_Status;
  d1_dependencies : list ERR_Dependency;
  d1_key_challenge : nat;
  d1_depth_level : nat;         (* 0-3: data/info/quality/character *)
}.

(** D2: Clarification — definitions + hidden assumptions *)
Record D2_Output := mkD2_Output {
  d2_base : D1_Output;
  d2_definitions : list (nat * nat);    (* elem_id -> definition *)
  d2_depth_levels : list (nat * nat);   (* elem_id -> depth: 0-3 *)
  d2_hidden_assumptions : list nat;
  d2_equivocation_check : bool;        (* L1: no meaning drift *)
  d2_flags_resolved : list (nat * nat); (* flag_id -> resolution *)
}.

(** D3: Framework Selection — coordinate system for comparison *)
Record D3_Output := mkD3_Output {
  d3_base : D2_Output;
  d3_framework_id : nat;
  d3_framework_name : nat;
  d3_alternatives_considered : list nat;
  d3_objectivity_test : bool;   (* L2: "Am I ready to accept ANY answer?" *)
  d3_criteria : list nat;       (* what D4 will compare by *)
  d3_hierarchy_checked : bool;  (* L5: general before specific *)
}.

(** D4: Comparison — framework applied to material *)
Record D4_Output := mkD4_Output {
  d4_base : D3_Output;
  d4_comparisons : list (nat * nat * nat);  (* elem1, elem2, criterion *)
  d4_computation_trace : list nat;
  d4_disconfirming_evidence : list nat;     (* what argues AGAINST the trend *)
  d4_empirical_audit : list (nat * bool);   (* claim_id, verified? *)
  d4_verified_steps : list nat;
}.

(** D5: Inference — conclusion extracted *)
Inductive CertaintyDegree := CD_Necessary | CD_Probabilistic | CD_Evaluative.

Record D5_Output := mkD5_Output {
  d5_base : D4_Output;
  d5_conclusion : nat;
  d5_certainty : CertaintyDegree;
  d5_inference_chain : list nat;    (* premise IDs -> conclusion *)
  d5_l5_direction_checked : bool;   (* premises->conclusion, NOT reverse *)
  d5_cross_verification : nat;      (* 0=none, 1=sanity, 2=alt, 3=sim *)
  d5_honesty_requirements : list bool; (* [correspond, mark, withhold, accept] *)
}.

(** ═══════════════════════════════════
    SECTION D: D6-REFLECT QUICK (INTER-DOMAIN GATE)
    Fires AFTER every D1-D5 output — 4 checks + verdict
    ═══════════════════════════════════ *)

Inductive GateVerdict :=
  | GV_Pass           (* proceed to next domain *)
  | GV_Iterate        (* retry THIS domain with feedback *)
  | GV_Escalate       (* trigger FULL reflection immediately *)
  .

Record QuickGate := mkQuickGate {
  qg_domain : nat;              (* which domain was just completed: 1-5 *)
  qg_alignment : bool;          (* does output address its question? *)
  qg_coverage : bool;           (* all sub-questions answered? *)
  qg_consistency : bool;        (* no contradictions with previous? *)
  qg_confidence_matches : bool; (* self-reported conf matches evidence? *)
  qg_verdict : GateVerdict;
  qg_feedback : list nat;       (* if Iterate: specific issues to fix *)
}.

(** ═══════════════════════════════════
    SECTION E: D6-REFLECT FULL (POST-PIPELINE)
    3 classes + diagnostics + return decision
    ═══════════════════════════════════ *)

(** ERR Chain check across ALL domains *)
Record ERR_ChainCheck := mkERR_ChainCheck {
  ecc_elements_consistent : bool;         (* no elements appearing/disappearing *)
  ecc_dependencies_acyclic : bool;        (* no circular reasoning *)
  ecc_status_transitions_justified : bool; (* each change has reason *)
  ecc_no_level_violations : bool;         (* Rules not governing Rules, etc. *)
}.

(** Per-domain quality assessment *)
Record DomainQuality := mkDomainQuality {
  dq_domain : nat;              (* 1-5 *)
  dq_quality : nat;             (* 0-100 *)
  dq_issues : list nat;
}.

(** Return assessment *)
Inductive ReturnType := RT_None | RT_Corrective | RT_Deepening | RT_Expanding.

Record ReturnAssessment := mkReturnAssessment {
  ra_type : ReturnType;
  ra_target_domain : nat;       (* 0=none, 1-5=which domain *)
  ra_reason : nat;
}.

(** Proof Boundary Audit — when D5 claims Necessary or conf >= 85% *)
Record BoundaryAudit := mkBoundaryAudit {
  ba_claims : list (nat * nat);     (* step_id, property_claimed *)
  ba_boundaries : list (nat * nat); (* step_id, "when is this NOT true?" *)
  ba_gaps : list nat;               (* steps where boundary not excluded *)
  ba_passed : bool;                 (* 0 gaps = passed *)
}.

Record D6_REFLECT_Full := mkD6_REFLECT_Full {
  (* Class I: Object — what was found *)
  rf_class_i : nat;

  (* Class II: Process — 4 reflective checks *)
  rf_perceptive : nat;          (* what D1 might have missed *)
  rf_procedural : nat;          (* weakest domain *)
  rf_perspectival : nat;        (* how different D3 changes answer *)
  rf_fundamental : nat;         (* what accepted without proof *)

  (* Class III: Self — meta-level *)
  rf_default_pattern : option nat;  (* das Man check: training bias? *)

  (* Integration *)
  rf_lesson : nat;
  rf_did_reflection_change : bool;

  (* ERR Chain Verification — across ALL domains *)
  rf_err_chain : ERR_ChainCheck;

  (* Per-domain quality *)
  rf_domain_qualities : list DomainQuality;

  (* Return assessment *)
  rf_return : ReturnAssessment;

  (* Proof Boundary Audit — conditional *)
  rf_boundary_audit : option BoundaryAudit;

  (* Confidence *)
  rf_d5_confidence : nat;       (* what D5 claimed *)
  rf_adjusted_confidence : nat; (* what D6 adjusts to *)
  rf_adjustment_reason : nat;

  (* Specific limitations — NOT generic *)
  rf_scope_applies_when : nat;
  rf_scope_fails_when : nat;
  rf_assumptions : list (nat * nat);  (* assumption, impact_if_wrong *)
  rf_new_questions : list nat;

  (* D5 certainty degree — for boundary audit check *)
  rf_d5_certainty_degree : option CertaintyDegree;
}.

(** ═══════════════════════════════════
    SECTION F: TEAM LEAD / CONSPECTUS
    ═══════════════════════════════════ *)

Record ConspectusEntry := mkConspectusEntry {
  ce_domain : nat;
  ce_key_finding : nat;
  ce_status : nat;              (* 0=passed, 1=flagged, 2=returned *)
}.

Record TeamLeadState := mkTeamLeadState {
  tl_conspectus : list ConspectusEntry;
  tl_current_domain : nat;
  tl_iterations : nat;
  tl_paradigm_shifts : nat;
  tl_paradigm_history : list nat;
}.

(** ═══════════════════════════════════
    SECTION G: FULL PIPELINE EXECUTION RECORD
    ASK -> [D1->gate->...->D5->gate] -> REFLECT FULL
    ═══════════════════════════════════ *)

Record PipelineExecution := mkPipelineExecution {
  (* Pre-pipeline *)
  pe_ask : D6_ASK_Output;

  (* D1 + gate *)
  pe_d1 : D1_Output;
  pe_gate1 : QuickGate;

  (* D2 + gate *)
  pe_d2 : D2_Output;
  pe_gate2 : QuickGate;
  pe_d2_d3_ready : bool;       (* control point *)

  (* D3 + gate *)
  pe_d3 : D3_Output;
  pe_gate3 : QuickGate;

  (* D4 + gate *)
  pe_d4 : D4_Output;
  pe_gate4 : QuickGate;
  pe_d4_d5_ready : bool;       (* control point *)

  (* D5 + gate *)
  pe_d5 : D5_Output;
  pe_gate5 : QuickGate;
  pe_answer_earned : bool;     (* control point: is answer EARNED? *)

  (* Post-pipeline: FULL reflection *)
  pe_reflect : D6_REFLECT_Full;

  (* Team Lead state *)
  pe_tl : TeamLeadState;

  (* Final *)
  pe_final_answer : nat;
  pe_final_confidence : nat;
}.

(** ═══════════════════════════════════
    SECTION H: DECIDABLE EQUALITY
    All Defined for extraction transparency
    ═══════════════════════════════════ *)

Lemma elemlevel_eq_dec : forall (a b : ElemLevel), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma roletag_eq_dec : forall (a b : RoleTag), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma rulesource_eq_dec : forall (a b : RuleSource), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma statustag_eq_dec : forall (a b : StatusTag), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma certaintydegree_eq_dec : forall (a b : CertaintyDegree), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma gateverdict_eq_dec : forall (a b : GateVerdict), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma returntype_eq_dec : forall (a b : ReturnType), {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** ═══════════════════════════════════
    SECTION I: HELPER FUNCTIONS
    ═══════════════════════════════════ *)

Definition count_nonzero (l : list nat) : nat :=
  length (filter (fun x => negb (Nat.eqb x 0)) l).

Definition reflect_class_ii_count (rf : D6_REFLECT_Full) : nat :=
  count_nonzero [rf_perceptive rf; rf_procedural rf;
                 rf_perspectival rf; rf_fundamental rf].

(** Domain chain extractors: D5 nests D4 nests D3 nests D2 nests D1 *)
Definition extract_d1 (d5 : D5_Output) : D1_Output :=
  d2_base (d3_base (d4_base (d5_base d5))).

Definition extract_d2 (d5 : D5_Output) : D2_Output :=
  d3_base (d4_base (d5_base d5)).

Definition extract_d3 (d5 : D5_Output) : D3_Output :=
  d4_base (d5_base d5).

Definition extract_d4 (d5 : D5_Output) : D4_Output :=
  d5_base d5.

(** Gate accessor by position *)
Definition gate_at_position (pe : PipelineExecution) (n : nat) : option QuickGate :=
  match n with
  | 1 => Some (pe_gate1 pe)
  | 2 => Some (pe_gate2 pe)
  | 3 => Some (pe_gate3 pe)
  | 4 => Some (pe_gate4 pe)
  | 5 => Some (pe_gate5 pe)
  | _ => None
  end.

(** ═══════════════════════════════════
    SECTION J: WELL-FORMEDNESS PREDICATES
    ═══════════════════════════════════ *)

Definition ask_erfragte_specified (ask : D6_ASK_Output) : Prop :=
  ask_erfragte ask <> 0.

Definition ask_composition_valid (ask : D6_ASK_Output) : Prop :=
  ask_composition_test ask = true ->
  forall p, In p (ask_serves_root ask) -> snd p = true.

Definition gate_well_formed (g : QuickGate) : Prop :=
  match qg_verdict g with
  | GV_Pass => qg_alignment g = true /\ qg_coverage g = true /\
               qg_consistency g = true /\ qg_confidence_matches g = true
  | GV_Iterate => qg_feedback g <> []
  | GV_Escalate => True
  end.

Definition reflect_well_formed (rf : D6_REFLECT_Full) : Prop :=
  rf_class_i rf <> 0 /\
  reflect_class_ii_count rf >= 2 /\
  rf_scope_fails_when rf <> 0 /\
  rf_adjustment_reason rf <> 0 /\
  (match ra_type (rf_return rf) with
   | RT_None => True
   | _ => ra_target_domain (rf_return rf) <> 0
   end).

(** Pipeline consistency: each domain's base links to previous *)
Definition pipeline_consistent (pe : PipelineExecution) : Prop :=
  d2_base (pe_d2 pe) = pe_d1 pe /\
  d3_base (pe_d3 pe) = pe_d2 pe /\
  d4_base (pe_d4 pe) = pe_d3 pe /\
  d5_base (pe_d5 pe) = pe_d4 pe.

(** Full well-formedness: ASK + gates + reflect + controls *)
Definition pipeline_well_formed (pe : PipelineExecution) : Prop :=
  ask_erfragte_specified (pe_ask pe) /\
  gate_well_formed (pe_gate1 pe) /\
  gate_well_formed (pe_gate2 pe) /\
  gate_well_formed (pe_gate3 pe) /\
  gate_well_formed (pe_gate4 pe) /\
  gate_well_formed (pe_gate5 pe) /\
  reflect_well_formed (pe_reflect pe) /\
  pe_d2_d3_ready pe = true /\
  pe_d4_d5_ready pe = true /\
  pe_answer_earned pe = true.

(** ═══════════════════════════════════
    SECTION K: STRUCTURAL LEMMAS
    27 total: 7 Defined + 20 Qed
    ═══════════════════════════════════ *)

(** Helper: forallb implies pointwise truth *)
Lemma forallb_In : forall {A : Type} (f : A -> bool) (l : list A) (x : A),
  forallb f l = true -> In x l -> f x = true.
Proof.
  intros A f l x. induction l as [| a l' IH]; simpl.
  - intros _ [].
  - intros Hb [Heq | Hin].
    + subst. apply andb_true_iff in Hb. destruct Hb as [H _]. exact H.
    + apply andb_true_iff in Hb. destruct Hb as [_ H]. exact (IH H Hin).
Qed.

(** ─── ASK lemmas ─── *)

Lemma ask_has_erfragte : forall ask,
  ask_erfragte ask <> 0 -> ask_erfragte_specified ask.
Proof.
  unfold ask_erfragte_specified. auto.
Qed.

Lemma ask_composition_sound : forall ask,
  ask_composition_test ask = true ->
  forallb snd (ask_serves_root ask) = true ->
  ask_composition_valid ask.
Proof.
  unfold ask_composition_valid. intros ask _ Hall _ p Hin.
  exact (forallb_In snd (ask_serves_root ask) p Hall Hin).
Qed.

(** ─── Domain chain: consistent pipeline preserves all data ─── *)

Lemma consistent_d5_has_d1 : forall pe,
  pipeline_consistent pe ->
  extract_d1 (pe_d5 pe) = pe_d1 pe.
Proof.
  unfold pipeline_consistent, extract_d1.
  intros pe [H12 [H23 [H34 H45]]].
  rewrite H45, H34, H23, H12. reflexivity.
Qed.

Lemma consistent_d5_has_d2 : forall pe,
  pipeline_consistent pe ->
  extract_d2 (pe_d5 pe) = pe_d2 pe.
Proof.
  unfold pipeline_consistent, extract_d2.
  intros pe [_ [H23 [H34 H45]]].
  rewrite H45, H34, H23. reflexivity.
Qed.

Lemma consistent_d5_has_d3 : forall pe,
  pipeline_consistent pe ->
  extract_d3 (pe_d5 pe) = pe_d3 pe.
Proof.
  unfold pipeline_consistent, extract_d3.
  intros pe [_ [_ [H34 H45]]].
  rewrite H45, H34. reflexivity.
Qed.

Lemma consistent_d5_has_d4 : forall pe,
  pipeline_consistent pe ->
  extract_d4 (pe_d5 pe) = pe_d4 pe.
Proof.
  unfold pipeline_consistent, extract_d4.
  intros pe [_ [_ [_ H45]]].
  rewrite H45. reflexivity.
Qed.

(** ─── Gate lemmas ─── *)

Lemma gate_pass_requires_all : forall g,
  gate_well_formed g ->
  qg_verdict g = GV_Pass ->
  qg_alignment g = true /\ qg_coverage g = true /\
  qg_consistency g = true /\ qg_confidence_matches g = true.
Proof.
  unfold gate_well_formed. intros g Hwf Hpass.
  rewrite Hpass in Hwf. exact Hwf.
Qed.

Lemma gate_iterate_has_feedback : forall g,
  gate_well_formed g ->
  qg_verdict g = GV_Iterate ->
  qg_feedback g <> [].
Proof.
  unfold gate_well_formed. intros g Hwf Hiter.
  rewrite Hiter in Hwf. exact Hwf.
Qed.

(** ─── Reflect lemmas ─── *)

Lemma reflect_has_class_i : forall rf,
  reflect_well_formed rf ->
  rf_class_i rf <> 0.
Proof.
  unfold reflect_well_formed. intros rf [H _]. exact H.
Qed.

Lemma reflect_has_class_ii : forall rf,
  reflect_well_formed rf ->
  reflect_class_ii_count rf >= 2.
Proof.
  unfold reflect_well_formed. intros rf [_ [H _]]. exact H.
Qed.

Lemma reflect_return_valid : forall rf,
  reflect_well_formed rf ->
  match ra_type (rf_return rf) with
  | RT_None => True
  | _ => ra_target_domain (rf_return rf) <> 0
  end.
Proof.
  unfold reflect_well_formed. intros rf [_ [_ [_ [_ H]]]]. exact H.
Qed.

Lemma reflect_limitations_specific : forall rf,
  reflect_well_formed rf ->
  rf_scope_fails_when rf <> 0.
Proof.
  unfold reflect_well_formed. intros rf [_ [_ [H _]]]. exact H.
Qed.

Lemma reflect_confidence_has_reason : forall rf,
  reflect_well_formed rf ->
  rf_adjustment_reason rf <> 0.
Proof.
  unfold reflect_well_formed. intros rf [_ [_ [_ [H _]]]]. exact H.
Qed.

Lemma reflect_expanding_is_paradigm_shift : forall rf,
  ra_type (rf_return rf) = RT_Expanding ->
  ra_type (rf_return rf) <> RT_None.
Proof.
  intros rf H. rewrite H. discriminate.
Qed.

(** ─── Pipeline lemmas ─── *)

Lemma pipeline_has_ask : forall pe,
  pipeline_well_formed pe ->
  ask_erfragte_specified (pe_ask pe).
Proof.
  unfold pipeline_well_formed. intros pe [H _]. exact H.
Qed.

Lemma pipeline_has_all_gates : forall pe,
  pipeline_well_formed pe ->
  gate_well_formed (pe_gate1 pe) /\
  gate_well_formed (pe_gate2 pe) /\
  gate_well_formed (pe_gate3 pe) /\
  gate_well_formed (pe_gate4 pe) /\
  gate_well_formed (pe_gate5 pe).
Proof.
  unfold pipeline_well_formed.
  intros pe [_ [H1 [H2 [H3 [H4 [H5 _]]]]]].
  auto.
Qed.

Lemma pipeline_has_reflect : forall pe,
  pipeline_well_formed pe ->
  reflect_well_formed (pe_reflect pe).
Proof.
  unfold pipeline_well_formed.
  intros pe [_ [_ [_ [_ [_ [_ [H _]]]]]]].
  exact H.
Qed.

Lemma pipeline_control_points : forall pe,
  pipeline_well_formed pe ->
  pe_d2_d3_ready pe = true /\
  pe_d4_d5_ready pe = true /\
  pe_answer_earned pe = true.
Proof.
  unfold pipeline_well_formed.
  intros pe [_ [_ [_ [_ [_ [_ [_ [H1 [H2 H3]]]]]]]]].
  auto.
Qed.

(** Master theorem: well-formed + consistent pipeline has everything *)
Lemma pipeline_complete : forall pe,
  pipeline_well_formed pe ->
  pipeline_consistent pe ->
  ask_erfragte_specified (pe_ask pe) /\
  extract_d1 (pe_d5 pe) = pe_d1 pe /\
  reflect_well_formed (pe_reflect pe) /\
  pe_answer_earned pe = true.
Proof.
  intros pe Hwf Hcon.
  split. { apply pipeline_has_ask. exact Hwf. }
  split. { apply consistent_d5_has_d1. exact Hcon. }
  split. { apply pipeline_has_reflect. exact Hwf. }
  apply pipeline_control_points in Hwf.
  destruct Hwf as [_ [_ H]]. exact H.
Qed.
