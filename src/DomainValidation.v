(* ════════════════════════════════════════════════════════════
   DomainValidation.v — Structural checks at every level

   Three levels of validation (matching 3 operator levels):
     L1: Per-domain checks (Worker output valid?)
     L2: Gate checks + ASK + REFLECT FULL
     L3: Pipeline checks (full execution valid?)

   All checks are DECIDABLE — boolean functions that extract.
   30 Qed, 0 Admitted
   ════════════════════════════════════════════════════════════ *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
From ToS Require Import DomainTypes.

(** ═══════════════════════════════════
    SECTION A: CYCLE DETECTION (fuel-based DFS)
    ═══════════════════════════════════ *)

Fixpoint reaches (deps : list ERR_Dependency) (src tgt : nat) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    Nat.eqb src tgt ||
    existsb (fun d => Nat.eqb (dep_from d) src &&
                      reaches deps (dep_to d) tgt fuel') deps
  end.

Definition is_acyclic_bool (deps : list ERR_Dependency) : bool :=
  negb (existsb (fun d =>
    reaches deps (dep_to d) (dep_from d) (length deps)) deps).

(** ═══════════════════════════════════
    SECTION B: ERR WELL-FORMEDNESS (Boolean)
    ═══════════════════════════════════ *)

Definition err_well_formed_bool
  (elems : list ERR_Element) (roles : list ERR_Role)
  (rules : list ERR_Rule) (deps : list ERR_Dependency) : bool :=
  (* WF2: No element shares ID with a rule *)
  negb (existsb (fun e => existsb (fun r =>
    Nat.eqb (elem_id e) (rule_id r)) rules) elems) &&
  (* WF4: Dependencies acyclic *)
  is_acyclic_bool deps.

(** ═══════════════════════════════════
    SECTION C: L1 PER-DOMAIN VALIDATORS
    ═══════════════════════════════════ *)

Definition validate_d1_bool (d1 : D1_Output) : bool :=
  (* Has elements *)
  negb (Nat.eqb (length (d1_elements d1)) 0) &&
  (* Every element has a role (L4 grounding) *)
  forallb (fun e => existsb (fun r =>
    Nat.eqb (role_element_id r) (elem_id e)) (d1_roles d1))
    (d1_elements d1) &&
  (* At least one unknown element *)
  existsb (fun s => match status_tag s with
                    | ST_Unknown => true | _ => false end)
    (d1_status d1) &&
  (* Dependencies acyclic *)
  is_acyclic_bool (d1_dependencies d1) &&
  (* Key challenge identified *)
  negb (Nat.eqb (d1_key_challenge d1) 0) &&
  (* Full E/R/R well-formedness *)
  err_well_formed_bool (d1_elements d1) (d1_roles d1)
    (d1_rules d1) (d1_dependencies d1).

Definition validate_d2_bool (d2 : D2_Output) : bool :=
  validate_d1_bool (d2_base d2) &&
  (* Every element defined *)
  Nat.leb (length (d1_elements (d2_base d2)))
          (length (d2_definitions d2)) &&
  (* Equivocation check passed (L1: meanings stable) *)
  d2_equivocation_check d2 &&
  (* Depth >= 2 for non-trivial questions *)
  Nat.leb 2 (fold_left (fun acc p => Nat.max acc (snd p))
              (d2_depth_levels d2) 0).

Definition validate_d3_bool (d3 : D3_Output) : bool :=
  validate_d2_bool (d3_base d3) &&
  (* Framework explicitly named *)
  negb (Nat.eqb (d3_framework_name d3) 0) &&
  (* Objectivity test passed (L2) *)
  d3_objectivity_test d3 &&
  (* At least one criterion for D4 *)
  negb (Nat.eqb (length (d3_criteria d3)) 0) &&
  (* Alternatives considered *)
  negb (Nat.eqb (length (d3_alternatives_considered d3)) 0) &&
  (* Hierarchy check (L5: general before specific) *)
  d3_hierarchy_checked d3.

Definition validate_d4_bool (d4 : D4_Output) : bool :=
  validate_d3_bool (d4_base d4) &&
  (* Comparisons exist *)
  negb (Nat.eqb (length (d4_comparisons d4)) 0) &&
  (* Computation trace exists *)
  negb (Nat.eqb (length (d4_computation_trace d4)) 0).

Definition validate_d5_bool (d5 : D5_Output) : bool :=
  validate_d4_bool (d5_base d5) &&
  (* Inference chain exists *)
  negb (Nat.eqb (length (d5_inference_chain d5)) 0) &&
  (* L5 direction checked: premises -> conclusion *)
  d5_l5_direction_checked d5 &&
  (* Cross-verification attempted (level >= 1) *)
  Nat.leb 1 (d5_cross_verification d5) &&
  (* All 4 honesty requirements checked *)
  Nat.eqb (length (d5_honesty_requirements d5)) 4.

(** ═══════════════════════════════════
    SECTION D: L2 GATE / ASK / REFLECT VALIDATORS
    ═══════════════════════════════════ *)

Definition validate_gate_bool (g : QuickGate) : bool :=
  match qg_verdict g with
  | GV_Pass => qg_alignment g && qg_coverage g
               && qg_consistency g && qg_confidence_matches g
  | GV_Iterate => negb (Nat.eqb (length (qg_feedback g)) 0)
  | GV_Escalate => true
  end.

Definition validate_ask_bool (ask : D6_ASK_Output) : bool :=
  (* Erfragte specified (answer format MUST be defined) *)
  negb (Nat.eqb (ask_erfragte ask) 0) &&
  (* At least one sub-question *)
  negb (Nat.eqb (length (ask_sub_questions ask)) 0) &&
  (* Composition test performed *)
  ask_composition_test ask &&
  (* All sub-questions serve root *)
  forallb snd (ask_serves_root ask).

Definition validate_reflect_bool (rf : D6_REFLECT_Full) : bool :=
  (* Class I present *)
  negb (Nat.eqb (rf_class_i rf) 0) &&
  (* At least 2 from Class II present *)
  Nat.leb 2 (reflect_class_ii_count rf) &&
  (* ERR chain fully checked *)
  (ecc_elements_consistent (rf_err_chain rf)
   && ecc_dependencies_acyclic (rf_err_chain rf)
   && ecc_status_transitions_justified (rf_err_chain rf)
   && ecc_no_level_violations (rf_err_chain rf)) &&
  (* Return target specified if return needed *)
  (match ra_type (rf_return rf) with
   | RT_None => true
   | _ => negb (Nat.eqb (ra_target_domain (rf_return rf)) 0)
   end) &&
  (* Limitations specific *)
  negb (Nat.eqb (rf_scope_fails_when rf) 0) &&
  (* Confidence adjustment has reason *)
  negb (Nat.eqb (rf_adjustment_reason rf) 0).

(** ═══════════════════════════════════
    SECTION E: L3 PIPELINE VALIDATOR
    ═══════════════════════════════════ *)

Definition validate_pipeline_bool (pe : PipelineExecution) : bool :=
  validate_ask_bool (pe_ask pe) &&
  validate_d1_bool (pe_d1 pe) &&
  validate_gate_bool (pe_gate1 pe) &&
  validate_d2_bool (pe_d2 pe) &&
  validate_gate_bool (pe_gate2 pe) &&
  validate_d3_bool (pe_d3 pe) &&
  validate_gate_bool (pe_gate3 pe) &&
  validate_d4_bool (pe_d4 pe) &&
  validate_gate_bool (pe_gate4 pe) &&
  validate_d5_bool (pe_d5 pe) &&
  validate_gate_bool (pe_gate5 pe) &&
  validate_reflect_bool (pe_reflect pe) &&
  pe_d2_d3_ready pe &&
  pe_d4_d5_ready pe &&
  pe_answer_earned pe.

(** ═══════════════════════════════════
    SECTION F: HELPERS
    ═══════════════════════════════════ *)

(** Local helper: b && false = false *)
Lemma andb_false_right : forall b : bool, b && false = false.
Proof. destruct b; reflexivity. Qed.

(** ═══════════════════════════════════
    SECTION G: L1 SOUNDNESS — PER-DOMAIN
    ═══════════════════════════════════ *)

(** 1. D1 has elements *)
Lemma validate_d1_has_elements : forall d1,
  validate_d1_bool d1 = true ->
  d1_elements d1 <> [].
Proof.
  intros d1 H Hcontra. unfold validate_d1_bool in H.
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 2. D1 has key challenge *)
Lemma validate_d1_has_challenge : forall d1,
  validate_d1_bool d1 = true ->
  d1_key_challenge d1 <> 0.
Proof.
  intros d1 H Hcontra. unfold validate_d1_bool in H.
  (* Extract 5th conjunct of 6 *)
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  (* H : negb (Nat.eqb (d1_key_challenge d1) 0) = true *)
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 3. D1 dependencies are acyclic *)
Lemma validate_d1_acyclic : forall d1,
  validate_d1_bool d1 = true ->
  is_acyclic_bool (d1_dependencies d1) = true.
Proof.
  intros d1 H. unfold validate_d1_bool in H.
  (* Extract 4th conjunct of 6: 2 drops, 1 take *)
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

(** 4. D2 implies D1 valid *)
Lemma validate_d2_implies_d1 : forall d2,
  validate_d2_bool d2 = true ->
  validate_d1_bool (d2_base d2) = true.
Proof.
  intros d2 H. unfold validate_d2_bool in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  exact H.
Qed.

(** 5. D2 equivocation check passed *)
Lemma validate_d2_equivocation : forall d2,
  validate_d2_bool d2 = true ->
  d2_equivocation_check d2 = true.
Proof.
  intros d2 H. unfold validate_d2_bool in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

(** 6. D3 implies D2 valid *)
Lemma validate_d3_implies_d2 : forall d3,
  validate_d3_bool d3 = true ->
  validate_d2_bool (d3_base d3) = true.
Proof.
  intros d3 H. unfold validate_d3_bool in H.
  do 5 (apply andb_true_iff in H; destruct H as [H _]).
  exact H.
Qed.

(** 7. D3 objectivity test *)
Lemma validate_d3_objectivity : forall d3,
  validate_d3_bool d3 = true ->
  d3_objectivity_test d3 = true.
Proof.
  intros d3 H. unfold validate_d3_bool in H.
  (* 3rd conjunct of 6: 3 drops, 1 take *)
  do 3 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

(** 8. D3 has criteria *)
Lemma validate_d3_has_criteria : forall d3,
  validate_d3_bool d3 = true ->
  d3_criteria d3 <> [].
Proof.
  intros d3 H Hcontra. unfold validate_d3_bool in H.
  (* 4th conjunct of 6: 2 drops, 1 take *)
  do 2 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 9. D4 implies D3 valid *)
Lemma validate_d4_implies_d3 : forall d4,
  validate_d4_bool d4 = true ->
  validate_d3_bool (d4_base d4) = true.
Proof.
  intros d4 H. unfold validate_d4_bool in H.
  do 2 (apply andb_true_iff in H; destruct H as [H _]).
  exact H.
Qed.

(** 10. D4 has comparisons *)
Lemma validate_d4_has_comparisons : forall d4,
  validate_d4_bool d4 = true ->
  d4_comparisons d4 <> [].
Proof.
  intros d4 H Hcontra. unfold validate_d4_bool in H.
  (* 2nd conjunct of 3: 1 drop, 1 take *)
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 11. D5 implies D4 valid *)
Lemma validate_d5_implies_d4 : forall d5,
  validate_d5_bool d5 = true ->
  validate_d4_bool (d5_base d5) = true.
Proof.
  intros d5 H. unfold validate_d5_bool in H.
  do 4 (apply andb_true_iff in H; destruct H as [H _]).
  exact H.
Qed.

(** 12. D5 has inference chain *)
Lemma validate_d5_has_chain : forall d5,
  validate_d5_bool d5 = true ->
  d5_inference_chain d5 <> [].
Proof.
  intros d5 H Hcontra. unfold validate_d5_bool in H.
  (* 2nd conjunct of 5: 3 drops, 1 take *)
  do 3 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 13. D5 L5 direction checked *)
Lemma validate_d5_direction : forall d5,
  validate_d5_bool d5 = true ->
  d5_l5_direction_checked d5 = true.
Proof.
  intros d5 H. unfold validate_d5_bool in H.
  (* 3rd conjunct of 5: 2 drops, 1 take *)
  do 2 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

(** ═══════════════════════════════════
    SECTION H: L2 SOUNDNESS — GATE / ASK / REFLECT
    ═══════════════════════════════════ *)

(** 14. Gate Pass requires all 4 checks *)
Lemma gate_pass_all_four : forall g,
  validate_gate_bool g = true ->
  qg_verdict g = GV_Pass ->
  qg_alignment g = true /\ qg_coverage g = true /\
  qg_consistency g = true /\ qg_confidence_matches g = true.
Proof.
  intros g H Hv. unfold validate_gate_bool in H. rewrite Hv in H.
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  auto.
Qed.

(** 15. ASK erfragte specified *)
Lemma ask_erfragte_valid : forall ask,
  validate_ask_bool ask = true ->
  ask_erfragte ask <> 0.
Proof.
  intros ask H Hcontra. unfold validate_ask_bool in H.
  do 3 (apply andb_true_iff in H; destruct H as [H _]).
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 16. ASK has sub-questions *)
Lemma ask_has_sub_questions : forall ask,
  validate_ask_bool ask = true ->
  ask_sub_questions ask <> [].
Proof.
  intros ask H Hcontra. unfold validate_ask_bool in H.
  do 2 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 17. Reflect has Class I *)
Lemma reflect_class_i_valid : forall rf,
  validate_reflect_bool rf = true ->
  rf_class_i rf <> 0.
Proof.
  intros rf H Hcontra. unfold validate_reflect_bool in H.
  do 5 (apply andb_true_iff in H; destruct H as [H _]).
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** 18. Reflect has >= 2 Class II *)
Lemma reflect_class_ii_valid : forall rf,
  validate_reflect_bool rf = true ->
  Nat.leb 2 (reflect_class_ii_count rf) = true.
Proof.
  intros rf H. unfold validate_reflect_bool in H.
  do 4 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

(** 19. Reflect ERR chain fully checked *)
Lemma reflect_err_chain_valid : forall rf,
  validate_reflect_bool rf = true ->
  ecc_elements_consistent (rf_err_chain rf) = true /\
  ecc_dependencies_acyclic (rf_err_chain rf) = true /\
  ecc_status_transitions_justified (rf_err_chain rf) = true /\
  ecc_no_level_violations (rf_err_chain rf) = true.
Proof.
  intros rf H. unfold validate_reflect_bool in H.
  (* 3rd conjunct of 6: 3 drops, 1 take *)
  do 3 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  (* H : ecc_* && ecc_* && ecc_* && ecc_* = true *)
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  auto.
Qed.

(** 20. Reflect limitations specific *)
Lemma reflect_limitations_valid : forall rf,
  validate_reflect_bool rf = true ->
  rf_scope_fails_when rf <> 0.
Proof.
  intros rf H Hcontra. unfold validate_reflect_bool in H.
  (* 5th conjunct of 6: 1 drop, 1 take *)
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** ═══════════════════════════════════
    SECTION I: L3 SOUNDNESS — PIPELINE
    ═══════════════════════════════════ *)

(** 21. Pipeline implies ASK valid *)
Lemma pipeline_implies_ask : forall pe,
  validate_pipeline_bool pe = true ->
  validate_ask_bool (pe_ask pe) = true.
Proof.
  intros pe H. unfold validate_pipeline_bool in H.
  do 14 (apply andb_true_iff in H; destruct H as [H _]).
  exact H.
Qed.

(** 22. Pipeline implies all gates valid *)
Lemma pipeline_implies_gates : forall pe,
  validate_pipeline_bool pe = true ->
  validate_gate_bool (pe_gate1 pe) = true /\
  validate_gate_bool (pe_gate2 pe) = true /\
  validate_gate_bool (pe_gate3 pe) = true /\
  validate_gate_bool (pe_gate4 pe) = true /\
  validate_gate_bool (pe_gate5 pe) = true.
Proof.
  intros pe H. unfold validate_pipeline_bool in H.
  (* Gates are at positions 3, 5, 7, 9, 11 of 15 conjuncts *)
  apply andb_true_iff in H. destruct H as [H H15].
  apply andb_true_iff in H. destruct H as [H H14].
  apply andb_true_iff in H. destruct H as [H H13].
  apply andb_true_iff in H. destruct H as [H H12].
  apply andb_true_iff in H. destruct H as [H H11].
  apply andb_true_iff in H. destruct H as [H H10].
  apply andb_true_iff in H. destruct H as [H H9].
  apply andb_true_iff in H. destruct H as [H H8].
  apply andb_true_iff in H. destruct H as [H H7].
  apply andb_true_iff in H. destruct H as [H H6].
  apply andb_true_iff in H. destruct H as [H H5].
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  (* H1=ask, H2=d1, H3=g1, H4=d2, H5=g2, H6=d3, H7=g3, H8=d4, H9=g4, H10=d5, H11=g5, H12=rf, H13=cp1, H14=cp2, H15=cp3 *)
  auto.
Qed.

(** 23. Pipeline implies REFLECT valid *)
Lemma pipeline_implies_reflect : forall pe,
  validate_pipeline_bool pe = true ->
  validate_reflect_bool (pe_reflect pe) = true.
Proof.
  intros pe H. unfold validate_pipeline_bool in H.
  (* 12th conjunct of 15: 3 drops from right, then take rightmost *)
  do 3 (apply andb_true_iff in H; destruct H as [H _]).
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

(** 24. Pipeline implies control points *)
Lemma pipeline_implies_controls : forall pe,
  validate_pipeline_bool pe = true ->
  pe_d2_d3_ready pe = true /\
  pe_d4_d5_ready pe = true /\
  pe_answer_earned pe = true.
Proof.
  intros pe H. unfold validate_pipeline_bool in H.
  (* Last 3 conjuncts *)
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H H2].
  apply andb_true_iff in H. destruct H as [_ H1].
  auto.
Qed.

(** ═══════════════════════════════════
    SECTION J: CUMULATIVE VALIDATION
    ═══════════════════════════════════ *)

(** 25. D5 valid implies all domains valid (cascade) *)
Lemma validation_cumulative : forall d5,
  validate_d5_bool d5 = true ->
  validate_d4_bool (d5_base d5) = true /\
  validate_d3_bool (d4_base (d5_base d5)) = true /\
  validate_d2_bool (d3_base (d4_base (d5_base d5))) = true /\
  validate_d1_bool (d2_base (d3_base (d4_base (d5_base d5)))) = true.
Proof.
  intros d5 H.
  assert (Hd4 := validate_d5_implies_d4 _ H).
  assert (Hd3 := validate_d4_implies_d3 _ Hd4).
  assert (Hd2 := validate_d3_implies_d2 _ Hd3).
  assert (Hd1 := validate_d2_implies_d1 _ Hd2).
  auto.
Qed.

(** ═══════════════════════════════════
    SECTION K: ERROR TAXONOMY
    ═══════════════════════════════════ *)

(** 26. Empty elements (skip D1) caught *)
Lemma catches_empty_elements : forall d1,
  d1_elements d1 = [] ->
  validate_d1_bool d1 = false.
Proof.
  intros d1 H. unfold validate_d1_bool. rewrite H.
  (* First conjunct reduces to false, whole chain = false *)
  reflexivity.
Qed.

(** 27. No key challenge caught *)
Lemma catches_no_challenge : forall d1,
  d1_key_challenge d1 = 0 ->
  validate_d1_bool d1 = false.
Proof.
  intros d1 H. unfold validate_d1_bool. rewrite H.
  change (negb (Nat.eqb 0 0)) with false.
  rewrite andb_false_right. reflexivity.
Qed.

(** 28. Equivocation unchecked caught *)
Lemma catches_no_equivocation : forall d2,
  d2_equivocation_check d2 = false ->
  validate_d2_bool d2 = false.
Proof.
  intros d2 H. unfold validate_d2_bool. rewrite H.
  rewrite andb_false_right. reflexivity.
Qed.

(** 29. Objectivity unchecked caught *)
Lemma catches_no_objectivity : forall d3,
  d3_objectivity_test d3 = false ->
  validate_d3_bool d3 = false.
Proof.
  intros d3 H. unfold validate_d3_bool. rewrite H.
  rewrite andb_false_right. reflexivity.
Qed.

(** 30. No inference chain caught *)
Lemma catches_no_chain : forall d5,
  d5_inference_chain d5 = [] ->
  validate_d5_bool d5 = false.
Proof.
  intros d5 H. unfold validate_d5_bool. rewrite H.
  assert (Hf : negb (Nat.eqb (length (@nil nat)) 0) = false) by reflexivity.
  rewrite Hf. rewrite andb_false_right. reflexivity.
Qed.

(** 31. No erfragte caught *)
Lemma catches_no_erfragte : forall ask,
  ask_erfragte ask = 0 ->
  validate_ask_bool ask = false.
Proof.
  intros ask H. unfold validate_ask_bool. rewrite H.
  reflexivity.
Qed.
