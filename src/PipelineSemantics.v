(* ════════════════════════════════════════════════════════════
   PipelineSemantics.v — Pipeline iteration as P4-process

   Key ideas:
     1. A PipelineIteration maps ASK → full execution record
     2. Iterations are step-indexed (GenProcess PipelineExecution)
     3. Convergence: confidence delta shrinks to within epsilon
     4. Paradigm shift: D6-REFLECT FULL → new ASK with D3 constraint
     5. Gates catch errors mid-pipeline (early termination)

   17 Qed, 0 Admitted
   ════════════════════════════════════════════════════════════ *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
From ToS Require Import DomainTypes.
From ToS Require Import DomainValidation.

(** ═══════════════════════════════════
    SECTION A: PIPELINE ITERATION
    ═══════════════════════════════════ *)

(** A pipeline iteration: given ASK output, produce a full execution *)
Definition PipelineIteration := D6_ASK_Output -> PipelineExecution.

(** Step-indexed iteration: nat -> PipelineExecution *)
Definition PipelineProcess := nat -> PipelineExecution.

(** Build a pipeline process by repeating iteration from fixed ASK *)
Definition pipeline_process (T : PipelineIteration) (ask : D6_ASK_Output)
  : PipelineProcess :=
  fun n => T ask.  (* each step independently applies T to ask *)

(** ═══════════════════════════════════
    SECTION B: DISTANCE / CONVERGENCE
    ═══════════════════════════════════ *)

(** Nat-based distance: |confidence1 - confidence2| *)
Definition pe_distance (pe1 pe2 : PipelineExecution) : nat :=
  let c1 := pe_final_confidence pe1 in
  let c2 := pe_final_confidence pe2 in
  if Nat.leb c1 c2 then c2 - c1 else c1 - c2.

(** Convergence: delta <= epsilon *)
Definition has_converged (pe1 pe2 : PipelineExecution) (epsilon : nat) : bool :=
  Nat.leb (pe_distance pe1 pe2) epsilon.

(** ═══════════════════════════════════
    SECTION C: PARADIGM SHIFT
    ═══════════════════════════════════ *)

(** Paradigm shift needed: REFLECT says RT_Expanding, or stall detected *)
Definition needs_paradigm_shift (rf : D6_REFLECT_Full) (tl : TeamLeadState) : bool :=
  match ra_type (rf_return rf) with
  | RT_Expanding => true
  | _ => false
  end
  || Nat.leb 2 (tl_iterations tl).

(** Shift ASK: record paradigm count in complexity field *)
Definition shift_ask (ask : D6_ASK_Output) (tl : TeamLeadState) : D6_ASK_Output :=
  mkD6_ASK_Output
    (ask_gefragte ask)
    (ask_befragte ask)
    (ask_erfragte ask)
    (ask_sub_questions ask)
    (ask_serves_root ask)
    (ask_composition_test ask)
    (ask_traps ask)
    (ask_format_required ask)
    (S (ask_complexity ask))           (* bump complexity = paradigm shift marker *)
    (ask_task_type ask).

(** ═══════════════════════════════════
    SECTION D: GATE CHECKING HELPERS
    ═══════════════════════════════════ *)

(** Gate passed? *)
Definition gate_passed (g : QuickGate) : bool :=
  match qg_verdict g with
  | GV_Pass => true
  | _ => false
  end.

(** All 5 gates passed in a pipeline execution *)
Definition all_gates_passed (pe : PipelineExecution) : bool :=
  gate_passed (pe_gate1 pe) &&
  gate_passed (pe_gate2 pe) &&
  gate_passed (pe_gate3 pe) &&
  gate_passed (pe_gate4 pe) &&
  gate_passed (pe_gate5 pe).

(** First failing gate position (0 = no failure, 1-5 = gate number) *)
Fixpoint first_failing_gate_helper (gates : list QuickGate) (pos : nat) : nat :=
  match gates with
  | [] => 0
  | g :: rest =>
    if gate_passed g then first_failing_gate_helper rest (S pos)
    else pos
  end.

Definition first_failing_gate (pe : PipelineExecution) : nat :=
  first_failing_gate_helper
    [pe_gate1 pe; pe_gate2 pe; pe_gate3 pe; pe_gate4 pe; pe_gate5 pe] 1.

(** ═══════════════════════════════════
    SECTION E: STEP-INDEXED EXECUTION
    ═══════════════════════════════════ *)

(** Run pipeline with fuel, paradigm shifts, and convergence detection.
    Returns (final execution, iterations used). *)
Fixpoint run_pipeline
  (T : PipelineIteration) (ask : D6_ASK_Output)
  (fuel : nat) (epsilon : nat) (max_shifts : nat)
  (prev : PipelineExecution)
  : PipelineExecution * nat :=
  match fuel with
  | O => (prev, 0)
  | S fuel' =>
    let pe := T ask in
    if has_converged pe prev epsilon then (pe, 1)
    else
      if needs_paradigm_shift (pe_reflect pe) (pe_tl pe)
           && Nat.ltb 0 max_shifts
      then
        let ask' := shift_ask ask (pe_tl pe) in
        let '(pe', n) := run_pipeline T ask' fuel' epsilon (max_shifts - 1) pe in
        (pe', S n)
      else
        let '(pe', n) := run_pipeline T ask fuel' epsilon max_shifts pe in
        (pe', S n)
  end.

(** ═══════════════════════════════════
    SECTION F: LEMMAS — TERMINATION (1-4)
    ═══════════════════════════════════ *)

(** 1. run_pipeline uses at most fuel iterations *)
Lemma run_pipeline_bounded : forall T ask fuel eps ms prev pe n,
  run_pipeline T ask fuel eps ms prev = (pe, n) ->
  n <= fuel.
Proof.
  intros T ask fuel. revert T ask.
  induction fuel as [|fuel' IH]; intros T ask eps ms prev pe n Heq.
  - simpl in Heq. inversion Heq. lia.
  - simpl in Heq.
    destruct (has_converged (T ask) prev eps).
    + inversion Heq. lia.
    + destruct (needs_paradigm_shift (pe_reflect (T ask)) (pe_tl (T ask))
                  && Nat.ltb 0 ms).
      * destruct (run_pipeline T (shift_ask ask (pe_tl (T ask))) fuel' eps
                    (ms - 1) (T ask)) as [pe_r n_r] eqn:Hrec.
        assert (Hle: n_r <= fuel') by (eapply IH; exact Hrec).
        inversion Heq. lia.
      * destruct (run_pipeline T ask fuel' eps ms (T ask)) as [pe_r n_r] eqn:Hrec.
        assert (Hle: n_r <= fuel') by (eapply IH; exact Hrec).
        inversion Heq. lia.
Qed.

(** 2. Fuel 0 returns the previous execution *)
Lemma run_pipeline_zero_fuel : forall T ask eps ms prev,
  run_pipeline T ask 0 eps ms prev = (prev, 0).
Proof. reflexivity. Qed.

(** 3. If converged, returns after 1 iteration *)
Lemma run_pipeline_converged : forall T ask fuel eps ms prev,
  has_converged (T ask) prev eps = true ->
  fuel > 0 ->
  run_pipeline T ask fuel eps ms prev = (T ask, 1).
Proof.
  intros T ask fuel eps ms prev Hconv Hfuel.
  destruct fuel as [|fuel'].
  - lia.
  - simpl. rewrite Hconv. reflexivity.
Qed.

(** 4. Positive fuel produces at least 1 iteration *)
Lemma run_pipeline_positive : forall T ask fuel eps ms prev pe n,
  fuel > 0 ->
  run_pipeline T ask fuel eps ms prev = (pe, n) ->
  n >= 1.
Proof.
  intros T ask fuel eps ms prev pe n Hfuel Heq.
  destruct fuel as [|fuel'].
  - lia.
  - simpl in Heq.
    destruct (has_converged (T ask) prev eps).
    + inversion Heq. lia.
    + destruct (needs_paradigm_shift (pe_reflect (T ask)) (pe_tl (T ask))
                  && Nat.ltb 0 ms).
      * destruct (run_pipeline T (shift_ask ask (pe_tl (T ask))) fuel' eps
                    (ms - 1) (T ask)) as [pe_r n_r].
        inversion Heq. lia.
      * destruct (run_pipeline T ask fuel' eps ms (T ask)) as [pe_r n_r].
        inversion Heq. lia.
Qed.

(** ═══════════════════════════════════
    SECTION G: LEMMAS — CONVERGENCE (5-8)
    ═══════════════════════════════════ *)

(** 5. pe_distance is symmetric *)
Lemma pe_distance_sym : forall pe1 pe2,
  pe_distance pe1 pe2 = pe_distance pe2 pe1.
Proof.
  intros pe1 pe2. unfold pe_distance.
  destruct (Nat.leb (pe_final_confidence pe1) (pe_final_confidence pe2)) eqn:E1;
  destruct (Nat.leb (pe_final_confidence pe2) (pe_final_confidence pe1)) eqn:E2.
  - apply Nat.leb_le in E1. apply Nat.leb_le in E2. lia.
  - reflexivity.
  - reflexivity.
  - apply Nat.leb_nle in E1. apply Nat.leb_nle in E2. lia.
Qed.

(** 6. pe_distance from self is 0 *)
Lemma pe_distance_self : forall pe,
  pe_distance pe pe = 0.
Proof.
  intros pe. unfold pe_distance.
  assert (Nat.leb (pe_final_confidence pe) (pe_final_confidence pe) = true)
    by (apply Nat.leb_le; lia).
  rewrite H. lia.
Qed.

(** 7. has_converged with epsilon >= max_confidence always true for self *)
Lemma converged_self : forall pe eps,
  has_converged pe pe eps = true.
Proof.
  intros pe eps. unfold has_converged.
  rewrite pe_distance_self. simpl. reflexivity.
Qed.

(** 8. Convergence monotone: larger epsilon is easier to satisfy *)
Lemma convergence_monotone : forall pe1 pe2 eps1 eps2,
  has_converged pe1 pe2 eps1 = true ->
  eps2 >= eps1 ->
  has_converged pe1 pe2 eps2 = true.
Proof.
  intros pe1 pe2 eps1 eps2 Hconv Hge.
  unfold has_converged in *. apply Nat.leb_le in Hconv.
  apply Nat.leb_le. lia.
Qed.

(** ═══════════════════════════════════
    SECTION H: LEMMAS — PARADIGM SHIFT (9-12)
    ═══════════════════════════════════ *)

(** 9. RT_Expanding always triggers paradigm shift *)
Lemma expanding_triggers_shift : forall rf tl,
  ra_type (rf_return rf) = RT_Expanding ->
  needs_paradigm_shift rf tl = true.
Proof.
  intros rf tl Hrt. unfold needs_paradigm_shift. rewrite Hrt.
  reflexivity.
Qed.

(** 10. Paradigm shift preserves erfragte (answer format unchanged) *)
Lemma shift_preserves_erfragte : forall ask tl,
  ask_erfragte (shift_ask ask tl) = ask_erfragte ask.
Proof. reflexivity. Qed.

(** 11. Paradigm shift bumps complexity *)
Lemma shift_bumps_complexity : forall ask tl,
  ask_complexity (shift_ask ask tl) = S (ask_complexity ask).
Proof. reflexivity. Qed.

(** 12. Paradigm shift preserves sub-questions *)
Lemma shift_preserves_sub_questions : forall ask tl,
  ask_sub_questions (shift_ask ask tl) = ask_sub_questions ask.
Proof. reflexivity. Qed.

(** ═══════════════════════════════════
    SECTION I: LEMMAS — GATES (13-15)
    ═══════════════════════════════════ *)

(** 13. All gates passed implies every individual gate passed *)
Lemma all_gates_implies_each : forall pe,
  all_gates_passed pe = true ->
  gate_passed (pe_gate1 pe) = true /\
  gate_passed (pe_gate2 pe) = true /\
  gate_passed (pe_gate3 pe) = true /\
  gate_passed (pe_gate4 pe) = true /\
  gate_passed (pe_gate5 pe) = true.
Proof.
  intros pe H. unfold all_gates_passed in H.
  apply andb_true_iff in H. destruct H as [H H5].
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  auto.
Qed.

(** 14. Gate failure means not all gates passed *)
Lemma gate_failure_breaks_all : forall pe,
  gate_passed (pe_gate1 pe) = false ->
  all_gates_passed pe = false.
Proof.
  intros pe H. unfold all_gates_passed.
  rewrite H. reflexivity.
Qed.

(** 15. If first_failing_gate = 0, all gates passed *)
Lemma no_failing_gate_means_all_pass : forall pe,
  first_failing_gate pe = 0 ->
  gate_passed (pe_gate1 pe) = true /\
  gate_passed (pe_gate2 pe) = true /\
  gate_passed (pe_gate3 pe) = true /\
  gate_passed (pe_gate4 pe) = true /\
  gate_passed (pe_gate5 pe) = true.
Proof.
  intros pe H.
  unfold first_failing_gate in H.
  simpl in H.
  destruct (gate_passed (pe_gate1 pe)) eqn:E1; [|discriminate].
  simpl in H.
  destruct (gate_passed (pe_gate2 pe)) eqn:E2; [|discriminate].
  simpl in H.
  destruct (gate_passed (pe_gate3 pe)) eqn:E3; [|discriminate].
  simpl in H.
  destruct (gate_passed (pe_gate4 pe)) eqn:E4; [|discriminate].
  simpl in H.
  destruct (gate_passed (pe_gate5 pe)) eqn:E5; [|discriminate].
  auto.
Qed.

(** ═══════════════════════════════════
    SECTION J: LEMMAS — COMPOSITION (16-17)
    ═══════════════════════════════════ *)

(** 16. Valid pipeline + all gates pass → answer earned *)
Lemma valid_pipeline_answer_earned : forall pe,
  validate_pipeline_bool pe = true ->
  pe_answer_earned pe = true.
Proof.
  intros pe H.
  assert (Hc := pipeline_implies_controls pe H).
  destruct Hc as [_ [_ Hae]]. exact Hae.
Qed.

(** 17. Shift + validate ASK: shifted ASK preserves validation properties *)
Lemma shift_preserves_ask_validation : forall ask tl,
  validate_ask_bool ask = true ->
  ask_erfragte (shift_ask ask tl) <> 0 /\
  ask_sub_questions (shift_ask ask tl) <> [] /\
  ask_composition_test (shift_ask ask tl) = ask_composition_test ask.
Proof.
  intros ask tl Hv.
  assert (He := ask_erfragte_valid ask Hv).
  assert (Hs := ask_has_sub_questions ask Hv).
  simpl. auto.
Qed.
