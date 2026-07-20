(** * KnowledgeQuestion.v — the QUESTION as a system: ground, direction, goal
      (formalization of MP-6/MP-7/MP-8, renamed and corrected per MP-17/MP-18,
       the mental-field working record, Knigi/Volya/01;
       sibling of KnowledgeInquiry.v / KnowledgeAnswerExists.v)

    Elements: the known ground; the directed place; the goal category;
              the motivation state of the asking act.
    Roles:    ground    = the Elements of the act (whence: what it stands on);
              direction = its Role (whither: which place is taken up);
              goal      = its Rule (what counts as an answer — the form of what
                          closes the act; reaching the goal IS the answer).
    Rules:    constitutive (generative) order goal -> direction -> ground
              (the root question first says WHAT is sought);
              integrity of the three parts = well-formedness;
              the direction stands in the KNOWN field for polar/selective
              goals — only the status / the choice is missing (MP-18) — and
              on the ring for the filling goal; never in the outer zone;
              the path fill -> select -> verify, always closed polarly
              ("cascade" retired per MP-18: the steps are the PATH to the answer);
              the ground of the act is TWO-FACED (V21): the content ground
              lives in the composition, the act ground (motivation ripened
              to L4) fires the act — the faces are independent.
    Status:   the defects of catalog group 1.A are exactly damages of the three
              parts (full classification); the fifth defect — the IMPOSSIBLE
              GOAL (1.A.7, renamed per MP-18) — was PREDICTED by the anatomy;
              closers: polar<->witness, selective<->will, filling<->actualization.
    STATUS: 37 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules (generative first): the goal (rule of answer-recognition) determines
      the direction — an aim is definite only under a given category; the
      direction differentiates the ground — the known becomes ground only
      under an acting aim.  The constitutive order is strict; the TEMPORAL
      order is free (an anomaly in the known may come first) — the same
      distinction as the domain sequence (logical strict / temporal free).
    Roles (L4): ground carries the act; direction takes up a place — in the
      known field (polar: status missing; selective: choice missing — a
      question of DECISION, not of knowledge) or on the ring (filling:
      content missing); goal assigns the status "answer"; motivation ripened
      to sufficiency is the ACT ground (L4), not a fourth part — composition
      and act-ground do not mix (MP-8), and the two faces of the ground are
      independent (V21: grounds_two_faces).
    Elements (L1+P4): finitely many states, every predicate decidable (bool);
      no completed totality anywhere — the "completed svod" goal is exactly
      the defect of the impossible layer ("cannot be", MP-5).
    P4 diagnostic (could it be otherwise?): a fourth PART is not found (an act
      of pointing needs exactly: whence, whither, what-closes); a fourth GOAL
      kind is impossible (givenness full / pool / category-only exhausts); no
      goal kind may target the outer zone (nothing is differentiated there to
      take up); the path cannot end non-polarly — whatever closes must be
      RECOGNIZED as closing, i.e. polarly checked against the goal. *)

From Stdlib Require Import List.
Import ListNotations.

(* ---------- zones of the field (in the spirit of KnowledgeInquiry.v) ---------- *)

Inductive Zone := ZKnown | ZRing | ZOuter.
(* subjective field "I know" | ring "I know that I do not know" |
   objective field beyond the border ("I do not know that I do not know") *)

Definition reachable (z : Zone) : bool :=
  match z with ZOuter => false | _ => true end.

(* one cannot direct a question into the unknown-unknown *)
Theorem outer_not_reachable : reachable ZOuter = false.
Proof. reflexivity. Qed.

Theorem reachable_two :
  forall z, reachable z = true -> z = ZKnown \/ z = ZRing.
Proof.
  intro z; destruct z; intro H;
  [ left; reflexivity | right; reflexivity | discriminate H ].
Qed.

(* ---------- kinds of the goal and their target zones (MP-6/MP-18) ---------- *)

Inductive GoalKind := CPolar | CSelective | CFilling.
(* status missing | one-of-pool missing | content missing *)

(* MP-18: the direction of a polar/selective question stands in the KNOWN
   field (the pair / the pool is known material); only the filling question
   directs onto the ring *)
Definition target_ok (k : GoalKind) (z : Zone) : bool :=
  match k, z with
  | CPolar, ZKnown | CSelective, ZKnown | CFilling, ZRing => true
  | _, _ => false
  end.

Theorem filling_targets_ring :
  forall z, target_ok CFilling z = true <-> z = ZRing.
Proof. intro z; destruct z; split; intro H; first [ reflexivity | discriminate H ]. Qed.

(* "where shall I go on holiday?" works with a known list of candidates *)
Theorem fact_and_choice_in_known :
  target_ok CPolar ZKnown = true /\ target_ok CSelective ZKnown = true.
Proof. split; reflexivity. Qed.

Theorem no_goal_targets_outer : forall k, target_ok k ZOuter = false.
Proof. intro k; destruct k; reflexivity. Qed.

Theorem target_ok_reachable :
  forall k z, target_ok k z = true -> reachable z = true.
Proof. intros k z H; destruct k, z; simpl in *; try discriminate H; reflexivity. Qed.

(* ---------- the three parts and their states ---------- *)

Inductive GroundState := GrReal | GrFalse.
(* ground: real known / false ground — built-in assumption (1.A.6) *)

Inductive DirectionState := DirOne | DirMerged | DirNone.
(* direction: single / merged (1.A.3) / absent (rhetorical shell — not a question) *)

Inductive GoalState := GlWhole | GlTrimTopic | GlTrimContext | GlImpossible.
(* goal: whole / trimmed by topics (1.A.4) / trimmed by context (1.A.5) /
   the impossible goal — outlines the "cannot be" layer (MP-7/MP-18, 1.A.7) *)

Record Question := mkQ {
  q_ground    : GroundState;
  q_direction : DirectionState;
  q_kind      : GoalKind;
  q_target    : Zone;
  q_goal      : GoalState
}.

Definition is_question (q : Question) : bool :=
  match q_direction q with DirNone => false | _ => true end.

Definition well_formed (q : Question) : bool :=
  match q_ground q, q_direction q, q_goal q with
  | GrReal, DirOne, GlWhole => target_ok (q_kind q) (q_target q)
  | _, _, _ => false
  end.

Theorem wf_target_fits_goal :
  forall q, well_formed q = true -> target_ok (q_kind q) (q_target q) = true.
Proof.
  intros [g dir k t gl] H; destruct g, dir, gl; simpl in *;
  try discriminate H; exact H.
Qed.

(* the old canon "the direction targets the ring" survives CONDITIONALLY:
   it is the law of the filling goal alone (MP-18) *)
Theorem wf_filling_on_ring :
  forall q, well_formed q = true -> q_kind q = CFilling -> q_target q = ZRing.
Proof.
  intros [g dir k t gl] H Hk; destruct g, dir, gl; simpl in *;
  try discriminate H; subst k; destruct t; simpl in H;
  try discriminate H; reflexivity.
Qed.

Theorem wf_polar_in_known :
  forall q, well_formed q = true -> q_kind q = CPolar -> q_target q = ZKnown.
Proof.
  intros [g dir k t gl] H Hk; destruct g, dir, gl; simpl in *;
  try discriminate H; subst k; destruct t; simpl in H;
  try discriminate H; reflexivity.
Qed.

Theorem wf_selective_in_known :
  forall q, well_formed q = true -> q_kind q = CSelective -> q_target q = ZKnown.
Proof.
  intros [g dir k t gl] H Hk; destruct g, dir, gl; simpl in *;
  try discriminate H; subst k; destruct t; simpl in H;
  try discriminate H; reflexivity.
Qed.

Theorem wf_never_outer :
  forall q, well_formed q = true -> q_target q <> ZOuter.
Proof.
  intros [g dir k t gl] H; destruct g, dir, gl; simpl in *;
  try discriminate H; destruct k, t; simpl in H;
  try discriminate H; discriminate.
Qed.

(* ---------- defects: catalog group 1.A plus the predicted fifth ---------- *)

Inductive Part := PGround | PDirection | PGoal.

Inductive Defect :=
  | D_BuiltInAssumption   (* 1.A.6: built-in assumption *)
  | D_MergedQuestions     (* 1.A.3: several questions merged into one *)
  | D_TopicExclusion      (* 1.A.4: exclusion of topics *)
  | D_ContextExclusion    (* 1.A.5: exclusion by context *)
  | D_ImpossibleGoal.     (* 1.A.7: the impossible goal — predicted (MP-7) *)

Definition damaged_part (d : Defect) : Part :=
  match d with
  | D_BuiltInAssumption => PGround
  | D_MergedQuestions   => PDirection
  | D_TopicExclusion    => PGoal
  | D_ContextExclusion  => PGoal
  | D_ImpossibleGoal    => PGoal
  end.

Definition strikes (d : Defect) (q : Question) : bool :=
  match d with
  | D_BuiltInAssumption => match q_ground q with GrFalse => true | _ => false end
  | D_MergedQuestions   => match q_direction q with DirMerged => true | _ => false end
  | D_TopicExclusion    => match q_goal q with GlTrimTopic => true | _ => false end
  | D_ContextExclusion  => match q_goal q with GlTrimContext => true | _ => false end
  | D_ImpossibleGoal    => match q_goal q with GlImpossible => true | _ => false end
  end.

Theorem wf_no_defect : forall q d, well_formed q = true -> strikes d q = false.
Proof.
  intros [g dir k t gl] d H; destruct g, dir, gl; simpl in H;
  try discriminate H; destruct d; reflexivity.
Qed.

Theorem defect_not_wf : forall q d, strikes d q = true -> well_formed q = false.
Proof.
  intros [g dir k t gl] d H; destruct d; destruct g, dir, gl; simpl in H;
  try discriminate H; reflexivity.
Qed.

(* completeness: an ill-formed question is struck by a defect
   or its target zone does not fit its goal kind *)
Theorem ill_formed_classified :
  forall q, is_question q = true -> well_formed q = false ->
    (exists d, strikes d q = true) \/ target_ok (q_kind q) (q_target q) = false.
Proof.
  intros [g dir k t gl] Hq Hw; destruct g, dir, gl; simpl in *;
  first [ discriminate Hq
        | (right; exact Hw)
        | (left; exists D_BuiltInAssumption; reflexivity)
        | (left; exists D_MergedQuestions; reflexivity)
        | (left; exists D_TopicExclusion; reflexivity)
        | (left; exists D_ContextExclusion; reflexivity)
        | (left; exists D_ImpossibleGoal; reflexivity) ].
Qed.

(* the damage map covers every part (surjectivity) *)
Theorem every_part_damageable : forall p : Part, exists d, damaged_part d = p.
Proof.
  intro p; destruct p;
  [ exists D_BuiltInAssumption | exists D_MergedQuestions | exists D_TopicExclusion ];
  reflexivity.
Qed.

(* the goal carries three kinds of damage — the asymmetry is honest *)
Theorem goal_carries_three :
  damaged_part D_TopicExclusion = PGoal /\
  damaged_part D_ContextExclusion = PGoal /\
  damaged_part D_ImpossibleGoal = PGoal.
Proof. split; [reflexivity | split; reflexivity]. Qed.

(* ---------- modal layers of the objective field (MP-5) ---------- *)

Inductive Modality := MNecessary | MActual | MPotential | MImpossible.
(* "cannot not be" | "can be — and is" | "can be, but is not" | "cannot be" *)

Definition in_field (m : Modality) : bool :=
  match m with MImpossible => false | _ => true end.

Theorem impossible_outside_field : in_field MImpossible = false.
Proof. reflexivity. Qed.

Theorem field_three_layers :
  forall m, in_field m = true ->
    m = MNecessary \/ m = MActual \/ m = MPotential.
Proof.
  intro m; destruct m; intro H;
  [ left; reflexivity | right; left; reflexivity
  | right; right; reflexivity | discriminate H ].
Qed.

(* no field element can fill an impossible category *)
Theorem no_answer_in_impossible :
  forall m : Modality, in_field m = true -> m <> MImpossible.
Proof. intros m H; destruct m; try discriminate H; discriminate. Qed.

(* the "completed svod" goal is the defect of the impossible (V11) *)
Definition completed_svod_goal : GoalState := GlImpossible.

Theorem svod_question_defective :
  forall q, q_goal q = completed_svod_goal ->
    strikes D_ImpossibleGoal q = true.
Proof. intros q H; cbn; rewrite H; reflexivity. Qed.

(* ---------- three goals: the measure of givenness (MP-6) ---------- *)

Inductive Givenness :=
  | GFull            (* both sides given — only the status is missing *)
  | GPool (n : nat)  (* a pool of S n candidates given — one-of is missing *)
  | GCategory.       (* only the category given — the sought is not in the field *)

Definition kind_of (g : Givenness) : GoalKind :=
  match g with GFull => CPolar | GPool _ => CSelective | GCategory => CFilling end.

Theorem kinds_exhaustive :
  forall g, kind_of g = CPolar \/ kind_of g = CSelective \/ kind_of g = CFilling.
Proof. intro g; destruct g; [left | right; left | right; right]; reflexivity. Qed.

(* MP-18: what each goal kind lacks — the selective question lacks a DECISION,
   not a piece of knowledge *)
Inductive Missing := MStatus | MChoice | MContent.

Definition missing_of (k : GoalKind) : Missing :=
  match k with CPolar => MStatus | CSelective => MChoice | CFilling => MContent end.

Theorem missing_injective :
  forall k1 k2, missing_of k1 = missing_of k2 -> k1 = k2.
Proof. intros k1 k2 H; destruct k1, k2; try reflexivity; discriminate H. Qed.

Theorem choice_is_not_content : MChoice <> MContent.
Proof. discriminate. Qed.

(* closers: witnessing, choice, actualization (MP-6) *)
Inductive Closer := ByWitness | ByWill | ByActualization.

Definition closes (k : GoalKind) : Closer :=
  match k with
  | CPolar => ByWitness | CSelective => ByWill | CFilling => ByActualization
  end.

Theorem closers_injective : forall k1 k2, closes k1 = closes k2 -> k1 = k2.
Proof. intros k1 k2 H; destruct k1, k2; try reflexivity; discriminate H. Qed.

Theorem closers_covered : forall c : Closer, exists k, closes k = c.
Proof.
  intro c; destruct c; [exists CPolar | exists CSelective | exists CFilling];
  reflexivity.
Qed.

(* ---------- the path to the answer: fill -> select -> verify (MP-6/7/18) ---------- *)

Inductive Step := SBuild | SSelect | SVerify.

Definition path (g : Givenness) : list Step :=
  match g with
  | GCategory => [SBuild; SSelect; SVerify]
  | GPool _   => [SSelect; SVerify]
  | GFull     => [SVerify]
  end.

(* invariant of polar closure: every path ends with the verification step *)
Theorem path_closes_polar :
  forall g, exists pre, path g = pre ++ [SVerify].
Proof.
  intro g; destruct g;
  [ exists [] | exists [SSelect] | exists [SBuild; SSelect] ]; reflexivity.
Qed.

(* truncation is only from the front: every path is a suffix of the full one *)
Definition full_path : list Step := [SBuild; SSelect; SVerify].

Theorem path_is_suffix :
  forall g, exists pre, pre ++ path g = full_path.
Proof.
  intro g; destruct g;
  [ exists [SBuild; SSelect] | exists [SBuild] | exists [] ]; reflexivity.
Qed.

(* a singleton pool still SELECTS — intuition begins, discourse verifies:
   the selective step is degenerate, not skipped (MP-7, candidate 4) *)
Theorem singleton_pool_selects : In SSelect (path (GPool 0)).
Proof. simpl; left; reflexivity. Qed.

(* no path is empty: a question is not closed without work *)
Theorem path_nonempty : forall g, path g <> [].
Proof. intro g; destruct g; discriminate. Qed.

(* ---------- constitutive order: goal -> direction -> ground (MP-7/MP-18) ---------- *)

Inductive Stage := StNone | StGoal | StDirection | StComplete.
(* assembling the act: nothing -> goal given -> direction definite -> ground taken *)

Inductive Assembles : Stage -> Prop :=
  | A_start     : Assembles StNone
  | A_goal      : Assembles StNone -> Assembles StGoal
  | A_direction : Assembles StGoal -> Assembles StDirection
  | A_ground    : Assembles StDirection -> Assembles StComplete.

(* the direction is never prior to the goal *)
Theorem direction_needs_goal : Assembles StDirection -> Assembles StGoal.
Proof. intro H; inversion H; assumption. Qed.

(* the ground is never prior to the direction *)
Theorem ground_needs_direction : Assembles StComplete -> Assembles StDirection.
Proof. intro H; inversion H; assumption. Qed.

(* every complete question has passed through the goal stage:
   the root question first says WHAT is sought *)
Theorem complete_passed_goal : Assembles StComplete -> Assembles StGoal.
Proof. intro H; apply direction_needs_goal; apply ground_needs_direction; exact H. Qed.

(* ---------- the act ground: motivation ripened to L4 (MP-8, V21) ---------- *)

Record Motivation := mkM {
  attention_drawn : bool;  (* something drew attention *)
  interest_held   : bool   (* interest: the will holds the beam, borders fixed *)
}.

Definition act_ground (m : Motivation) : bool :=
  attention_drawn m && interest_held m.

Definition act_fires (m : Motivation) : bool := act_ground m.

Theorem no_act_ground_no_act :
  forall m, act_ground m = false -> act_fires m = false.
Proof. intros m H; exact H. Qed.

(* attention alone is a precondition, not yet the ground (MP-8: no "pre-question") *)
Theorem attention_alone_insufficient : act_fires (mkM true false) = false.
Proof. reflexivity. Qed.

Theorem interest_alone_insufficient : act_fires (mkM false true) = false.
Proof. reflexivity. Qed.

Theorem act_ground_needs_both :
  forall m, act_fires m = true ->
    attention_drawn m = true /\ interest_held m = true.
Proof.
  intros [a i] H; destruct a, i; simpl in H; try discriminate H;
  split; reflexivity.
Qed.

(* V21: the ground is two-faced — the CONTENT ground lives in the composition
   (q_ground), the ACT ground fires the act (motivation); the faces are
   independent: a sound composition may stand unfired, a fired motive may
   push a broken composition *)
Theorem grounds_two_faces :
  (exists q m, well_formed q = true /\ act_fires m = false) /\
  (exists q m, well_formed q = false /\ act_fires m = true).
Proof.
  split.
  - exists (mkQ GrReal DirOne CPolar ZKnown GlWhole), (mkM true false).
    split; reflexivity.
  - exists (mkQ GrFalse DirOne CPolar ZKnown GlWhole), (mkM true true).
    split; reflexivity.
Qed.
