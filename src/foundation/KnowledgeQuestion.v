(** * KnowledgeQuestion.v — the QUESTION as a system: support, point, contour
      (formalization of MP-6/MP-7/MP-8, the mental-field working record,
       Knigi/Volya/01; sibling of KnowledgeInquiry.v / KnowledgeAnswerExists.v)

    Elements: the known support; the pointed ring-place; the contour category;
              the motivation state of the asking act.
    Roles:    support = the Elements of the act (what it stands on);
              point   = its Role (which place of the ring is taken up);
              contour = its Rule (what counts as an answer — assigns the status).
    Rules:    constitutive (generative) order contour -> point -> support
              (Rules -> Roles -> Elements on the question itself);
              integrity of the three parts = well-formedness;
              the point targets ONLY the ring (know-that-not-know);
              cascade build -> select -> verify, always closed polarly;
              the act fires only on sufficient ground (L4: attention + interest).
    Status:   the defects of catalog group 1.A are exactly damages of the three
              parts (full classification); the FIFTH defect — the contour of the
              impossible — is PREDICTED by the anatomy (MP-7) and included;
              closers: polar<->witness, selective<->will, filling<->actualization.
    STATUS: 26 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules (generative first): the contour (rule of answer-recognition) determines
      the point — an aim is definite only under a given category; the point
      differentiates the support — the known becomes support only under an acting
      aim.  The constitutive order is strict; the TEMPORAL order is free (an
      anomaly in the known may come first) — the same distinction as the domain
      sequence (logical strict / temporal free).
    Roles (L4): support carries the act; point takes up a ring-place; contour
      assigns the status "answer"; motivation ripened to sufficiency is the
      GROUND of the act (L4), not a fourth part — composition and ground do not
      mix (MP-8).
    Elements (L1+P4): finitely many states, every predicate decidable (bool);
      no completed totality anywhere — the "completed svod" contour is exactly
      the defect of the impossible layer ("cannot be", MP-5).
    P4 diagnostic (could it be otherwise?): a fourth PART is not found (an act of
      pointing needs exactly: whence, whither, what-closes); a fourth CONTOUR
      kind is impossible (givenness full / pool / category-only exhausts); the
      cascade cannot end non-polarly — whatever closes must be RECOGNIZED as
      closing, i.e. polarly checked against the contour. *)

From Stdlib Require Import List.
Import ListNotations.

(* ---------- zones of the field (in the spirit of KnowledgeInquiry.v) ---------- *)

Inductive Zone := ZKnown | ZRing | ZOuter.
(* subjective field "I know" | ring "I know that I do not know" |
   objective field beyond the border ("I do not know that I do not know") *)

Definition pointable (z : Zone) : bool :=
  match z with ZRing => true | _ => false end.

Theorem pointable_iff_ring : forall z, pointable z = true <-> z = ZRing.
Proof. intro z; destruct z; simpl; split; intro H; try reflexivity; discriminate H. Qed.

(* one cannot point into the unknown-unknown: only known unknowing is pointable *)
Theorem outer_not_pointable : pointable ZOuter = false.
Proof. reflexivity. Qed.

(* ---------- the three parts and their states ---------- *)

Inductive SupportState := SupReal | SupFalse.
(* support: real known / false support — built-in assumption (1.A.6) *)

Inductive PointState := PtOne | PtMerged | PtNone.
(* point: single / merged (1.A.3) / absent (rhetorical shell — not a question) *)

Inductive ContourState := CtWhole | CtTrimTopic | CtTrimContext | CtImpossible.
(* contour: whole / trimmed by topics (1.A.4) / trimmed by context (1.A.5) /
   contour of the impossible — outlines the "cannot be" layer (MP-7/MP-8) *)

Record Question := mkQ {
  q_support : SupportState;
  q_point   : PointState;
  q_target  : Zone;
  q_contour : ContourState
}.

Definition is_question (q : Question) : bool :=
  match q_point q with PtNone => false | _ => true end.

Definition well_formed (q : Question) : bool :=
  match q_support q, q_point q, q_contour q, q_target q with
  | SupReal, PtOne, CtWhole, ZRing => true
  | _, _, _, _ => false
  end.

Theorem wf_targets_ring : forall q, well_formed q = true -> q_target q = ZRing.
Proof.
  intros [s p t c] H; destruct s, p, c, t; simpl in H; try discriminate H; reflexivity.
Qed.

(* ---------- defects: catalog group 1.A plus the predicted fifth ---------- *)

Inductive Part := PSupport | PPoint | PContour.

Inductive Defect :=
  | D_BuiltInAssumption   (* 1.A.6: built-in assumption *)
  | D_MergedQuestions     (* 1.A.3: several questions merged into one *)
  | D_TopicExclusion      (* 1.A.4: exclusion of topics *)
  | D_ContextExclusion    (* 1.A.5: exclusion by context *)
  | D_ImpossibleContour.  (* contour of the impossible — predicted (MP-7) *)

Definition damaged_part (d : Defect) : Part :=
  match d with
  | D_BuiltInAssumption => PSupport
  | D_MergedQuestions   => PPoint
  | D_TopicExclusion    => PContour
  | D_ContextExclusion  => PContour
  | D_ImpossibleContour => PContour
  end.

Definition strikes (d : Defect) (q : Question) : bool :=
  match d with
  | D_BuiltInAssumption => match q_support q with SupFalse => true | _ => false end
  | D_MergedQuestions   => match q_point q with PtMerged => true | _ => false end
  | D_TopicExclusion    => match q_contour q with CtTrimTopic => true | _ => false end
  | D_ContextExclusion  => match q_contour q with CtTrimContext => true | _ => false end
  | D_ImpossibleContour => match q_contour q with CtImpossible => true | _ => false end
  end.

Theorem wf_no_defect : forall q d, well_formed q = true -> strikes d q = false.
Proof.
  intros [s p t c] d H; destruct s, p, c, t; simpl in H; try discriminate H;
  destruct d; reflexivity.
Qed.

Theorem defect_not_wf : forall q d, strikes d q = true -> well_formed q = false.
Proof.
  intros [s p t c] d H; destruct d; destruct s, p, c, t; simpl in H;
  try discriminate H; reflexivity.
Qed.

(* completeness: an ill-formed question is struck by a defect or misses the ring *)
Theorem ill_formed_classified :
  forall q, is_question q = true -> well_formed q = false ->
    (exists d, strikes d q = true) \/ q_target q <> ZRing.
Proof.
  intros [s p t c] Hq Hw; destruct s, p, c, t; simpl in *;
  first [ discriminate Hq
        | discriminate Hw
        | (left; exists D_BuiltInAssumption; reflexivity)
        | (left; exists D_MergedQuestions; reflexivity)
        | (left; exists D_TopicExclusion; reflexivity)
        | (left; exists D_ContextExclusion; reflexivity)
        | (left; exists D_ImpossibleContour; reflexivity)
        | (right; discriminate) ].
Qed.

(* the damage map covers every part (surjectivity) *)
Theorem every_part_damageable : forall p : Part, exists d, damaged_part d = p.
Proof.
  intro p; destruct p;
  [ exists D_BuiltInAssumption | exists D_MergedQuestions | exists D_TopicExclusion ];
  reflexivity.
Qed.

(* the contour carries three kinds of damage — the asymmetry is honest *)
Theorem contour_carries_three :
  damaged_part D_TopicExclusion = PContour /\
  damaged_part D_ContextExclusion = PContour /\
  damaged_part D_ImpossibleContour = PContour.
Proof. split; [reflexivity | split; reflexivity]. Qed.

(* ---------- modal layers of the objective field (MP-5) ---------- *)

Inductive Modality := MActual | MPotential | MImpossible.
(* "can be — and is" | "can be, but is not" | "cannot be" *)

Definition in_field (m : Modality) : bool :=
  match m with MImpossible => false | _ => true end.

Theorem impossible_outside_field : in_field MImpossible = false.
Proof. reflexivity. Qed.

Theorem field_two_layers :
  forall m, in_field m = true -> m = MActual \/ m = MPotential.
Proof.
  intro m; destruct m; intro H;
  [ left; reflexivity | right; reflexivity | discriminate H ].
Qed.

(* no field element can fill an impossible category *)
Theorem no_answer_in_impossible :
  forall m : Modality, in_field m = true -> m <> MImpossible.
Proof. intros m H; destruct m; try discriminate H; discriminate. Qed.

(* the "completed svod" contour is the defect of the impossible (V11) *)
Definition completed_svod_contour : ContourState := CtImpossible.

Theorem svod_question_defective :
  forall q, q_contour q = completed_svod_contour ->
    strikes D_ImpossibleContour q = true.
Proof. intros q H; cbn; rewrite H; reflexivity. Qed.

(* ---------- three contours: the measure of givenness (MP-6) ---------- *)

Inductive Givenness :=
  | GFull            (* both sides given — only the status is missing *)
  | GPool (n : nat)  (* a pool of S n candidates given — one-of is missing *)
  | GCategory.       (* only the category given — the sought is not in the field *)

Inductive ContourKind := CPolar | CSelective | CFilling.

Definition kind_of (g : Givenness) : ContourKind :=
  match g with GFull => CPolar | GPool _ => CSelective | GCategory => CFilling end.

Theorem kinds_exhaustive :
  forall g, kind_of g = CPolar \/ kind_of g = CSelective \/ kind_of g = CFilling.
Proof. intro g; destruct g; [left | right; left | right; right]; reflexivity. Qed.

(* closers: witnessing, choice, actualization (MP-6) *)
Inductive Closer := ByWitness | ByWill | ByActualization.

Definition closes (k : ContourKind) : Closer :=
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

(* ---------- the cascade: build -> select -> verify (MP-6/MP-7) ---------- *)

Inductive Step := SBuild | SSelect | SVerify.

Definition cascade (g : Givenness) : list Step :=
  match g with
  | GCategory => [SBuild; SSelect; SVerify]
  | GPool _   => [SSelect; SVerify]
  | GFull     => [SVerify]
  end.

(* invariant of polar closure: every cascade ends with the verification step *)
Theorem cascade_closes_polar :
  forall g, exists pre, cascade g = pre ++ [SVerify].
Proof.
  intro g; destruct g;
  [ exists [] | exists [SSelect] | exists [SBuild; SSelect] ]; reflexivity.
Qed.

(* truncation is only from the front: every cascade is a suffix of the full one *)
Definition full_cascade : list Step := [SBuild; SSelect; SVerify].

Theorem cascade_is_suffix :
  forall g, exists pre, pre ++ cascade g = full_cascade.
Proof.
  intro g; destruct g;
  [ exists [SBuild; SSelect] | exists [SBuild] | exists [] ]; reflexivity.
Qed.

(* a singleton pool still SELECTS — intuition begins, discourse verifies:
   the selective step is degenerate, not skipped (MP-7, candidate 4) *)
Theorem singleton_pool_selects : In SSelect (cascade (GPool 0)).
Proof. simpl; left; reflexivity. Qed.

(* no cascade is empty: a question is not closed without work *)
Theorem cascade_nonempty : forall g, cascade g <> [].
Proof. intro g; destruct g; discriminate. Qed.

(* ---------- constitutive order: contour -> point -> support (MP-7) ---------- *)

Inductive Stage := StNone | StContour | StPoint | StComplete.
(* assembling the act: nothing -> contour given -> point definite -> support taken *)

Inductive Assembles : Stage -> Prop :=
  | A_start   : Assembles StNone
  | A_contour : Assembles StNone -> Assembles StContour
  | A_point   : Assembles StContour -> Assembles StPoint
  | A_support : Assembles StPoint -> Assembles StComplete.

(* the point is never prior to the contour *)
Theorem point_needs_contour : Assembles StPoint -> Assembles StContour.
Proof. intro H; inversion H; assumption. Qed.

(* the support is never prior to the point *)
Theorem support_needs_point : Assembles StComplete -> Assembles StPoint.
Proof. intro H; inversion H; assumption. Qed.

(* every complete question has passed through the contour stage *)
Theorem complete_passed_contour : Assembles StComplete -> Assembles StContour.
Proof. intro H; apply point_needs_contour; apply support_needs_point; exact H. Qed.

(* ---------- the ground of the act: motivation ripened to L4 (MP-8) ---------- *)

Record Motivation := mkM {
  attention_drawn : bool;  (* something drew attention *)
  interest_held   : bool   (* interest: the will holds the beam, borders fixed *)
}.

Definition sufficient_ground (m : Motivation) : bool :=
  attention_drawn m && interest_held m.

Definition act_fires (m : Motivation) : bool := sufficient_ground m.

Theorem no_ground_no_act :
  forall m, sufficient_ground m = false -> act_fires m = false.
Proof. intros m H; exact H. Qed.

(* attention alone is a precondition, not yet the ground (MP-8: no "pre-question") *)
Theorem attention_alone_insufficient : act_fires (mkM true false) = false.
Proof. reflexivity. Qed.

Theorem interest_alone_insufficient : act_fires (mkM false true) = false.
Proof. reflexivity. Qed.

Theorem ground_needs_both :
  forall m, act_fires m = true ->
    attention_drawn m = true /\ interest_held m = true.
Proof.
  intros [a i] H; destruct a, i; simpl in H; try discriminate H;
  split; reflexivity.
Qed.
