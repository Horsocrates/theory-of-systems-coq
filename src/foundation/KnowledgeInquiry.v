(** * KnowledgeInquiry.v — fork (d→inquiry): the QUESTION as a pointing act — a request that directs
      attention at a region of the field of possible knowledge ("I know that I don't know"), distinct
      from the gap it points at and from the access process that may (or may not) answer it

    Closes the inquiry fork, absorbing fork (d) selection.  Built on the AUTHOR'S CORRECTIONS
    (2026-06-13), which sharpen the ontology decisively:

      * A question is NOT an open distinction.  The open distinction (the gap) is ONE of the L4/ЗДО
        criteria for a question to ARISE — not the question itself.  The question is the ACT-request
        that points attention at a region.
      * The L4 criteria for a well-founded question: (1) a data-information base; (2) an open
        distinction (unresolved); (3) DELINEABILITY (we can mark the region as "known-unknown" — tell
        it apart from the unknown-unknown); (4) attention to direct.  REACHABILITY is NOT a criterion:
        you can ask without seeing a road to the answer — it is enough to understand there is a field
        of non-knowledge.
      * A correct question does NOT guarantee an answer.  It merely POINTS at a region of the field;
        ACCESS to that region (whether the data yield the answer, whether a road exists) is a wholly
        SEPARATE process — the rest of the branch (gap / depth / failure modes).  Correct question
        =/= answerable question.
      * The telos is ANY movement in the field — deepening OR broadening — not depth alone.

    The field of possible knowledge is an ANNULUS:
        RESOLVED            |   FIELD = "know that I don't know"   |   UNKNOWN-UNKNOWN
        (nothing to ask)    |   delineable /\ unresolved           |   (no frame to ask with)
        ----------------[ inner: answers push out ]----[ outer: data push out ]----------
    The well-founded question lives ONLY in the middle.  Reachability (access) is an ORTHOGONAL
    overlay, NOT a boundary of the annulus.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      R-ground (L4/ЗДО): a question ARISES iff its criteria hold — (1) a data-information base,
                 (2) an open distinction, (3) delineability (mark the region vs the unknown-unknown),
                 (4) attention.  The open distinction is ONE criterion, not the question;
                 REACHABILITY is NOT a criterion.
      R-attention (L5/R3): the question DIRECTS attention at ONE region — a single focus (this is the
                 directing act; it subsumes fork (d) selection).
      R-pointing-not-access: the question POINTS at a region; whether information is there / reachable
                 is a SEPARATE process.  A correct question may have no road.
    Roles (L4): data-information = the base; the field of possible knowledge = the known-unknown
      (delineable /\ unresolved); the open distinction = one ground-criterion; the question = the
      attention-directing pointing act; access = the separate acquisition process (the rest of the
      branch).
    Elements (L1+P4): topics / possible distinctions; resolved (inner boundary), delineable (outer
      boundary), accessible (an orthogonal overlay); the target; the direction (deepen / broaden).
    P4 diagnostic (could it be otherwise?):
      The well-founded question lives ONLY in the middle annulus (delineable /\ unresolved) — bounded
      inside by the resolved (nothing to ask) and outside by the undelineable (unknown-unknown, no
      frame).  Reachability does NOT bound it: a question can be well-founded with no road
      (question_without_road).  Pointing is INDEPENDENT of accessing — all four
      (question? x road?) quadrants occur (question_access_independent).  Telos = any movement
      (telos_both_directions).
    Honesty wall:
      This is the STRUCTURE of the question-as-pointing-act; "attention / will / consciousness" is the
      INTERPRETATION.  Access (whether the data yield the answer) is explicitly SEPARATED out and
      handed to the existing branch (KnowledgeGap / KnowledgeDepth / KnowledgeFailure), NOT conflated
      with the question.  stdlib-only and robust; the cross-links are in prose.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Bool.

(* ===================================================================== *)
(*  PART I — the field of possible knowledge; the question as pointing      *)
(* ===================================================================== *)

Section Inquiry.
Context {T : Type}.
Variable resolved   : T -> bool.   (* already known — the inner boundary *)
Variable delineable : T -> bool.   (* markable as "known-unknown" from current data — outer boundary *)

(** The field of possible knowledge: "I know that I don't know" — delineable but unresolved. *)
Definition in_field (t : T) : Prop := delineable t = true /\ resolved t = false.

(** A well-founded question POINTS at a target in the field.  Pointing needs delineability + an open
    distinction — NOT reachability (no [accessible] term appears). *)
Definition well_founded_question (t : T) : Prop := in_field t.

(** ★ The open distinction is NECESSARY for a well-founded question (one of the L4 criteria). *)
Theorem open_necessary : forall t, well_founded_question t -> resolved t = false.
Proof. intros t [_ H]. exact H. Qed.

(** ★ Delineability is NECESSARY — the question must point at a markable region, not the
    unknown-unknown. *)
Theorem delineable_necessary : forall t, well_founded_question t -> delineable t = true.
Proof. intros t [H _]. exact H. Qed.

(** ★★ THE CORRECTION, formally: a well-founded question is EXACTLY "delineable /\ unresolved" — it
    is POINTING, with NO reference to access/reachability.  The question and the road are different
    things. *)
Theorem question_is_pointing_not_access : forall t,
  well_founded_question t <-> (delineable t = true /\ resolved t = false).
Proof. intros t. unfold well_founded_question, in_field. tauto. Qed.

(** ★★ The three zones: every topic is resolved, OR in the field (known-unknown), OR
    unknown-unknown.  Only the middle admits a well-founded question. *)
Theorem three_zones : forall t,
  (resolved t = true)                                   (* resolved: nothing to ask *)
  \/ (delineable t = true /\ resolved t = false)        (* field: the question lives here *)
  \/ (delineable t = false /\ resolved t = false).      (* unknown-unknown: no frame to ask with *)
Proof.
  intros t. destruct (resolved t) eqn:Hr.
  - left. reflexivity.
  - destruct (delineable t) eqn:Hd.
    + right; left. split; reflexivity.
    + right; right. split; reflexivity.
Qed.

(** The question points at ONE target (the indication relation). *)
Definition points_at (target t : T) : Prop := t = target.

(** ★ The question DIRECTS attention at exactly ONE target (R3, single focus) — selection from the
    field is the question's directing function (this is fork (d), absorbed). *)
Theorem question_directs_one : forall target,
  well_founded_question target ->
  exists! t, points_at target t /\ well_founded_question t.
Proof.
  intros target H. exists target. split.
  - split; [ reflexivity | exact H ].
  - intros t' [Ht' _]. symmetry. exact Ht'.
Qed.

End Inquiry.

(* ===================================================================== *)
(*  PART II — a concrete model: pointing is INDEPENDENT of access           *)
(*  (topic 0 resolved; 1 known-unknown with road; 2 known-unknown NO road;  *)
(*   3 unknown-unknown)                                                      *)
(* ===================================================================== *)

Definition c_resolved (n : nat) : bool :=
  match n with O => true | _ => false end.
Definition c_delineable (n : nat) : bool :=
  match n with O => true | S O => true | S (S O) => true | _ => false end.
Definition c_accessible (n : nat) : bool :=
  match n with O => true | S O => true | _ => false end.

(** ★★★ THE KEY WITNESS (the correction): topic 2 is a perfectly WELL-FOUNDED question (delineable,
    unresolved) with NO road to the answer (not accessible).  Correct question, no answer guaranteed
    — pointing is not accessing. *)
Theorem question_without_road :
  well_founded_question c_resolved c_delineable 2 /\ c_accessible 2 = false.
Proof.
  split.
  - unfold well_founded_question, in_field. split; reflexivity.
  - reflexivity.
Qed.

(** ★★ Pointing is INDEPENDENT of accessing: all four (question? x road?) quadrants occur.
    (1) question with a road; (2) question WITHOUT a road [the correction]; (3) access without a
    question [the already-resolved]; (4) neither [the unknown-unknown]. *)
Theorem question_access_independent :
     (well_founded_question c_resolved c_delineable 1 /\ c_accessible 1 = true)
  /\ (well_founded_question c_resolved c_delineable 2 /\ c_accessible 2 = false)
  /\ (~ well_founded_question c_resolved c_delineable 0 /\ c_accessible 0 = true)
  /\ (~ well_founded_question c_resolved c_delineable 3 /\ c_accessible 3 = false).
Proof.
  split; [ | split; [ | split ] ].
  - split; [ unfold well_founded_question, in_field; split; reflexivity | reflexivity ].
  - split; [ unfold well_founded_question, in_field; split; reflexivity | reflexivity ].
  - split; [ unfold well_founded_question, in_field; intros [_ Hr]; discriminate Hr | reflexivity ].
  - split; [ unfold well_founded_question, in_field; intros [Hd _]; discriminate Hd | reflexivity ].
Qed.

(** ★ The open distinction is NOT SUFFICIENT: topic 3 is unresolved (open) yet undelineable
    (unknown-unknown) — so it is NOT a well-founded question.  The gap is one criterion, not the
    question. *)
Theorem gap_not_sufficient :
  c_resolved 3 = false /\ ~ well_founded_question c_resolved c_delineable 3.
Proof.
  split.
  - reflexivity.
  - unfold well_founded_question, in_field. intros [Hd _]. discriminate Hd.
Qed.

(** Direction tag: a question can move DEEPER or BROADER. *)
Inductive Dir := Deepen | Broaden.
Definition c_kind (n : nat) : Dir := match n with S O => Deepen | _ => Broaden end.

(** ★ The telos is ANY movement in the field — deepening (topic 1) AND broadening (topic 2) are both
    well-founded questions.  Not depth alone. *)
Theorem telos_both_directions :
  (well_founded_question c_resolved c_delineable 1 /\ c_kind 1 = Deepen)
  /\ (well_founded_question c_resolved c_delineable 2 /\ c_kind 2 = Broaden).
Proof.
  split.
  - split; [ unfold well_founded_question, in_field; split; reflexivity | reflexivity ].
  - split; [ unfold well_founded_question, in_field; split; reflexivity | reflexivity ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ Inquiry: the question is the POINTING act at the field of possible knowledge (delineable /\
    unresolved), with NO access criterion (question_is_pointing_not_access); the open distinction is
    necessary but only one criterion (open_necessary, gap_not_sufficient); every topic falls in one
    of three zones (three_zones), the question living only in the middle; and pointing is independent
    of accessing (question_without_road). *)
Theorem inquiry_capstone : forall {T} (resolved delineable : T -> bool) (t : T),
  (well_founded_question resolved delineable t <-> (delineable t = true /\ resolved t = false))
  /\ (well_founded_question resolved delineable t -> resolved t = false /\ delineable t = true)
  /\ ((resolved t = true)
      \/ (delineable t = true /\ resolved t = false)
      \/ (delineable t = false /\ resolved t = false)).
Proof.
  intros T resolved delineable t. split; [ | split ].
  - exact (question_is_pointing_not_access resolved delineable t).
  - intro H. split; [ exact (open_necessary resolved delineable t H)
                    | exact (delineable_necessary resolved delineable t H) ].
  - exact (three_zones resolved delineable t).
Qed.

Print Assumptions inquiry_capstone.
Print Assumptions question_without_road.
Print Assumptions question_access_independent.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  10 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The QUESTION is a pointing act, not the gap it points at.  It is well-     *)
(*  founded iff its target is delineable and unresolved — the middle of the   *)
(*  annulus (three_zones), bounded inside by the resolved and outside by the  *)
(*  unknown-unknown.  The open distinction is necessary but only ONE L4        *)
(*  criterion (open_necessary, gap_not_sufficient); REACHABILITY is NOT a      *)
(*  criterion (question_is_pointing_not_access).  Pointing is INDEPENDENT of   *)
(*  accessing — a correct question may have no road (question_without_road),   *)
(*  all four quadrants occur (question_access_independent); access is the      *)
(*  separate process handed to KnowledgeGap / KnowledgeDepth / KnowledgeFailure.*)
(*  The question directs attention at ONE target (question_directs_one,        *)
(*  absorbing fork d); telos = any movement, deepen or broaden                 *)
(*  (telos_both_directions).  Fork (inquiry) of the F-39 branch; stdlib-only. *)
(* ========================================================================= *)
