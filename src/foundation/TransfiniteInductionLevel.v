(** * TransfiniteInductionLevel.v — well-founded induction over the Level hierarchy
    Elements: Level (L1 | LS), level_lt, level_depth
    Roles:    level_lt = the foundation order; level_depth = its nat rank
    Rules:    level_lt strictly decreases depth => well-founded => strong
              induction; the successor LS always escapes => no top level
    STATUS:   9 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    Complements foundation/TransfiniteInduction.v (which is about the ordinal
    notations Ord): HERE the well-founded induction is over the ToS membership
    hierarchy Level (L1 | LS) itself — the order that structurally blocks
    self-membership (P1).

    G2: well-founded / strong induction over Level (level_lt_wf,
        level_strong_induction).
    G3: no level lies above all levels — the "set of all ordinals" /
        Burali-Forti paradox dissolves structurally: the successor LS of any
        candidate top escapes it (level_no_top, no_universal_level).

    E/R/R reading: the hierarchy is a RULE (the foundation order), not a
    completed Element-object "the level of all levels"; the very attempt to
    name a top is refuted by one more step LS.

    Nov 2026 (last section).  Elements: a criterion and its level label; a
    system that would collect "all systems of its level not members of
    themselves"; a nonempty collection of levels.  Roles: the label never
    plays "own level"; no system plays "Russell collector"; some member of
    the collection plays "minimal".  Rules: P2 + irreflexivity; the diagonal;
    well-foundedness.  russell_paradox_blocked in Core_ERR is stated for L2
    only and speaks about the label: here the same content for every level
    (criterion_label_never_own_level), the Russell collection itself on every
    level (russell_blocked_every_level), and well-foundedness in the form
    closest to the axiom of Foundation (level_foundation_form).
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From Stdlib Require Import Wf_nat Lia.

(* ===================== G2: well-founded induction over Level ============= *)

(* level_lt is well-founded because it strictly decreases the nat rank
   level_depth (level_lt_depth, proved in Core_ERR). 0 axioms. *)
Lemma level_lt_wf : well_founded level_lt.
Proof.
  apply (Wf_nat.well_founded_lt_compat Level level_depth).
  exact level_lt_depth.
Qed.

(* Strong (course-of-values) induction over the Level hierarchy *)
Theorem level_strong_induction :
  forall P : Level -> Prop,
    (forall L, (forall L', L' << L -> P L') -> P L) ->
    forall L, P L.
Proof.
  intros P H. apply (well_founded_ind level_lt_wf). exact H.
Qed.

(* ===================== G3: no top level (Burali-Forti analogue) ========= *)

(* Every level is strictly below its own successor *)
Lemma level_lt_succ : forall L, L << LS L.
Proof. intros L. simpl. left. reflexivity. Qed.

(* The successor of L is neither below L nor equal to L *)
Lemma succ_not_le : forall L, ~ (LS L << L \/ LS L = L).
Proof.
  intros L [Hlt | Heq].
  - apply level_lt_depth in Hlt. simpl in Hlt. lia.
  - assert (Hd : level_depth (LS L) = level_depth L) by (rewrite Heq; reflexivity).
    simpl in Hd. lia.
Qed.

(* For any candidate top M, some level (its successor) escapes it:
   it is neither below M nor equal to M. *)
Theorem level_no_top :
  forall M : Level, exists L : Level, ~ (L << M \/ L = M).
Proof.
  intros M. exists (LS M). apply succ_not_le.
Qed.

(* Hence there is NO universal level above-or-equal to every level.
   The "level of all levels" cannot exist (Burali-Forti, dissolved). *)
Theorem no_universal_level :
  ~ exists Top : Level, forall L : Level, L << Top \/ L = Top.
Proof.
  intros [Top Hall].
  exact (succ_not_le Top (Hall (LS Top))).
Qed.

(* ===================== Nov 2026: Russell on every level; Foundation form === *)

(* The level label of a criterion's domain is never the criterion's own
   level: P2 (crit_level_valid) + irreflexivity of <<.  This is the content
   of russell_paradox_blocked (Core_ERR), there stated for L2 only and with a
   premise about the domain which its proof does not use. *)
Theorem criterion_label_never_own_level :
  forall (L : Level) (C : Criterion L), crit_level_witness L C <> L.
Proof.
  intros L C Heq.
  pose proof (crit_level_valid L C) as Hv.
  rewrite Heq in Hv.
  exact (level_lt_irrefl L Hv).
Qed.

(* Russell's collection itself: on NO level is there a system that collects
   exactly those systems of the level which are not members of themselves --
   whatever the membership relation.  The diagonal does not use the level:
   the same holds on any carrier (cs/RussellViaLawvere.russell_no_universal_set). *)
Theorem russell_blocked_every_level :
  forall (L : Level) (mem : System L -> System L -> Prop),
    ~ exists R : System L, forall X : System L, mem X R <-> ~ mem X X.
Proof.
  intros L mem [R HR].
  destruct (HR R) as [H1 H2].
  assert (Hn : ~ mem R R) by (intro Hm; exact (H1 Hm Hm)).
  exact (Hn (H2 Hn)).
Qed.

(* Well-foundedness in the form closest to the axiom of Foundation: in a
   nonempty collection of levels not every member has a member strictly
   below it -- some member is minimal. *)
Theorem level_foundation_form :
  forall P : Level -> Prop,
    (exists l, P l) ->
    ~ (forall l, P l -> exists l', P l' /\ l' << l).
Proof.
  intros P [l0 Hl0] Hno.
  revert Hl0. induction l0 as [l IH] using level_strong_induction.
  intro Hl. destruct (Hno l Hl) as [l' [Hl' Hlt]].
  exact (IH l' Hlt Hl').
Qed.
