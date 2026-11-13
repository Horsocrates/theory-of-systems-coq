(** * PrinciplesFromLawsDerived.v — What of the principles is DERIVED, with the
      laws standing as premises; and what the number "two" rests on

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, chapter I.4, places 1-8, 2026-11-13):

    Elements: systems, levels and a membership relation between systems
              (abstract carriers); a distinction with its two sides; a
              criterion with its level label; a typing context.
    Roles:    L1 (a system has ONE level) and L5 (the order of levels is
              irreflexive; what is organized lies below its organizer) — as
              PREMISES; membership — a relation that lowers the level;
              the position (role) occupied by a side of a distinction.
    Rules:    (1) P1, no self-membership, FOLLOWS from L1 and L5 taken as
                  premises, and each premise is needed (counter-models);
              (2) under a level-lowering membership Russell's condition holds
                  of everything, a collector over the whole universe does not
                  exist, a collector over the lower levels is harmless;
              (3) the level label of [Criterion] is independent of its
                  content; a criterion whose label is tied to the content
                  excludes "S is what satisfies S";
              (4) intensional equality of systems is equality of the three
                  fields of the record — that is, equality of the records;
                  the same criterion alone is not enough;
              (5) "two": the sides of a distinction are two DISTINCT
                  elements; any labelling of the sides needs two positions,
                  and two suffice; without either rule of the record the
                  sides may coincide;
              (6) the typing judgment [HasType] is equivalent to the
                  well-formedness of the context.
    P4 diagnostic ("could it be otherwise?"): nothing infinite is used.
              Forced: P1 once L1 and L5 are granted; "two" for elements and
              positions. NOT forced, and not derived here: P2 (a field of
              the record [Criterion]), P3 (a definition), P4 (the choice of
              the type nat -> Q). The reading of L1 as "one level per
              system" is a modelling decision and is stated as a premise.

    STATUS: 28 Qed, 0 Admitted
    AXIOMS: none — except [complete_foundation_with_sides], whose first
            conjunct builds a distinction for every proposition and so
            rests on Classical_Prop.classic; the same statement without that
            conjunct, [foundation_core_closed], is closed.
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.DistinctionCoDefinition.
From ToS Require Import foundation.ERRFromDistinction.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import Judgments.
From ToS Require Import FormationRules.

(* ========================================================================= *)
(*  1. P1 FROM L1 AND L5 — the laws stand as premises                        *)
(* ========================================================================= *)

Section P1_Derived.
  Variable U : Type.                      (* systems *)
  Variable Lv : Type.                     (* levels *)
  Variable lt : Lv -> Lv -> Prop.         (* order of levels *)
  Variable at_level : U -> Lv -> Prop.    (* "x is located at level l" *)
  Variable mem : U -> U -> Prop.          (* "x is organized by the system y" *)

  (** L1, determinate identity: a system has one level. *)
  Definition L1_determinate_level : Prop :=
    forall x l1 l2, at_level x l1 -> at_level x l2 -> l1 = l2.

  (** L5: the order of levels is irreflexive. *)
  Definition L5_irreflexive : Prop := forall l, ~ lt l l.

  (** L5: what is organized lies below its organizer. *)
  Definition L5_organized_below : Prop :=
    forall x y, mem x y ->
      exists lx ly, at_level x lx /\ at_level y ly /\ lt lx ly.

  (** P1: no system is organized by itself. *)
  Theorem P1_from_L1_and_L5 :
    L1_determinate_level -> L5_irreflexive -> L5_organized_below ->
    forall x, ~ mem x x.
  Proof.
    intros HL1 Hirr Hbelow x Hm.
    destruct (Hbelow x x Hm) as [lx [ly [Hx [Hy Hlt]]]].
    rewrite (HL1 x lx ly Hx Hy) in Hlt.
    exact (Hirr ly Hlt).
  Qed.
End P1_Derived.

(** L1 is needed: a model where L5 holds in both forms and a system
    contains itself (the system has two levels at once). *)
Theorem P1_needs_L1 :
  exists (U Lv : Type) (lt : Lv -> Lv -> Prop)
         (at_level : U -> Lv -> Prop) (mem : U -> U -> Prop),
    L5_irreflexive Lv lt /\
    L5_organized_below U Lv lt at_level mem /\
    exists x, mem x x.
Proof.
  exists unit, bool, (fun a b => a = false /\ b = true),
         (fun _ _ => True), (fun _ _ => True).
  split; [| split].
  - intros l [H1 H2]. rewrite H1 in H2. discriminate H2.
  - intros x y _. exists false, true. split; [exact I | split; [exact I |]].
    split; reflexivity.
  - exists tt. exact I.
Qed.

(** Irreflexivity (L5) is needed. *)
Theorem P1_needs_L5 :
  exists (U Lv : Type) (lt : Lv -> Lv -> Prop)
         (at_level : U -> Lv -> Prop) (mem : U -> U -> Prop),
    L1_determinate_level U Lv at_level /\
    L5_organized_below U Lv lt at_level mem /\
    exists x, mem x x.
Proof.
  exists unit, unit, (fun _ _ => True), (fun _ _ => True), (fun _ _ => True).
  split; [| split].
  - intros x l1 l2 _ _. destruct l1, l2. reflexivity.
  - intros x y _. exists tt, tt. split; [exact I | split; exact I].
  - exists tt. exact I.
Qed.

(** The instance on the type [Level] of the formalization: any membership
    that lowers the level has no self-membership. *)
Corollary no_self_membership_Level :
  forall (U : Type) (lev : U -> Level) (mem : U -> U -> Prop),
    (forall x y, mem x y -> lev x << lev y) -> forall x, ~ mem x x.
Proof.
  intros U lev mem Hlow.
  apply (P1_from_L1_and_L5 U Level level_lt (fun x l => lev x = l) mem).
  - intros x l1 l2 H1 H2. rewrite <- H1. exact H2.
  - exact level_lt_irrefl.
  - intros x y Hm. exists (lev x), (lev y).
    split; [reflexivity | split; [reflexivity | exact (Hlow x y Hm)]].
Qed.

(* ========================================================================= *)
(*  2. RUSSELL AND THE HIERARCHY — with membership in the statement          *)
(* ========================================================================= *)

Section RussellHierarchy.
  Variable U : Type.
  Variable lev : U -> Level.
  Variable mem : U -> U -> Prop.
  Hypothesis mem_lowers : forall x y, mem x y -> lev x << lev y.

  (** Russell's condition "x does not contain itself" holds of everything:
      the question of self-membership is always settled in the negative. *)
  Theorem russell_condition_holds_everywhere : forall x, ~ mem x x.
  Proof. exact (no_self_membership_Level U lev mem mem_lowers). Qed.

  (** There is no collector of Russell's condition over the whole universe:
      it would contain everything, itself included. *)
  Theorem no_russell_collector : forall r,
    ~ (forall x, mem x r <-> ~ mem x x).
  Proof.
    intros r H.
    apply (russell_condition_holds_everywhere r).
    apply (proj2 (H r)). exact (russell_condition_holds_everywhere r).
  Qed.

  (** A collector taken over the levels BELOW its own is harmless: it
      contains everything below and does not contain itself. *)
  Theorem levelled_collector_is_harmless : forall r,
    (forall x, lev x << lev r -> (mem x r <-> ~ mem x x)) ->
    ~ mem r r /\ (forall x, lev x << lev r -> mem x r).
  Proof.
    intros r H. split.
    - exact (russell_condition_holds_everywhere r).
    - intros x Hx. apply (proj2 (H x Hx)).
      exact (russell_condition_holds_everywhere x).
  Qed.
End RussellHierarchy.

(* ========================================================================= *)
(*  3. P2 — the level label of a criterion                                   *)
(* ========================================================================= *)

(** In the record [Criterion] the level label is independent of the domain
    and the predicate: any content carries any admissible label. *)
Theorem level_label_is_free : forall (L l : Level) (D : Type) (p : D -> Prop),
  l << L ->
  exists C : Criterion L,
    crit_domain L C = D /\ crit_level_witness L C = l.
Proof.
  intros L l D p H. exists (mkCriterion L D p l H). split; reflexivity.
Qed.

(** A criterion whose level IS tied to its content: whatever satisfies a
    criterion of level L lies below L. *)
Section LevelledCriterion.
  Variable U : Type.
  Variable lev : U -> Level.

  Record LevelledCriterion (L : Level) : Type := mkLevelledCriterion {
    lc_pred : U -> Prop;
    lc_below : forall x, lc_pred x -> lev x << L
  }.

  (** An object of level L does not satisfy a criterion of level L. *)
  Theorem criterion_excludes_own_level :
    forall (L : Level) (C : LevelledCriterion L) (s : U),
      lev s = L -> ~ lc_pred L C s.
  Proof.
    intros L C s Hs Hp. apply (level_lt_irrefl L).
    rewrite <- Hs at 1. exact (lc_below L C s Hp).
  Qed.

  (** "S is what satisfies S" is excluded. *)
  Theorem levelled_membership_no_self :
    forall (crit : forall s : U, LevelledCriterion (lev s)) (s : U),
      ~ lc_pred (lev s) (crit s) s.
  Proof.
    intros crit s. apply (criterion_excludes_own_level (lev s) (crit s) s).
    reflexivity.
  Qed.

  (** Membership given by such criteria lowers the level, so Section 2
      applies to it. *)
  Theorem levelled_membership_lowers :
    forall (crit : forall s : U, LevelledCriterion (lev s)) (x s : U),
      lc_pred (lev s) (crit s) x -> lev x << lev s.
  Proof. intros crit x s H. exact (lc_below (lev s) (crit s) x H). Qed.
End LevelledCriterion.

(* ========================================================================= *)
(*  4. P3 — intensional equality of systems                                  *)
(* ========================================================================= *)

(** [systems_intensionally_equal] is equality of the records. *)
Theorem intensional_iff_eq : forall (L : Level) (S1 S2 : System L),
  systems_intensionally_equal S1 S2 <-> S1 = S2.
Proof.
  intros L S1 S2. unfold systems_intensionally_equal. split.
  - destruct S1 as [c1 p1 u1], S2 as [c2 p2 u2]. simpl.
    intros [Hc [Hp Hu]]. subst. reflexivity.
  - intro H. subst. split; [| split]; reflexivity.
Qed.

(** The same criterion alone is not enough for intensional equality. *)
Theorem same_criterion_not_enough :
  exists S1 S2 : System L2,
    sys_criterion L2 S1 = sys_criterion L2 S2 /\
    ~ systems_intensionally_equal S1 S2.
Proof.
  exists (mkSystem L2 nat_gt_5_criterion Unbounded MultiplePerRole),
         (mkSystem L2 nat_gt_5_criterion (Finite 0) MultiplePerRole).
  split; [reflexivity |].
  intros [_ [H _]]. simpl in H. discriminate H.
Qed.

(* ========================================================================= *)
(*  5. "TWO" — elements, positions, rules                                    *)
(* ========================================================================= *)

(** Two elements: the list of sides has no repetition and length 2.
    (The distinctness of the sides uses BOTH rules of the record.) *)
Theorem elements_nodup : forall D : Distinction, NoDup (err_elements D).
Proof.
  intro D. unfold err_elements. constructor.
  - intros [H | H].
    + exact (sides_distinct D (eq_sym H)).
    + exact H.
  - constructor.
    + intro H. exact H.
    + constructor.
Qed.

Theorem two_distinct_elements : forall D : Distinction,
  NoDup (err_elements D) /\ length (err_elements D) = 2.
Proof. intro D. split; [exact (elements_nodup D) | reflexivity]. Qed.

(** Two positions: under ANY labelling of the sides by positions, the
    position of the distinguished and the position of the background differ. *)
Theorem two_positions_needed :
  forall (D : Distinction) (I : Type) (side : I -> Prop) (i j : I),
    side i = Distinction.positive D -> side j = negative D -> i <> j.
Proof.
  intros D I side i j Hi Hj Heq. subst j.
  apply (sides_distinct D). rewrite <- Hi. exact Hj.
Qed.

(** One position is not enough. *)
Corollary one_position_insufficient :
  forall (D : Distinction) (side : unit -> Prop),
    ~ ((exists i, side i = Distinction.positive D) /\
       (exists j, side j = negative D)).
Proof.
  intros D side [[i Hi] [j Hj]].
  apply (two_positions_needed D unit side i j Hi Hj).
  destruct i, j. reflexivity.
Qed.

(** Two positions suffice: the labelling "distinguished / background" is
    injective. *)
Definition side_of (D : Distinction) (b : bool) : Prop :=
  if b then Distinction.positive D else negative D.

Theorem side_of_injective : forall (D : Distinction) (b1 b2 : bool),
  side_of D b1 = side_of D b2 -> b1 = b2.
Proof.
  intros D b1 b2 H. destruct b1, b2; simpl in H.
  - reflexivity.
  - exfalso. exact (sides_distinct D H).
  - exfalso. exact (sides_distinct D (eq_sym H)).
  - reflexivity.
Qed.

(** Two rules: without either of them the sides may coincide. (That
    neither rule follows from the other: DistinctionCoDefinition.v.) *)
Theorem without_exclusive_sides_may_coincide :
  exists P N : Prop, (P \/ N) /\ P = N.
Proof. exists True, True. split; [left; exact I | reflexivity]. Qed.

Theorem without_exhaustive_sides_may_coincide :
  exists P N : Prop, ~ (P /\ N) /\ P = N.
Proof.
  exists False, False. split.
  - intros [H _]. exact H.
  - reflexivity.
Qed.

(** The counters of ERRFromDistinction.v are constants: they do not depend
    on the distinction, and the theorems about them unfold a definition. *)
Lemma err_role_count_constant : forall D1 D2 : Distinction,
  err_role_count D1 = err_role_count D2.
Proof. reflexivity. Qed.

(** [complete_foundation] with a third conjunct that has content: the two
    sides are distinct. Without the first conjunct — no axiom. *)
Theorem foundation_core_closed :
  (forall D, ~ (Distinction.positive D /\ negative D) /\
             (Distinction.positive D \/ negative D)) /\
  (forall D, Distinction.positive D <> negative D /\
             NoDup (err_elements D) /\ length (err_elements D) = 2) /\
  (forall l : Level, ~ (l << l)).
Proof.
  split; [| split].
  - intro D. split; [exact (exclusive D) | exact (exhaustive D)].
  - intro D. split; [exact (sides_distinct D) | exact (two_distinct_elements D)].
  - exact level_lt_irrefl.
Qed.

(** With the first conjunct (a distinction for EVERY proposition) the price
    is Classical_Prop.classic. *)
Theorem complete_foundation_with_sides :
  (forall P, exists D : Distinction, Distinction.positive D = P) /\
  (forall D, ~ (Distinction.positive D /\ negative D) /\
             (Distinction.positive D \/ negative D)) /\
  (forall D, Distinction.positive D <> negative D /\
             NoDup (err_elements D) /\ length (err_elements D) = 2) /\
  (forall l : Level, ~ (l << l)).
Proof.
  split.
  - intro P. exists (distinction_of P). reflexivity.
  - exact foundation_core_closed.
Qed.

(* ========================================================================= *)
(*  6. THE TYPING JUDGMENT                                                   *)
(* ========================================================================= *)

(** [HasType] does not depend on the system: it is the well-formedness of
    the context (its second conjunct holds of every system by the field
    [crit_level_valid]). *)
Theorem HasType_iff_ctx : forall (L : Level) (G : Context) (S : System L),
  HasType L G S <-> ctx_well_formed G.
Proof.
  intros L G S. unfold HasType. split.
  - intros [H _]. exact H.
  - intro H. split; [exact H | exact (crit_level_valid L (sys_criterion L S))].
Qed.

Corollary HasType_any_system : forall (L : Level) (G : Context) (S T : System L),
  HasType L G S -> HasType L G T.
Proof.
  intros L G S T H. apply (proj2 (HasType_iff_ctx L G T)).
  exact (proj1 (HasType_iff_ctx L G S) H).
Qed.

(** The conclusion of [p1_check] holds with no premise. *)
Theorem p1_check_without_premise : forall (L : Level) (S : System L),
  crit_level_witness L (sys_criterion L S) << L.
Proof. intros L S. exact (crit_level_valid L (sys_criterion L S)). Qed.

(** The conclusions of [l4_role_principle] and [p1_check] coincide by
    definition. *)
Theorem l4_role_principle_is_p1_check : forall (L : Level) (S : System L),
  P2_valid L (sys_criterion L S) =
  (crit_level_witness L (sys_criterion L S) << L).
Proof. reflexivity. Qed.

(** The conclusion of [wf4_check] coincides with its premise by definition. *)
Theorem wf4_check_is_identity : forall (L : Level) (G : Context) (S : System L),
  HasType L G S =
  (ctx_well_formed G /\ crit_level_witness L (sys_criterion L S) << L).
Proof. reflexivity. Qed.
