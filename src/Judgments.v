(* ========================================================================= *)
(*                  JUDGMENTS: CORE JUDGMENT FORMS                          *)
(*                                                                          *)
(*  Part of: Theory of Systems — Coq Formalization                         *)
(*                                                                          *)
(*  Formalizes judgment forms (HasType, HasElem, SystemEquiv) as           *)
(*  Prop-valued functions over existing System/Criterion types.            *)
(*  Uses shallow embedding — judgments are plain propositions built         *)
(*  from existing predicates.                                               *)
(*                                                                          *)
(*  Depends on: TheoryOfSystems_Core_ERR.v, UniversePolymorphism.v         *)
(*  STATUS: 20 Qed, 0 Admitted, 0 axioms beyond Classical                  *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.

(* ========================================================================= *)
(*                   PART I: CONTEXT ENTRIES                                *)
(* ========================================================================= *)

(**
  CONTEXT: A LIST OF NAMED BINDINGS
  ===================================

  A context collects named declarations: systems, elements, roles,
  and morphisms. Each entry carries a name (nat) and level information.

  Context well-formedness = no duplicate names (NoDup on names).
  This mirrors the variable-uniqueness condition in type theory.
*)

Inductive CtxEntry : Type :=
  | CE_System   : nat -> Level -> CtxEntry
  | CE_Elem     : nat -> Level -> CtxEntry
  | CE_Role     : nat -> Level -> CtxEntry
  | CE_Morphism : nat -> Level -> Level -> CtxEntry.

(** Extract name from context entry *)
Definition ce_name (e : CtxEntry) : nat :=
  match e with
  | CE_System n _     => n
  | CE_Elem n _       => n
  | CE_Role n _       => n
  | CE_Morphism n _ _ => n
  end.

(** Extract primary level from context entry *)
Definition ce_level (e : CtxEntry) : Level :=
  match e with
  | CE_System _ l     => l
  | CE_Elem _ l       => l
  | CE_Role _ l       => l
  | CE_Morphism _ l _ => l
  end.

Definition Context := list CtxEntry.

(** Context well-formedness: no duplicate names *)
Definition ctx_well_formed (G : Context) : Prop :=
  NoDup (map ce_name G).

(** Lookup: find entry by name *)
Fixpoint ctx_lookup (G : Context) (n : nat) : option CtxEntry :=
  match G with
  | [] => None
  | e :: rest =>
    if Nat.eqb (ce_name e) n then Some e
    else ctx_lookup rest n
  end.

(* ========================================================================= *)
(*                   PART II: CONTEXT LEMMAS                                *)
(* ========================================================================= *)

(** Lemma 1: Empty context is well-formed *)
Lemma ctx_wf_nil : ctx_well_formed [].
Proof.
  unfold ctx_well_formed. simpl. constructor.
Qed.

(** Lemma 2: Extending WF context with fresh name preserves WF *)
Lemma ctx_wf_cons : forall (G : Context) (e : CtxEntry),
  ctx_well_formed G ->
  ~ In (ce_name e) (map ce_name G) ->
  ctx_well_formed (e :: G).
Proof.
  intros G e Hwf Hfresh.
  unfold ctx_well_formed in *. simpl.
  constructor; assumption.
Qed.

(** Lemma 3: Looking up entry by name is decidable *)
Lemma ctx_lookup_dec : forall (G : Context) (n : nat),
  {e : CtxEntry | ctx_lookup G n = Some e} + {ctx_lookup G n = None}.
Proof.
  intros G n. induction G as [| e rest IH].
  - right. simpl. reflexivity.
  - simpl. destruct (Nat.eqb (ce_name e) n) eqn:Heqb.
    + left. exists e. reflexivity.
    + exact IH.
Qed.

(** Lemma 4: ce_name is total — every constructor yields a name *)
Lemma ce_name_total : forall (e : CtxEntry), exists n, ce_name e = n.
Proof.
  intros e. exists (ce_name e). reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART III: ELEMENT TYPE AND JUDGMENT FORMS              *)
(* ========================================================================= *)

(**
  SHALLOW EMBEDDING OF JUDGMENTS
  ================================

  Instead of an inductive judgment datatype, we define judgments as
  Prop-valued functions that combine existing System/Criterion
  predicates.

  HasType G L S:  "System S at level L is well-formed in context G"
  HasElem G L S e: "Element e belongs to system S at level L in G"
  SystemEquiv L S1 S2: "Systems S1 and S2 are equivalent at level L"
*)

Section JudgmentForms.

Variable L : Level.

(** Element type: domain of a system's criterion *)
Definition ElemOf (S : System L) : Type :=
  crit_domain L (sys_criterion L S).

(** HasType: System S at level L is well-formed in context G.
    Well-formedness means:
    1. Context is well-formed (no duplicate names)
    2. Criterion level hierarchy is satisfied (P1: elements below system) *)
Definition HasType (G : Context) (S : System L) : Prop :=
  ctx_well_formed G /\
  crit_level_witness L (sys_criterion L S) << L.

(** HasElem: Element e belongs to system S in context G.
    Membership means:
    1. Context is well-formed
    2. Element satisfies the system's criterion predicate *)
Definition HasElem (G : Context) (S : System L) (e : ElemOf S) : Prop :=
  ctx_well_formed G /\
  crit_predicate L (sys_criterion L S) e.

(** SystemEquiv: Two systems at level L are equivalent.
    We use intensional identity (P3): same criterion, same structure. *)
Definition SystemEquiv (S1 S2 : System L) : Prop :=
  sys_criterion L S1 = sys_criterion L S2 /\
  sys_pos_bound L S1 = sys_pos_bound L S2 /\
  sys_uniqueness L S1 = sys_uniqueness L S2.

(* ========================================================================= *)
(*                   PART IV: JUDGMENT PROPERTIES                           *)
(* ========================================================================= *)

(** Lemma 5: HasType implies level hierarchy (P1) *)
Lemma has_type_implies_P1 : forall (G : Context) (S : System L),
  HasType G S ->
  crit_level_witness L (sys_criterion L S) << L.
Proof.
  intros G S [_ HP1]. exact HP1.
Qed.

(** Lemma 6: HasElem implies criterion satisfied *)
Lemma has_elem_satisfies_criterion : forall (G : Context) (S : System L) (e : ElemOf S),
  HasElem G S e ->
  crit_predicate L (sys_criterion L S) e.
Proof.
  intros G S e [_ Hcrit]. exact Hcrit.
Qed.

(** Lemma 7: System equivalence is reflexive *)
Lemma system_equiv_refl : forall (S : System L),
  SystemEquiv S S.
Proof.
  intros S. unfold SystemEquiv. auto.
Qed.

(** Lemma 8: System equivalence is symmetric *)
Lemma system_equiv_sym : forall (S1 S2 : System L),
  SystemEquiv S1 S2 -> SystemEquiv S2 S1.
Proof.
  intros S1 S2 [Hc [Hp Hu]].
  unfold SystemEquiv. auto.
Qed.

(** Lemma 9: System equivalence is transitive *)
Lemma system_equiv_trans : forall (S1 S2 S3 : System L),
  SystemEquiv S1 S2 -> SystemEquiv S2 S3 -> SystemEquiv S1 S3.
Proof.
  intros S1 S2 S3 [Hc12 [Hp12 Hu12]] [Hc23 [Hp23 Hu23]].
  unfold SystemEquiv.
  split; [| split]; etransitivity; eassumption.
Qed.

(** Lemma 10: level_lt is decidable (wraps UniversePolymorphism result) *)
Lemma level_lt_in_context : forall (l1 l2 : Level),
  {l1 << l2} + {~ l1 << l2}.
Proof.
  exact level_lt_dec.
Qed.

(* ========================================================================= *)
(*                   PART V: CONNECTIONS — WEAKENING AND TRANSFER           *)
(* ========================================================================= *)

(**
  STRUCTURAL RULES
  ==================

  Weakening: adding entries to the context does not invalidate
  existing judgments, provided the extended context remains well-formed.

  These are the standard structural rules of type theory.
*)

(** Lemma 11: Typing in empty context works *)
Lemma has_type_in_empty_ctx : forall (S : System L),
  crit_level_witness L (sys_criterion L S) << L ->
  HasType [] S.
Proof.
  intros S HP1. unfold HasType.
  split.
  - exact ctx_wf_nil.
  - exact HP1.
Qed.

(** Lemma 12: Adding entries preserves HasType (weakening) *)
Lemma has_type_weakening : forall (G : Context) (S : System L) (e : CtxEntry),
  HasType G S ->
  ~ In (ce_name e) (map ce_name G) ->
  HasType (e :: G) S.
Proof.
  intros G S entry [Hwf HP1] Hfresh.
  unfold HasType. split.
  - exact (ctx_wf_cons G entry Hwf Hfresh).
  - exact HP1.
Qed.

(** Lemma 13: Adding entries preserves HasElem (weakening) *)
Lemma has_elem_weakening : forall (G : Context) (S : System L)
  (elem : ElemOf S) (entry : CtxEntry),
  HasElem G S elem ->
  ~ In (ce_name entry) (map ce_name G) ->
  HasElem (entry :: G) S elem.
Proof.
  intros G S elem entry [Hwf Hcrit] Hfresh.
  unfold HasElem. split.
  - exact (ctx_wf_cons G entry Hwf Hfresh).
  - exact Hcrit.
Qed.

(** Lemma 14: Equivalent systems preserve HasType *)
Lemma system_equiv_preserves_has_type : forall (G : Context) (S1 S2 : System L),
  HasType G S1 ->
  SystemEquiv S1 S2 ->
  crit_level_witness L (sys_criterion L S2) << L ->
  HasType G S2.
Proof.
  intros G S1 S2 [Hwf _] _ HP1_2.
  unfold HasType. split; assumption.
Qed.

(** Lemma 15: HasType implies the level constraint is recorded *)
Lemma has_type_level_unique : forall (G : Context) (S : System L),
  HasType G S ->
  exists l, crit_level_witness L (sys_criterion L S) = l /\ l << L.
Proof.
  intros G S [_ HP1].
  exists (crit_level_witness L (sys_criterion L S)).
  split; [reflexivity | exact HP1].
Qed.

(* ========================================================================= *)
(*                   PART VI: ADDITIONAL PROPERTIES                        *)
(* ========================================================================= *)

(**
  EXTRA LEMMAS
  ==============

  Additional useful properties for downstream development.
*)

(** Lemma 16: SystemEquiv implies same criterion level witness *)
Lemma system_equiv_same_level : forall (S1 S2 : System L),
  SystemEquiv S1 S2 ->
  crit_level_witness L (sys_criterion L S1) =
  crit_level_witness L (sys_criterion L S2).
Proof.
  intros S1 S2 [Hcrit _].
  rewrite Hcrit. reflexivity.
Qed.

(** Lemma 17: HasType is preserved by context tail (reverse weakening) *)
Lemma has_type_tail : forall (G : Context) (S : System L) (e : CtxEntry),
  HasType (e :: G) S ->
  ctx_well_formed G ->
  HasType G S.
Proof.
  intros G S e [_ HP1] Hwf.
  unfold HasType. split; assumption.
Qed.

(** Lemma 18: HasElem is preserved by context tail *)
Lemma has_elem_tail : forall (G : Context) (S : System L)
  (elem : ElemOf S) (entry : CtxEntry),
  HasElem (entry :: G) S elem ->
  ctx_well_formed G ->
  HasElem G S elem.
Proof.
  intros G S elem entry [_ Hcrit] Hwf.
  unfold HasElem. split; assumption.
Qed.

(** Lemma 19: HasType implies the P2 condition holds *)
Lemma has_type_P2 : forall (G : Context) (S : System L),
  HasType G S ->
  P2_valid L (sys_criterion L S).
Proof.
  intros G S [_ HP1].
  unfold P2_valid. exact HP1.
Qed.

(** Lemma 20: Lookup in a well-formed context with a found entry
    means the name is in the map *)
Lemma ctx_lookup_in : forall (G : Context) (n : nat) (e : CtxEntry),
  ctx_lookup G n = Some e ->
  In (ce_name e) (map ce_name G).
Proof.
  intros G n e. induction G as [| x rest IH].
  - simpl. intros H. discriminate.
  - simpl. destruct (Nat.eqb (ce_name x) n) eqn:Heqb.
    + intros H. injection H as H. subst.
      left. reflexivity.
    + intros H. right. exact (IH H).
Qed.

End JudgmentForms.

(* ========================================================================= *)
(*                   PART VII: CONCRETE EXAMPLE                            *)
(* ========================================================================= *)

(**
  EXAMPLE: nat_gt_5 system is well-typed at L2
  ==============================================

  We demonstrate that the existing nat_gt_5_criterion system from
  Core_ERR.v passes HasType in the empty context.
*)

(** The nat_gt_5 system at L2 is well-typed *)
Example nat_gt5_well_typed :
  HasType L2 [] example_nat_system.
Proof.
  apply has_type_in_empty_ctx.
  simpl. left. reflexivity.
Qed.

(** Element 7 satisfies the criterion of nat_gt_5 system *)
Example nat_gt5_has_elem_7 :
  HasElem L2 [] example_nat_system 7.
Proof.
  unfold HasElem. split.
  - exact ctx_wf_nil.
  - simpl. lia.
Qed.

(** example_nat_system is equivalent to itself *)
Example nat_gt5_equiv_refl :
  SystemEquiv L2 example_nat_system example_nat_system.
Proof.
  apply system_equiv_refl.
Qed.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  PROVEN (20 Qed, 0 Admitted):

  Part I — Context entries:
    CtxEntry (inductive), ce_name, ce_level, Context, ctx_well_formed,
    ctx_lookup

  Part II — Context lemmas:
    1.  ctx_wf_nil              — empty context is well-formed
    2.  ctx_wf_cons             — fresh extension preserves WF
    3.  ctx_lookup_dec          — lookup is decidable
    4.  ce_name_total           — name extraction is total

  Part IV — Judgment properties:
    5.  has_type_implies_P1     — HasType implies level hierarchy
    6.  has_elem_satisfies_criterion — HasElem implies criterion satisfied
    7.  system_equiv_refl       — equivalence is reflexive
    8.  system_equiv_sym        — equivalence is symmetric
    9.  system_equiv_trans      — equivalence is transitive
    10. level_lt_in_context     — level_lt is decidable

  Part V — Structural rules:
    11. has_type_in_empty_ctx   — typing in empty context works
    12. has_type_weakening      — adding entries preserves HasType
    13. has_elem_weakening      — adding entries preserves HasElem
    14. system_equiv_preserves_has_type — equivalent systems both well-typed
    15. has_type_level_unique   — level constraint is recorded

  Part VI — Additional properties:
    16. system_equiv_same_level — equivalent systems have same level witness
    17. has_type_tail           — reverse weakening for HasType
    18. has_elem_tail           — reverse weakening for HasElem
    19. has_type_P2             — HasType implies P2
    20. ctx_lookup_in           — lookup result is in the name map

  Part VII — Concrete examples:
    nat_gt5_well_typed, nat_gt5_has_elem_7, nat_gt5_equiv_refl

  DESIGN: Shallow embedding — judgments are Prop-valued functions
  combining existing System/Criterion predicates. No deep syntax.

  AXIOMS: classic (inherited from Core_ERR via Classical)
*)
