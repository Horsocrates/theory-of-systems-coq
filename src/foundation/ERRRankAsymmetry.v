(** * ERRRankAsymmetry.v — Кирпич 1 развития ядра Теории Систем: the RANK ASYMMETRY
      Rules > Roles > Elements made a THEOREM on the canonical E/R/R object FunctionalSystem.

    The E/R/R paper (docs/ERR_FRAMEWORK.md, Preprint/Article_ERR_Addendum, Jan 2026) ASSERTS, as
    prose, the rank asymmetry "Rules > Roles > Elements" (L5) and "Rules are primary — they justify
    and constrain the Roles" (L4).  Since Jan 2026 the E/R/R core was BUILT ON but never DEVELOPED
    from within; this file is the first brick of that development.  It turns the prose claim into
    machine-checked theorems on FunctionalSystem (Core_ERR §XVII: fs_constitution=Rules,
    fs_domain=Elements, fs_relations=Roles), pivoting on the single point where the three aspects
    INTERACT — the field fs_functional : fs_constitution fs_domain fs_relations.

    What is genuinely proved (NOT a restatement of fs_functional, which only ever witnesses "yes"
    for a given system):

      ★ RULES FILTER (non-vacuous) — a constitution can say NO to a (Elements, Roles) pair:
        EquivalenceConstitution rejects a non-reflexive relation (rules_filter_nonvacuous).
      ★ (ELEMENTS, ROLES) UNDERDETERMINE RULES — the asymmetry, made CONCRETE at the system level:
        two genuine FunctionalSystems (BoolEqTrivial, BoolEqEquiv) with the SAME Elements (bool) and
        the SAME Roles (eq) but DIFFERENT Rules (same_elements + same_roles + different_rules).
      ★ RULES ARE THE GATE (L4 primacy) — in ANY FunctionalSystem the Rules hold on its own
        (Elements, Roles): get_Rules S is inhabited by fs_functional (rules_are_the_gate); combined
        with "filter non-vacuous", the existence of a system is a genuine constraint, not automatic.
      ★ ELEMENTS UNDERDETERMINE ROLES — a domain admits distinct relations
        (elements_underdetermine_roles): the lower link of the chain.

    Together: each lower tier underdetermines the tier above, and each upper tier filters the lower —
    the rank asymmetry Rules → Roles → Elements, machine-checked.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) a Rule is a NON-VACUOUS filter on (Roles over Elements) — it can reject a pair;
      (2) (Elements, Roles) do NOT fix the Rules — one pair passes >=2 distinct Rules (two systems);
      (3) a Rule is the GATE (L4): a system exists only if its Rules hold on its (Elements, Roles);
      (4) Elements do NOT fix the Roles — a domain admits distinct relations.
    Roles (L4): fs_constitution = the gate/filter; fs_relations = the organizing layer over the
      domain; fs_domain = the substrate; fs_functional = the discharge point (Rules applied to E,R).
    Elements (L1+P4): the constitutions (Trivial/Equivalence); the domain bool; the relations
      eq/both_true; the two systems BoolEqTrivial/BoolEqEquiv.
    P4 diagnostic (could it be otherwise?):
      The asymmetry is STRUCTURAL — it lives in the TYPES of the FunctionalSystem record (Elements:
      Type; Roles : E->E->Prop depends on Elements; Rules : forall D,(D->D->Prop)->Prop depends on
      both).  This file does not DERIVE the record; it proves the CONSEQUENCES of the asymmetry the
      paper asserts: the filter is non-vacuous, the lower underdetermines the upper, the gate always
      holds.
    Honesty wall:
      NOT a re-description of fs_functional (which only says "yes" for a given system).  The new
      content: (a) the filter can say "no"; (b) (Elements, Roles) underdetermine Rules — TWO concrete
      systems; (c) Elements underdetermine Roles.  "Roles organize Elements" is given here as
      DEPENDENCY + underdetermination, NOT as an organization operator (that is Кирпич 2 —
      composition).  Built on FunctionalSystem (the canonical E/R/R object per the paper); the
      indexed System L (criterion line) is legacy and not used.  0 axioms (classic sits in Core_ERR's
      context but these theorems do not touch it — Print Assumptions confirms).

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
(* Constitution, TrivialConstitution, EquivalenceConstitution, FunctionalSystem, get_Elements/
   get_Roles/get_Rules, fs_constitution/domain/relations/functional, Level, L1, L2, L1_lt_L2 *)

(* The {L} implicit on the record projections is section-local in Core_ERR; restore it here so
   fs_constitution / fs_functional take the level implicitly (as get_Elements/get_Roles do). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.

(* ===================================================================== *)
(*  PART I — RULES FILTER: a constitution can say NO (non-vacuous)         *)
(* ===================================================================== *)

(** A non-reflexive relation on bool: "both sides are true" — fails reflexivity at false. *)
Definition both_true (x y : bool) : Prop := x = true /\ y = true.

(** EquivalenceConstitution REJECTS both_true (it is not reflexive at false). *)
Lemma rules_can_reject : ~ EquivalenceConstitution bool both_true.
Proof.
  intros [Hrefl _]. specialize (Hrefl false). destruct Hrefl as [Hf _]. discriminate.
Qed.

(** ★ RULES ARE A NON-VACUOUS FILTER: some constitution rejects some (Elements, Roles) pair.
    (fs_functional only ever witnesses acceptance; here the filter genuinely excludes.) *)
Theorem rules_filter_nonvacuous :
  exists (C : Constitution) (D : Type) (R : D -> D -> Prop), ~ C D R.
Proof. exists EquivalenceConstitution, bool, both_true. exact rules_can_reject. Qed.

(* ===================================================================== *)
(*  PART II — (ELEMENTS, ROLES) UNDERDETERMINE RULES: two concrete systems  *)
(* ===================================================================== *)

Lemma trivial_accepts_eq : TrivialConstitution bool (@eq bool).
Proof. exact I. Qed.

Lemma equiv_accepts_eq : EquivalenceConstitution bool (@eq bool).
Proof.
  split; [ | split ].
  - intro x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z H1 H2. transitivity y; assumption.
Qed.

(** Same Elements (bool), same Roles (eq), but RULES = TrivialConstitution. *)
Definition BoolEqTrivial : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool; fs_relations := (@eq bool);
            fs_functional := I; fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** Same Elements (bool), same Roles (eq), but RULES = EquivalenceConstitution. *)
Definition BoolEqEquiv : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := bool; fs_relations := (@eq bool);
            fs_functional := _; fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  - exact equiv_accepts_eq.
  - exact L1_lt_L2.
Defined.

(** ★ Same Elements. *)
Lemma same_elements : get_Elements BoolEqTrivial = get_Elements BoolEqEquiv.
Proof. reflexivity. Qed.

(** ★ Same Roles. *)
Lemma same_roles : get_Roles BoolEqTrivial = get_Roles BoolEqEquiv.
Proof. reflexivity. Qed.

(** ★★ DIFFERENT Rules: the two constitutions differ (they disagree on both_true).  So the same
    (Elements, Roles) carries two distinct Rules — Rules are NOT fixed by the lower tier. *)
Lemma different_rules : fs_constitution BoolEqTrivial <> fs_constitution BoolEqEquiv.
Proof.
  intro H. apply rules_can_reject.
  change (fs_constitution BoolEqEquiv bool both_true).
  rewrite <- H. exact I.
Qed.

(* ===================================================================== *)
(*  PART III — RULES ARE THE GATE (L4 primacy)                             *)
(* ===================================================================== *)

(** ★ In ANY FunctionalSystem the Rules HOLD on its own (Elements, Roles): get_Rules is inhabited by
    fs_functional.  A system exists only because its Rules are satisfied — the L4 "Rules are primary"
    reading.  (Non-trivial because the gate can reject, PART I.) *)
Theorem rules_are_the_gate : forall (L : Level) (S : FunctionalSystem L), get_Rules S.
Proof. intros L S. unfold get_Rules. exact (fs_functional S). Qed.

(* ===================================================================== *)
(*  PART IV — ELEMENTS UNDERDETERMINE ROLES (the lower link)               *)
(* ===================================================================== *)

(** ★ A domain admits DISTINCT relations: Elements do not fix the Roles. *)
Theorem elements_underdetermine_roles :
  exists (D : Type) (R1 R2 : D -> D -> Prop), R1 <> R2.
Proof.
  exists bool, (@eq bool), both_true. intro H.
  assert (Hff : both_true false false).
  { pose proof (f_equal (fun R => R false false) H) as E. rewrite <- E. reflexivity. }
  destruct Hff as [Hf _]. discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the rank asymmetry Rules -> Roles -> Elements              *)
(* ===================================================================== *)

(** ★★★ RANK ASYMMETRY, machine-checked on FunctionalSystem:
      (filter)        a Rule can reject a (Elements, Roles) pair — non-vacuous;
      (under-Rules)   one (Elements, Roles) carries two distinct Rules — lower does not fix upper;
      (gate, L4)      any system's Rules hold on its own (Elements, Roles);
      (under-Roles)   a domain admits distinct relations — Elements do not fix Roles.
    Each lower tier underdetermines the upper; each upper tier filters the lower.  The paper's prose
    "Rules > Roles > Elements" is now a theorem (structural asymmetry; consequences proved). *)
Theorem err_rank_asymmetry :
  (exists (C : Constitution) (D : Type) (R : D -> D -> Prop), ~ C D R)
  /\ (get_Elements BoolEqTrivial = get_Elements BoolEqEquiv
      /\ get_Roles BoolEqTrivial = get_Roles BoolEqEquiv
      /\ fs_constitution BoolEqTrivial <> fs_constitution BoolEqEquiv)
  /\ (forall (L : Level) (S : FunctionalSystem L), get_Rules S)
  /\ (exists (D : Type) (R1 R2 : D -> D -> Prop), R1 <> R2).
Proof.
  split; [ exact rules_filter_nonvacuous | ].
  split; [ split; [ exact same_elements | split; [ exact same_roles | exact different_rules ] ] | ].
  split; [ exact rules_are_the_gate | exact elements_underdetermine_roles ].
Qed.

Print Assumptions err_rank_asymmetry.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  10 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Кирпич 1 of developing the ToS core from within: the rank asymmetry       *)
(*  Rules > Roles > Elements (paper prose, L4/L5) made a THEOREM on           *)
(*  FunctionalSystem.  Rules are a non-vacuous filter (rules_filter_nonvacuous);*)
(*  (Elements,Roles) underdetermine Rules — two concrete systems same E & R,   *)
(*  different Rules (same_elements/same_roles/different_rules); Rules are the   *)
(*  gate (rules_are_the_gate = get_Rules via fs_functional, L4); Elements       *)
(*  underdetermine Roles (elements_underdetermine_roles).  Pivot: fs_functional*)
(*  (the one interaction point).  NOT a restatement of fs_functional — the new  *)
(*  facts are the filter saying "no", the two-system underdetermination, and    *)
(*  the lower link.  Next (Кирпич 2): E/R/R-morphism + composition.            *)
(* ========================================================================= *)
