(** * ERRQuotient.v — thread ④: QUOTIENT systems, the DUAL of sub-systems.  A sub-system REFINES (a
      subset, embedded by a mono — ERRDynamicsInvariant.restrict); a quotient COARSENS the Roles by a
      congruence (an equivalence ⊇ the Roles), forgetting distinctions, and is surjected onto by an epi.

      ★ congruence S E — an equivalence E on the Elements that CONTAINS the Roles (so the quotient map
        is a morphism).  fs_quotient S E — same carrier, Roles COARSENED to E, Rules = Equivalence.
      ★ The quotient morphism fs_quot : S → S/E is SURJECTIVE (an epi) — fs_quot_surjective.
      ★ CO-UNIVERSAL PROPERTY (dual to the product/coproduct mediator): any g : S → T that RESPECTS the
        congruence (E-related ↦ T-related) factors UNIQUELY through the quotient (fs_quot_factor,
        fs_quot_factor_unique).
      ★ A quotient FORGETS distinctions: two P4-distinct elements (true ≠ false) become related in the
        quotient (quotient_collapses) — the dual of a sub-system, which adds distinctions/constraints.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      a QUOTIENT coarsens the Roles by a congruence (equivalence ⊇ Roles); the quotient map is an EPI
      (surjective); a congruence-respecting morphism factors UNIQUELY through it (co-universal); this is
      the DUAL of a sub-system (a mono that refines).
    Roles (L4): congruence (the coarsening relation); fs_quotient; fs_quot (the epi); fs_quot_mediator
      (the co-mediator).
    Elements (L1+P4): the states (the carrier is UNCHANGED); the congruence; the systems.
    P4 diagnostic (could it be otherwise?):
      a quotient FORGETS distinctions — two P4-distinct elements become related; WHICH congruence is a
      free choice (finer or coarser).  The carrier's actuality is untouched; only the relating coarsens.
    Honesty wall:
      QUOTIENT here = coarsening the Roles (SAME carrier), NOT a carrier quotient-TYPE (those need a
      quotient axiom — avoided to stay 0-axiom); the congruence must CONTAIN the Roles (so the quotient
      map is a morphism) and be an equivalence (so S/E is a FunctionalSystem); the co-universal property
      is at the Elements-map level (dual to ERRProductUniversal / ERRCoproduct).  The dual sub-system is
      ERRDynamicsInvariant.restrict.  Reuses ERRComposition.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, mkERRMorphism, err_map, err_comp, err_morph_eq *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(** A function is SURJECTIVE if it hits every target (an epi witness). *)
Definition surjective {A B : Type} (f : A -> B) : Prop := forall y, exists x, f x = y.

(* ===================================================================== *)
(*  CONGRUENCE and the QUOTIENT system                                     *)
(* ===================================================================== *)

(** A CONGRUENCE on S: an equivalence on the Elements that CONTAINS the Roles. *)
Definition congruence {L} (S : FunctionalSystem L) (E : get_Elements S -> get_Elements S -> Prop) : Prop :=
  EquivalenceConstitution (get_Elements S) E /\ (forall x y, get_Roles S x y -> E x y).

(** ★★ THE QUOTIENT S/E: the same carrier, Roles COARSENED to E, Rules = EquivalenceConstitution. *)
Definition fs_quotient {L} (S : FunctionalSystem L)
  (E : get_Elements S -> get_Elements S -> Prop) (HE : congruence S E) : FunctionalSystem L.
Proof.
  refine {| fs_constitution := EquivalenceConstitution;
            fs_domain := get_Elements S;
            fs_relations := E;
            fs_functional := _;
            fs_element_level := fun x => fs_element_level S x;
            fs_level_valid := fun x => fs_level_valid S x |}.
  exact (proj1 HE).
Defined.

(** ★ The carrier is preserved. *)
Lemma fs_quotient_elements : forall {L} (S : FunctionalSystem L) E HE,
  get_Elements (fs_quotient S E HE) = get_Elements S.
Proof. intros. reflexivity. Qed.

(** ★ The Roles are the congruence (coarsened). *)
Lemma fs_quotient_roles : forall {L} (S : FunctionalSystem L) E HE,
  get_Roles (fs_quotient S E HE) = E.
Proof. intros. reflexivity. Qed.

(* ===================================================================== *)
(*  THE QUOTIENT MORPHISM (an epi)                                         *)
(* ===================================================================== *)

(** The quotient morphism S → S/E: identity on Elements, sending Roles into the congruence. *)
Definition fs_quot {L} (S : FunctionalSystem L)
  (E : get_Elements S -> get_Elements S -> Prop) (HE : congruence S E)
  : ERRMorphism S (fs_quotient S E HE).
Proof.
  refine (@mkERRMorphism L S (fs_quotient S E HE) (fun x => x) _).
  intros x y H. exact (proj2 HE x y H).
Defined.

(** ★★ The quotient morphism is SURJECTIVE (an epi). *)
Lemma fs_quot_surjective : forall {L} (S : FunctionalSystem L) E HE,
  surjective (err_map (fs_quot S E HE)).
Proof. intros L S E HE y. exists y. reflexivity. Qed.

(* ===================================================================== *)
(*  CO-UNIVERSAL PROPERTY                                                   *)
(* ===================================================================== *)

(** The co-mediator: a congruence-respecting g : S → T descends to S/E → T. *)
Definition fs_quot_mediator {L} {S T : FunctionalSystem L}
  (E : get_Elements S -> get_Elements S -> Prop) (HE : congruence S E)
  (g : ERRMorphism S T)
  (Hresp : forall x y, E x y -> get_Roles T (err_map g x) (err_map g y))
  : ERRMorphism (fs_quotient S E HE) T.
Proof.
  refine (@mkERRMorphism L (fs_quotient S E HE) T (err_map g) _).
  intros x y H. exact (Hresp x y H).
Defined.

(** ★★ The co-mediator factors g through the quotient: mediator ∘ quot = g. *)
Lemma fs_quot_factor : forall {L} {S T : FunctionalSystem L} E HE
  (g : ERRMorphism S T) Hresp,
  err_morph_eq (err_comp (fs_quot S E HE) (fs_quot_mediator E HE g Hresp)) g.
Proof. intros L S T E HE g Hresp x. reflexivity. Qed.

(** ★★ UNIQUENESS of the co-mediator: any h with h ∘ quot = g equals the mediator. *)
Lemma fs_quot_factor_unique : forall {L} {S T : FunctionalSystem L} E HE
  (g : ERRMorphism S T) Hresp (h : ERRMorphism (fs_quotient S E HE) T),
  err_morph_eq (err_comp (fs_quot S E HE) h) g ->
  err_morph_eq h (fs_quot_mediator E HE g Hresp).
Proof. intros L S T E HE g Hresp h Hh x. exact (Hh x). Qed.

(* ===================================================================== *)
(*  A QUOTIENT FORGETS DISTINCTIONS (the dual of a sub-system)             *)
(* ===================================================================== *)

(** A discrete bool-system (Roles = equality). *)
Definition SDisc : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := bool;
            fs_relations := @eq bool; fs_functional := _;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => L1_lt_L2 |}.
  unfold EquivalenceConstitution. split; [ | split ].
  - intro x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z Hxy Hyz. transitivity y; assumption.
Defined.

(** The full relation: identifies everything (a congruence containing eq). *)
Definition Efull : get_Elements SDisc -> get_Elements SDisc -> Prop := fun _ _ => True.

Lemma Efull_congruence : congruence SDisc Efull.
Proof.
  split.
  - unfold EquivalenceConstitution. split; [ | split ]; intros; exact I.
  - intros x y _. exact I.
Qed.

(** ★★ The quotient FORGETS the distinction: true ≠ false, yet they are related in SDisc/Efull. *)
Lemma quotient_collapses :
  (true <> false) /\ get_Roles (fs_quotient SDisc Efull Efull_congruence) true false.
Proof. split; [ discriminate | exact I ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE QUOTIENT (dual of the sub-system):
      (epi)          the quotient morphism S → S/E is surjective;
      (triad)        the carrier is kept, the Roles coarsened to the congruence E;
      (co-universal) a congruence-respecting g factors UNIQUELY through the quotient;
      (forgets)      a quotient collapses distinctions (true ≠ false become related).
    A quotient coarsens the Roles by a congruence and is surjected onto by an epi — the exact dual of a
    sub-system, which refines via a mono. *)
Theorem err_quotient :
  (forall (L : Level) (S : FunctionalSystem L) E HE, surjective (err_map (fs_quot S E HE)))
  /\ (forall (L : Level) (S : FunctionalSystem L) E HE,
        get_Elements (fs_quotient S E HE) = get_Elements S
        /\ get_Roles (fs_quotient S E HE) = E)
  /\ (forall (L : Level) (S T : FunctionalSystem L) E HE (g : ERRMorphism S T) Hresp,
        err_morph_eq (err_comp (fs_quot S E HE) (fs_quot_mediator E HE g Hresp)) g
        /\ (forall (h : ERRMorphism (fs_quotient S E HE) T),
              err_morph_eq (err_comp (fs_quot S E HE) h) g ->
              err_morph_eq h (fs_quot_mediator E HE g Hresp)))
  /\ ((true <> false) /\ get_Roles (fs_quotient SDisc Efull Efull_congruence) true false).
Proof.
  split; [ exact @fs_quot_surjective | ].
  split; [ intros L S E HE; split; reflexivity | ].
  split.
  - intros L S T E HE g Hresp.
    split; [ exact (fs_quot_factor E HE g Hresp) | exact (fs_quot_factor_unique E HE g Hresp) ].
  - exact quotient_collapses.
Qed.

Print Assumptions err_quotient.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Thread ④: QUOTIENT systems = dual of sub-systems.  congruence (equivalence *)
(*  ⊇ Roles); fs_quotient (same carrier, Roles coarsened to E, Rules = Equiv): *)
(*  fs_quotient_elements/roles.  fs_quot (the quotient morphism) +             *)
(*  fs_quot_surjective (an EPI).  CO-UNIVERSAL: fs_quot_mediator +             *)
(*  fs_quot_factor (mediator ∘ quot = g) + fs_quot_factor_unique.  FORGETS:    *)
(*  SDisc/Efull collapses true≠false into a related pair (quotient_collapses) — *)
(*  dual of a sub-system, which adds distinctions.  Capstone err_quotient.     *)
(*  HONEST: coarsen-Roles, NOT a carrier quotient-type (avoids the quotient    *)
(*  axiom); congruence ⊇ Roles + equivalence; co-universal at the map level;   *)
(*  dual sub-system = ERRDynamicsInvariant.restrict.                          *)
(* ========================================================================= *)
