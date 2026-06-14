(** * ERRCoequalizer.v — coequalizers and finite cocompleteness of the E/R/R category.

    Dual to ERREqualizer.v.  The coequalizer of f,g : S1 ⇉ S2 is the quotient of S2 by the SMALLEST
    congruence forcing f x ~ g x (and containing S2's Roles).  Built as an inductive closure
    (gen_cong) + the quotient (ERRQuotient).  With initial + coproducts + coequalizers, the category
    is FINITELY COCOMPLETE.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the coequalizer COARSENS S2's Roles to the smallest congruence that forces f x ~ g x and
      contains S2's Roles — defined as an inductive reflexive/symmetric/transitive closure (gen_cong).
    Roles (L4): the quotient morphism identifies f x and g x AT THE ROLES TIER (get_Roles
      (coequalizer)(f x)(g x)); the merge happens in Roles, not Elements.
    Elements (L1+P4): the carrier is UNCHANGED (= get_Elements S2); f x and g x stay distinct
      ELEMENTS — they only become Roles-related.  The carrier-merge (making them equal elements) is
      NOT performed.
    P4 diagnostic (could it be otherwise?):
      merging into equivalence-CLASSES as new elements is the role-limit / quotient-type act (the
      wall); ToS does the Roles-merge (0-axiom).  The Roles-merge is forced (smallest congruence);
      the carrier-merge is the wall.
    Honesty wall — the DUAL ASYMMETRY (mirrors H1):
      the coequalizer has FULL mediator uniqueness 0-axiom (same carrier, no proof-irrelevance) —
      BETTER than the equalizer (subobject-uniqueness only, PI wall).  But it is the "weaker" colimit:
      the carrier is NOT merged (the true colimit = quotient-type wall, decidable-dissolvable via
      CanonRepr, cf ERRFiniteQuotient).  Carve-a-sub-carrier (Element-side, concrete) vs merge-into-
      classes (role-limit, walled) = the finitization signature again.  The co-mediator needs the
      TARGET to be an equivalence-system (the gate, dual to the equalizer needing S1 restriction-
      stable).  Finite cocompleteness = initial (ERRTerminalInitial) + coproducts (ERRCoproduct) +
      coequalizers (here).  Reuses fs_quotient / fs_quot_mediator (ERRQuotient).  0 axioms.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* err_comp, err_map, err_pres, err_morph_eq *)
From ToS Require Import foundation.ERRQuotient.        (* congruence, fs_quotient, fs_quot, fs_quot_mediator, fs_quot_factor, fs_quot_factor_unique, SDisc *)
From ToS Require Import foundation.ERR2Category.       (* roles_equiv *)
From ToS Require Import foundation.ERRCoproduct.       (* fs_coproduct, fs_inl, fs_inr — for the pushout *)
From ToS Require Import foundation.ERRFirstIso.        (* fconst — concrete witness *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  The generated congruence                                               *)
(* ===================================================================== *)

(** The SMALLEST congruence on S2 forcing f x ~ g x and containing S2's Roles. *)
Inductive gen_cong {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  : get_Elements S2 -> get_Elements S2 -> Prop :=
  | gc_roles : forall a b, get_Roles S2 a b -> gen_cong f g a b
  | gc_gen   : forall x, gen_cong f g (err_map f x) (err_map g x)
  | gc_refl  : forall a, gen_cong f g a a
  | gc_sym   : forall a b, gen_cong f g a b -> gen_cong f g b a
  | gc_trans : forall a b c, gen_cong f g a b -> gen_cong f g b c -> gen_cong f g a c.

(** ★ It is a congruence (an equivalence containing the Roles). *)
Lemma gen_cong_congruence {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2) :
  congruence S2 (gen_cong f g).
Proof.
  split.
  - split; [ | split ].
    + intro a. apply gc_refl.
    + intros a b H. apply gc_sym. exact H.
    + intros a b c Hab Hbc. exact (gc_trans f g a b c Hab Hbc).
  - intros a b H. apply gc_roles. exact H.
Qed.

(* ===================================================================== *)
(*  The coequalizer object and the coequalizing morphism                   *)
(* ===================================================================== *)

(** ★★ The COEQUALIZER of f,g : S1 ⇉ S2 = S2 with its Roles coarsened to the generated congruence. *)
Definition fs_coequalizer {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  : FunctionalSystem L :=
  fs_quotient S2 (gen_cong f g) (gen_cong_congruence f g).

(** Its Roles are exactly the generated congruence. *)
Lemma fs_coequalizer_roles {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2) :
  get_Roles (fs_coequalizer f g) = gen_cong f g.
Proof. reflexivity. Qed.

(** The coequalizing morphism (the quotient map S2 → coequalizer). *)
Definition coeq_quot {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  : ERRMorphism S2 (fs_coequalizer f g) :=
  fs_quot S2 (gen_cong f g) (gen_cong_congruence f g).

(** ★ The coequalizing morphism COEQUALIZES f and g: in the coequalizer, q;f and q;g are
    Roles-related at every point (f x and g x are identified up to Roles). *)
Lemma coeq_coequalizes {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2) :
  forall x, get_Roles (fs_coequalizer f g)
              (err_map (err_comp f (coeq_quot f g)) x) (err_map (err_comp g (coeq_quot f g)) x).
Proof. intro x. exact (gc_gen f g x). Qed.

(* ===================================================================== *)
(*  The co-universal property                                              *)
(* ===================================================================== *)

(** A coequalizing morphism h respects the whole generated congruence (the target must be an
    equivalence-system for the closure cases). *)
Lemma gen_cong_respects {L} {S1 S2 T : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  (h : ERRMorphism S2 T) (HT : roles_equiv T)
  (Hcoeq : forall x, get_Roles T (err_map h (err_map f x)) (err_map h (err_map g x))) :
  forall a b, gen_cong f g a b -> get_Roles T (err_map h a) (err_map h b).
Proof.
  intros a b Hab.
  induction Hab as [a0 b0 Hr | x0 | a0 | a0 b0 Hab0 IH | a0 b0 c0 Hab1 IH1 Hab2 IH2].
  - exact (err_pres h a0 b0 Hr).
  - exact (Hcoeq x0).
  - exact (proj1 HT (err_map h a0)).
  - exact (proj1 (proj2 HT) (err_map h a0) (err_map h b0) IH).
  - exact (proj2 (proj2 HT) (err_map h a0) (err_map h b0) (err_map h c0) IH1 IH2).
Qed.

(** The CO-MEDIATOR: any coequalizing h : S2 → T factors through the coequalizer. *)
Definition coeq_mediator {L} {S1 S2 T : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  (h : ERRMorphism S2 T) (HT : roles_equiv T)
  (Hcoeq : forall x, get_Roles T (err_map h (err_map f x)) (err_map h (err_map g x)))
  : ERRMorphism (fs_coequalizer f g) T :=
  fs_quot_mediator (gen_cong f g) (gen_cong_congruence f g) h (gen_cong_respects f g h HT Hcoeq).

(** ★ The co-mediator factors h:  q ; mediator = h. *)
Lemma coeq_mediator_factors {L} {S1 S2 T : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  (h : ERRMorphism S2 T) (HT : roles_equiv T)
  (Hcoeq : forall x, get_Roles T (err_map h (err_map f x)) (err_map h (err_map g x))) :
  err_morph_eq (err_comp (coeq_quot f g) (coeq_mediator f g h HT Hcoeq)) h.
Proof. apply fs_quot_factor. Qed.

(** ★★ FULL uniqueness of the co-mediator — 0-axiom (the carrier is unchanged, so no proof-
    irrelevance is needed; this is STRICTLY better than the equalizer's subobject-uniqueness). *)
Lemma coeq_mediator_unique {L} {S1 S2 T : FunctionalSystem L} (f g : ERRMorphism S1 S2)
  (h : ERRMorphism S2 T) (HT : roles_equiv T)
  (Hcoeq : forall x, get_Roles T (err_map h (err_map f x)) (err_map h (err_map g x)))
  (u : ERRMorphism (fs_coequalizer f g) T) :
  err_morph_eq (err_comp (coeq_quot f g) u) h ->
  err_morph_eq u (coeq_mediator f g h HT Hcoeq).
Proof. intro Hu. exact (fs_quot_factor_unique (gen_cong f g) (gen_cong_congruence f g) h (gen_cong_respects f g h HT Hcoeq) u Hu). Qed.

(* ===================================================================== *)
(*  Pushouts: coproducts + coequalizers give pushouts (cocompleteness)      *)
(* ===================================================================== *)

Section Pushout.
  Context {L} {A B C : FunctionalSystem L}.
  Context (HB : fs_constitution B = EquivalenceConstitution)
          (HC : fs_constitution C = EquivalenceConstitution).
  Context (f : ERRMorphism A B) (g : ERRMorphism A C).

  (** The pushout of f,g under A = the coequalizer of (f ; inl) and (g ; inr) into B + C. *)
  Definition po_f : ERRMorphism A (fs_coproduct B C HB HC) := err_comp f (fs_inl B C HB HC).
  Definition po_g : ERRMorphism A (fs_coproduct B C HB HC) := err_comp g (fs_inr B C HB HC).
  Definition fs_pushout := fs_coequalizer po_f po_g.
  Definition po_quot := coeq_quot po_f po_g.

  (** ★ The pushout square cocommutes: the two paths B → pushout and C → pushout (through A) agree
      up to Roles. *)
  Lemma fs_pushout_cocommutes :
    forall x, get_Roles fs_pushout
                (err_map (err_comp po_f po_quot) x) (err_map (err_comp po_g po_quot) x).
  Proof. exact (coeq_coequalizes po_f po_g). Qed.
End Pushout.

(* ===================================================================== *)
(*  Concrete grounding                                                     *)
(* ===================================================================== *)

(** The coequalizer of the identity and the constant-true map on the discrete bool system
    IDENTIFIES false and true (up to Roles) — the dual of the equalizer carving {true}. *)
Lemma coeq_concrete : get_Roles (fs_coequalizer (err_id SDisc) fconst) false true.
Proof. exact (gc_gen (err_id SDisc) fconst false). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE E/R/R CATEGORY HAS COEQUALIZERS — hence (with the initial object and coproducts) it is
    FINITELY COCOMPLETE.
      (coequalizes)  the quotient morphism identifies f x and g x up to Roles;
      (factors)      every coequalizing morphism factors through the coequalizer;
      (unique)       the co-mediator is FULLY unique (0-axiom — strictly better than the equalizer).
    The pushout (fs_pushout) is the coequalizer of the coproduct legs — coproducts + coequalizers
    give all finite colimits.  Honest: the carrier is not merged (true colimit = quotient-type wall);
    the co-mediator needs the target to be an equivalence-system. *)
Theorem err_coequalizer :
  (forall (L : Level) (S1 S2 : FunctionalSystem L) (f g : ERRMorphism S1 S2),
     forall x, get_Roles (fs_coequalizer f g)
                 (err_map (err_comp f (coeq_quot f g)) x) (err_map (err_comp g (coeq_quot f g)) x))
  /\ (forall (L : Level) (S1 S2 T : FunctionalSystem L) (f g : ERRMorphism S1 S2)
        (h : ERRMorphism S2 T) (HT : roles_equiv T)
        (Hcoeq : forall x, get_Roles T (err_map h (err_map f x)) (err_map h (err_map g x))),
        err_morph_eq (err_comp (coeq_quot f g) (coeq_mediator f g h HT Hcoeq)) h)
  /\ (forall (L : Level) (S1 S2 T : FunctionalSystem L) (f g : ERRMorphism S1 S2)
        (h : ERRMorphism S2 T) (HT : roles_equiv T)
        (Hcoeq : forall x, get_Roles T (err_map h (err_map f x)) (err_map h (err_map g x)))
        (u : ERRMorphism (fs_coequalizer f g) T),
        err_morph_eq (err_comp (coeq_quot f g) u) h ->
        err_morph_eq u (coeq_mediator f g h HT Hcoeq)).
Proof.
  split; [ | split ].
  - intros L S1 S2 f g. exact (coeq_coequalizes f g).
  - intros L S1 S2 T f g h HT Hcoeq. exact (coeq_mediator_factors f g h HT Hcoeq).
  - intros L S1 S2 T f g h HT Hcoeq u Hu. exact (coeq_mediator_unique f g h HT Hcoeq u Hu).
Qed.

Print Assumptions err_coequalizer.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Coequalizers + finite cocompleteness (dual to ERREqualizer).  gen_cong    *)
(*  (inductive smallest congruence forcing f x ~ g x) + gen_cong_congruence.  *)
(*  fs_coequalizer (= quotient of S2 by gen_cong) + fs_coequalizer_roles.     *)
(*  coeq_quot (coequalizing morphism) + coeq_coequalizes.  gen_cong_respects  *)
(*  (a coequalizing h respects the congruence) + coeq_mediator + coeq_        *)
(*  mediator_factors + coeq_mediator_unique (FULL uniqueness, 0-axiom).        *)
(*  Pushout section: fs_pushout (= coequalizer of the coproduct legs) +        *)
(*  fs_pushout_cocommutes.  coeq_concrete (id and const-true on SDisc identify *)
(*  false~true).  Capstone err_coequalizer.  With initial + coproducts, the    *)
(*  category is finitely cocomplete.  HONEST: carrier not merged (quotient-    *)
(*  type wall); co-mediator needs an equivalence target.  DUAL ASYMMETRY:      *)
(*  full uniqueness here vs subobject-only for the equalizer (= H1 signature). *)
(* ========================================================================= *)
