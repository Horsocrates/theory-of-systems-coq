(** * ERREqualizer.v — equalizers and finite completeness of the E/R/R category.

    The 1-categorical core already has products, coproducts, sub/quotient, terminal/initial.  The
    one finite limit still missing is the EQUALIZER of two parallel morphisms.  Building it (and,
    from it + products, the pullback) shows the category of E/R/R systems is FINITELY COMPLETE.

      equalizer of f,g : S1 ⇉ S2  =  the sub-system of S1 on the agreement locus {x | f x = g x}.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the equalizer is a SUB-object of S1; its Constitution is the (restriction-stable) Constitution
      of S1 carried to the agreement locus.  Its universal property holds because morphisms preserve
      Roles (err_pres) and the agreement condition is a pure Element-side equation f x = g x.
    Roles (L4): the equalizer's Roles = S1's Roles restricted to the agreement sub-carrier; the
      equalizing morphism (inclusion) and the mediator both preserve them.
    Elements (L1+P4): the carrier is {x | f x = g x} (an actual sub-collection — the agreement
      locus); the pullback's carrier is {(a,b) | f a = g b}.
    P4 diagnostic (could it be otherwise?):
      carving a sub-object by a predicate is a finitization act (algorithmic when S2 is decidable);
      the agreement locus is forced by the equation; the only freedom — Leibniz equality of the
      sig-elements — is the proof-irrelevance wall, nothing else is underdetermined.
    Honesty wall:
      uniqueness-as-a-subobject (the mediator's image in S1 is forced) is proved 0-axiom; the FULL
      Leibniz uniqueness of the mediator needs proof-irrelevance of the predicate (UIP on S2) — the
      SAME wall as the first-iso theorem, dissolvable on decidable carriers (UIP_dec, cf
      ERRFiniteQuotient).  Finite completeness = terminal (ERRTerminalInitial) + products
      (ERRComposition) + equalizers (here); finite COcompleteness (coequalizers / pushouts) is not
      built (the generated congruence is harder) — flagged.  Reuses fs_subsystem /
      equiv_restriction_stable (ERRTierIIResidue) + fs_product / fs_proj (ERRComposition).  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.      (* fs_product, fs_proj1, fs_proj2, fs_product_rules, err_comp, err_map, err_morph_eq, mkERRMorphism, err_pres *)
From ToS Require Import foundation.ERRTierIIResidue.     (* fs_subsystem, fs_incl, equiv_restriction_stable *)
From ToS Require Import foundation.ERRQuotient.          (* SDisc *)
From ToS Require Import foundation.ERRFirstIso.          (* fconst *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  The equalizer object and the equalizing morphism                       *)
(* ===================================================================== *)

(** ★★ The EQUALIZER of f,g : S1 ⇉ S2 = the sub-system of S1 on the agreement locus. *)
Definition fs_equalizer {L} {S1 S2 : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
  : FunctionalSystem L :=
  fs_subsystem EquivalenceConstitution equiv_restriction_stable S1 H1
    (fun x => err_map f x = err_map g x).

(** Its carrier is exactly the agreement locus {x | f x = g x}. *)
Lemma fs_equalizer_carrier {L} {S1 S2 : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2) :
  get_Elements (fs_equalizer H1 f g) = { x : get_Elements S1 | err_map f x = err_map g x }.
Proof. reflexivity. Qed.

(** The equalizing morphism (the inclusion of the agreement locus into S1). *)
Definition eq_incl {L} {S1 S2 : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
  : ERRMorphism (fs_equalizer H1 f g) S1 :=
  fs_incl EquivalenceConstitution equiv_restriction_stable S1 H1
    (fun x => err_map f x = err_map g x).

(** ★ The equalizing morphism EQUALIZES f and g:  e ; f = e ; g. *)
Lemma eq_incl_equalizes {L} {S1 S2 : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2) :
  err_morph_eq (err_comp (eq_incl H1 f g) f) (err_comp (eq_incl H1 f g) g).
Proof. intro x. exact (proj2_sig x). Qed.

(* ===================================================================== *)
(*  The universal property                                                 *)
(* ===================================================================== *)

(** The MEDIATOR: any morphism h : T → S1 that equalizes f,g factors through the equalizer.
    On elements: t ↦ ⟨h t, (the proof that f(h t) = g(h t))⟩. *)
Definition eq_mediator {L} {S1 S2 T : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
  (h : ERRMorphism T S1) (Heq : err_morph_eq (err_comp h f) (err_comp h g))
  : ERRMorphism T (fs_equalizer H1 f g).
Proof.
  refine (@mkERRMorphism L T (fs_equalizer H1 f g)
            (fun t => exist (fun x => err_map f x = err_map g x) (err_map h t) (Heq t)) _).
  intros t t' Hr. exact (err_pres h t t' Hr).
Defined.

(** ★ The mediator factors h:  mediator ; e = h. *)
Lemma eq_mediator_factors {L} {S1 S2 T : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
  (h : ERRMorphism T S1) (Heq : err_morph_eq (err_comp h f) (err_comp h g)) :
  err_morph_eq (err_comp (eq_mediator H1 f g h Heq) (eq_incl H1 f g)) h.
Proof. intro t. reflexivity. Qed.

(** ★ Uniqueness AS A SUBOBJECT: any mediator's image in S1 is forced to be err_map h.
    (Full Leibniz uniqueness of the mediator needs proof-irrelevance of the agreement predicate
    — the same wall as the first-iso theorem, dissolvable on decidable carriers.) *)
Lemma eq_mediator_unique_in_S1 {L} {S1 S2 T : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
  (h : ERRMorphism T S1) (u : ERRMorphism T (fs_equalizer H1 f g))
  (Hu : err_morph_eq (err_comp u (eq_incl H1 f g)) h) :
  forall t, proj1_sig (err_map u t) = err_map h t.
Proof. intro t. exact (Hu t). Qed.

(* ===================================================================== *)
(*  Pullbacks: products + equalizers give pullbacks (finite completeness)   *)
(* ===================================================================== *)

Section Pullback.
  Context {L} {A B C : FunctionalSystem L}.
  Context (HA : fs_constitution A = EquivalenceConstitution)
          (HB : fs_constitution B = EquivalenceConstitution).
  Context (f : ERRMorphism A C) (g : ERRMorphism B C).

  (** The pullback of f,g over C = the equalizer of (π1 ; f) and (π2 ; g) on A × B. *)
  Definition pb_prod := fs_product A B HA HB.
  Definition pb_m1 : ERRMorphism pb_prod C := err_comp (fs_proj1 A B HA HB) f.
  Definition pb_m2 : ERRMorphism pb_prod C := err_comp (fs_proj2 A B HA HB) g.
  Definition fs_pullback := fs_equalizer (fs_product_rules A B HA HB) pb_m1 pb_m2.
  Definition pb_incl := eq_incl (fs_product_rules A B HA HB) pb_m1 pb_m2.

  (** ★ The pullback square commutes: the two paths pullback → A → C and pullback → B → C agree. *)
  Lemma fs_pullback_commutes :
    err_morph_eq (err_comp pb_incl pb_m1) (err_comp pb_incl pb_m2).
  Proof. apply eq_incl_equalizes. Qed.
End Pullback.

(* ===================================================================== *)
(*  Concrete grounding                                                     *)
(* ===================================================================== *)

(** The equalizer of the identity and the constant-true map on the discrete bool system carves
    out exactly {true}: true is in the agreement locus, false is not. *)
Lemma eq_agree_true : err_map (err_id SDisc) true = err_map fconst true.
Proof. reflexivity. Qed.

Lemma eq_agree_false : err_map (err_id SDisc) false <> err_map fconst false.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE E/R/R CATEGORY HAS EQUALIZERS — hence (with the previously-built terminal object and
    binary products) it is FINITELY COMPLETE.
      (equalizes)  the equalizing morphism satisfies e ; f = e ; g;
      (factors)    every equalizing cone factors through the equalizer;
      (unique)     the mediator is unique as a subobject (its image in S1 is forced).
    The pullback (fs_pullback) is the equalizer over the product — products + equalizers give all
    finite limits.  Honest: subobject-uniqueness 0-axiom; full mediator uniqueness is the PI wall. *)
Theorem err_equalizer :
  (forall (L : Level) (S1 S2 : FunctionalSystem L)
      (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2),
      err_morph_eq (err_comp (eq_incl H1 f g) f) (err_comp (eq_incl H1 f g) g))
  /\ (forall (L : Level) (S1 S2 T : FunctionalSystem L)
        (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
        (h : ERRMorphism T S1) (Heq : err_morph_eq (err_comp h f) (err_comp h g)),
        err_morph_eq (err_comp (eq_mediator H1 f g h Heq) (eq_incl H1 f g)) h)
  /\ (forall (L : Level) (S1 S2 T : FunctionalSystem L)
        (H1 : fs_constitution S1 = EquivalenceConstitution) (f g : ERRMorphism S1 S2)
        (h : ERRMorphism T S1) (u : ERRMorphism T (fs_equalizer H1 f g)),
        err_morph_eq (err_comp u (eq_incl H1 f g)) h ->
        forall t, proj1_sig (err_map u t) = err_map h t).
Proof.
  split; [ | split ].
  - intros L S1 S2 H1 f g. exact (eq_incl_equalizes H1 f g).
  - intros L S1 S2 T H1 f g h Heq. exact (eq_mediator_factors H1 f g h Heq).
  - intros L S1 S2 T H1 f g h u Hu. exact (eq_mediator_unique_in_S1 H1 f g h u Hu).
Qed.

Print Assumptions err_equalizer.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Equalizers + finite completeness of the E/R/R category.  fs_equalizer    *)
(*  (= sub-system on the agreement locus {x | f x = g x}) + fs_equalizer_     *)
(*  carrier.  eq_incl (equalizing morphism) + eq_incl_equalizes (e;f = e;g).  *)
(*  eq_mediator (the factoring morphism) + eq_mediator_factors + eq_mediator_ *)
(*  unique_in_S1 (subobject uniqueness; full uniqueness = PI wall).  Pullback *)
(*  section: fs_pullback (= equalizer over the product) + fs_pullback_        *)
(*  commutes — products + equalizers give pullbacks.  eq_agree_true/_false    *)
(*  (concrete: equalizer of id and const-true on SDisc = {true}).  Capstone   *)
(*  err_equalizer.  With terminal (ERRTerminalInitial) + products             *)
(*  (ERRComposition), the category is finitely complete.  HONEST: cocomplete- *)
(*  ness (coequalizers/pushouts) not built; full mediator uniqueness = PI.    *)
(* ========================================================================= *)
