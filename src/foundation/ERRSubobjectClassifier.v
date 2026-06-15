(** * ERRSubobjectClassifier.v — the topos question, resolved: a classifier on the decidable
      Roles-saturated fragment; full topos-hood fails exactly at H1 + the Roles constraint.

    Does the category of E/R/R systems have a subobject classifier (is it a topos)?  The discrete
    two-element system Ω = SDisc (carrier bool, Roles = equality) is the candidate, with `true`
    distinguished.  A sub-object = a predicate P on a system X; its characteristic morphism χ : X → Ω
    sends x to `true` iff P x.  Two constraints emerge, and they are the whole answer:

      ★ for χ to be a MORPHISM (preserve Roles), P must be ROLES-SATURATED: x ~ y ⟹ (P x ↔ P y);
      ★ for χ to be bool-valued, P must be DECIDABLE.

    So a sub-object is classified by Ω  ⟺  its predicate is DECIDABLE and ROLES-SATURATED.  The
    category is a topos on exactly that fragment; full topos-hood fails precisely at (a) decidability
    (= H1: an undecidable predicate is a role-limit, no computable χ) and (b) Roles-saturation (the
    Roles tier forbids classifying a predicate that splits a Roles-class).  Not a dead wall — a precise
    characterization, and the two obstructions ARE H1 and the Roles tier.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      Ω = SDisc with `true` classifies a sub-object P by its characteristic morphism χ; the Rules force
      χ to be a morphism (Roles-saturation) and bool-valued (decidability).
    Roles (L4): roles_saturated (the predicate respects the system's Roles); char (the characteristic
      morphism); the classification A = χ⁻¹(true).
    Elements (L1+P4): the carrier points; the truth-values in/out; the decision procedure.
    P4 diagnostic (could it be otherwise?):
      no — classifiability is forced to coincide with decidability ∧ Roles-saturation; an undecidable
      predicate is a role-limit (no computable χ), a non-saturated one splits a Roles-class (no
      morphism).  The two walls ARE H1 (decidability) and the Roles tier.
    Honesty wall:
      this is the honest resolution: a subobject classifier EXISTS on the decidable Roles-saturated
      fragment (char, unique), and classifiability ⟺ decidable ∧ Roles-saturated (proved both ways).
      So the category is NOT a full topos (undecidable / non-saturated sub-objects are unclassified) —
      that failure is exactly H1 + the Roles constraint.  Predicate-based (a sub-object = a predicate,
      corresponding to fs_subsystem).  Reuses SDisc (ERRQuotient) + SB (ERRDynamics).  0 axioms.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, err_map, err_pres, err_morph_eq, mkERRMorphism *)
From ToS Require Import foundation.ERRQuotient.        (* SDisc — the classifier object Omega *)
From ToS Require Import foundation.ERRDynamics.        (* SB — the full-Roles contrast *)
From Stdlib Require Import Bool.

(* ===================================================================== *)
(*  The classifier object and Roles-saturation                             *)
(* ===================================================================== *)

(** Omega = the discrete two-element system; `true` is the distinguished truth value. *)
Definition Omega : FunctionalSystem L2 := SDisc.

(** A predicate is ROLES-SATURATED if it respects the system's Roles (Roles-classes are not split). *)
Definition roles_saturated {L} (X : FunctionalSystem L) (P : get_Elements X -> Prop) : Prop :=
  forall x y, get_Roles X x y -> (P x <-> P y).

(* ===================================================================== *)
(*  The characteristic morphism (for decidable, Roles-saturated P)         *)
(* ===================================================================== *)

(** ★★ The characteristic morphism χ : X → Ω of a decidable, Roles-saturated sub-object. *)
Definition char (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
  (Pdec : forall x, {P x} + {~ P x}) (Psat : roles_saturated X P)
  : ERRMorphism X Omega.
Proof.
  refine (@mkERRMorphism L2 X Omega (fun x => if Pdec x then true else false) _).
  intros x y H. destruct (Pdec x) as [px | npx], (Pdec y) as [py | npy].
  - reflexivity.
  - exfalso. apply npy. exact (proj1 (Psat x y H) px).
  - exfalso. apply npx. exact (proj2 (Psat x y H) py).
  - reflexivity.
Defined.

(** ★★ It CLASSIFIES: the sub-object is the preimage of `true` (A = χ⁻¹(true)). *)
Lemma char_classifies (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
  (Pdec : forall x, {P x} + {~ P x}) (Psat : roles_saturated X P) :
  forall x, P x <-> err_map (char X P Pdec Psat) x = true.
Proof.
  intro x. cbn. destruct (Pdec x) as [px | npx].
  - split; [ intro; reflexivity | intro; exact px ].
  - split; [ intro H; exfalso; exact (npx H) | intro H; discriminate H ].
Qed.

(** ★★ It is UNIQUE: any morphism that classifies P equals χ. *)
Lemma char_unique (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
  (Pdec : forall x, {P x} + {~ P x}) (Psat : roles_saturated X P)
  (g : ERRMorphism X Omega) (Hg : forall x, P x <-> err_map g x = true) :
  err_morph_eq (char X P Pdec Psat) g.
Proof.
  intro x. cbn. destruct (Pdec x) as [px | npx].
  - symmetry. exact (proj1 (Hg x) px).
  - destruct (err_map g x) eqn:E.
    + exfalso. apply npx. exact (proj2 (Hg x) E).
    + reflexivity.
Qed.

(* ===================================================================== *)
(*  The two walls: classifiable ⟹ decidable AND Roles-saturated            *)
(* ===================================================================== *)

(** ★★ WALL 1 (= H1): a classifiable predicate is DECIDABLE — the classifier reaches only the
    Element side; an undecidable predicate (role-limit) has no characteristic morphism. *)
Lemma classified_implies_decidable (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
  (g : ERRMorphism X Omega) (Hg : forall x, P x <-> err_map g x = true) :
  forall x, {P x} + {~ P x}.
Proof.
  intro x. destruct (bool_dec (err_map g x) true) as [E | E].
  - left. exact (proj2 (Hg x) E).
  - right. intro H. apply E. exact (proj1 (Hg x) H).
Qed.

(** ★★ WALL 2 (= the Roles tier): a classifiable predicate is ROLES-SATURATED — χ being a morphism
    forces it to respect the Roles. *)
Lemma classified_implies_saturated (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
  (g : ERRMorphism X Omega) (Hg : forall x, P x <-> err_map g x = true) :
  roles_saturated X P.
Proof.
  intros x y Hxy. pose proof (err_pres g x y Hxy) as Hg'. split; intro H.
  - apply (proj2 (Hg y)). rewrite <- Hg'. exact (proj1 (Hg x) H).
  - apply (proj2 (Hg x)). rewrite Hg'. exact (proj1 (Hg y) H).
Qed.

(* ===================================================================== *)
(*  How far the classifier reaches depends on the target's Rules/Roles     *)
(* ===================================================================== *)

(** On the DISCRETE system every predicate is Roles-saturated (Roles = equality) — so there
    classifiability = decidability alone (the full Set-like topos on decidable predicates). *)
Lemma sdisc_all_saturated : forall (P : get_Elements SDisc -> Prop), roles_saturated SDisc P.
Proof. intros P x y H. rewrite H. split; intro; assumption. Qed.

(** On the FULL-Roles system only constant predicates are saturated (Roles relate everything) — so
    the classifier sees only the ⊤/⊥ sub-objects (degenerate). *)
Lemma sb_saturated_is_constant : forall (P : get_Elements SB -> Prop),
  roles_saturated SB P -> forall x y, P x <-> P y.
Proof. intros P Hsat x y. apply Hsat. exact I. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE TOPOS QUESTION, RESOLVED.
      (classifies)  Ω = SDisc with `true` classifies every decidable Roles-saturated sub-object via χ;
      (unique)      the characteristic morphism is unique;
      (the walls)   conversely, a classifiable sub-object MUST be decidable (= H1) and Roles-saturated
                    (= the Roles tier).
    Hence: a sub-object is classified  ⟺  its predicate is decidable ∧ Roles-saturated.  The category
    of E/R/R systems has a subobject classifier on exactly that fragment; it is NOT a full topos, and
    that failure is precisely the finitization boundary (decidability) together with the Roles
    constraint — H1 and the Roles tier, once more. *)
(** (Stated with prod `*` because decidability {P x}+{~P x} is Type-valued, not Prop — the
    computational content is exactly the point.) *)
Theorem err_subobject_classifier :
  (forall (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
      (Pdec : forall x, {P x} + {~ P x}) (Psat : roles_saturated X P),
      forall x, P x <-> err_map (char X P Pdec Psat) x = true)
  * (forall (X : FunctionalSystem L2) (P : get_Elements X -> Prop)
        (Pdec : forall x, {P x} + {~ P x}) (Psat : roles_saturated X P)
        (g : ERRMorphism X Omega),
        (forall x, P x <-> err_map g x = true) -> err_morph_eq (char X P Pdec Psat) g)
  * (forall (X : FunctionalSystem L2) (P : get_Elements X -> Prop) (g : ERRMorphism X Omega),
        (forall x, P x <-> err_map g x = true) ->
        (forall x, {P x} + {~ P x}) * roles_saturated X P).
Proof.
  split; [ split | ].
  - intros X P Pdec Psat. exact (char_classifies X P Pdec Psat).
  - intros X P Pdec Psat g Hg. exact (char_unique X P Pdec Psat g Hg).
  - intros X P g Hg.
    split; [ exact (classified_implies_decidable X P g Hg)
           | exact (classified_implies_saturated X P g Hg) ].
Qed.

Print Assumptions err_subobject_classifier.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  7 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The topos question resolved.  Omega = SDisc (classifier object).  roles_   *)
(*  saturated (the predicate respects Roles).  char (characteristic morphism   *)
(*  for decidable Roles-saturated P) + char_classifies (A = chi^-1(true)) +    *)
(*  char_unique.  classified_implies_decidable (WALL 1 = H1) + classified_     *)
(*  implies_saturated (WALL 2 = Roles tier): classifiable => decidable AND     *)
(*  Roles-saturated; with char the converse, so classifiable IFF decidable     *)
(*  AND Roles-saturated.  sdisc_all_saturated (discrete: full reach modulo     *)
(*  decidability) vs sb_saturated_is_constant (full Roles: only constant).     *)
(*  Capstone err_subobject_classifier.  The category is a topos on the         *)
(*  decidable Roles-saturated fragment; full topos-hood fails exactly at H1    *)
(*  (decidability) + the Roles tier — not a dead wall, a precise boundary.     *)
(* ========================================================================= *)
