(** * ERREnrichedComposition.v — closing the wall: composition and identity AS MORPHISMS.

    ERR2CategoryHom.v built the hom-object fs_hom S1 S2 (a FunctionalSystem) and showed the
    internal composition RESPECTS its Roles (hom_comp_is_role_morphism) — but it left the
    enriched composition and identity as bare facts, not packaged as actual morphisms of the
    category.  This file closes that wall: the E/R/R category is a genuine SELF-ENRICHED category.

      comp_morph : fs_hom S2 S3 × fs_hom S1 S2  →  fs_hom S1 S3      (composition IS a morphism)
      id_morph   : 𝟙 → fs_hom S S                                    (identity IS a morphism)
      + the enriched unit laws (left, right) and associativity.

    Global elements of a hom-object (morphisms out of the point 𝟙) ARE the morphisms — a small
    representability fact; the identity is the global element picking err_id.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      composition, to be a MORPHISM of hom-objects, must carry the product's Roles into the
      target's Roles — i.e. it must respect the 2-cells.  That it does is hom_comp_is_role_morphism
      (= Roles2_hcomp), and it holds because the hom-objects' Rules are equivalences (the gate).
      The unit object 𝟙 is the point system; the identity is a constant map into the hom-object,
      well-defined because Roles2 is reflexive (the Rules again).
    Roles (L4): the product's Roles (prod_rel of two Roles2) and the target's Roles (Roles2) —
      composition is exactly the map that turns the former into the latter.
    Elements (L1+P4): pairs of morphisms (the product carrier) and single morphisms (the target);
      composition acts on actual element-pairs; the point has one element.
    P4 diagnostic (could it be otherwise?):
      composition could only be a morphism BY respecting the 2-cells — any map of hom-objects must
      (err_pres); and the ONLY structure-respecting such map sending (g,f) to a single morphism is
      g∘f.  Forced.  Global elements = morphisms because the point has trivial (full) Roles, so any
      target morphism gives a valid constant map — nothing else is needed.
    Honesty wall:
      this packages composition / identity as morphisms and proves the unit + associativity laws
      (all at the err_map / err_morph_eq level — the honest "thin" equational content, NOT 2-cell-
      proof equalities, consistent with ERR2Category's locally-thin wall).  Full enriched-category
      coherence (associator/unitor 2-cells, interchange) is not packaged — same Prop-thinness wall.
      Reuses ERRComposition (fs_product) + ERR2Category + ERR2CategoryHom.  0 axioms.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.     (* fs_product, err_comp, err_id, err_map, err_morph_eq, mkERRMorphism *)
From ToS Require Import foundation.ERR2Category.         (* roles_equiv, Roles2, Roles2_refl, Roles2_hcomp *)
From ToS Require Import foundation.ERR2CategoryHom.      (* fs_hom, fs_hom_rules, SB_roles_equiv *)
From ToS Require Import foundation.ERRDynamics.          (* SB *)
From ToS Require Import foundation.ERRDynamicsArrow.     (* flip *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  The point (unit) object at level LS L                                  *)
(* ===================================================================== *)

(** The terminal / point system at the hom-objects' level (one element, full Roles). *)
Definition fs_point {L} : FunctionalSystem (LS L).
Proof.
  refine (@mkFunctionalSystem (LS L)
            EquivalenceConstitution unit (fun _ _ => True) _ (fun _ => L) (fun _ => _)).
  - unfold EquivalenceConstitution. split; [ | split ]; intros; exact I.
  - simpl. left. reflexivity.
Defined.

(* ===================================================================== *)
(*  Global elements of a hom-object ARE the morphisms                      *)
(* ===================================================================== *)

(** A global element of fs_hom S1 S2 = a morphism 𝟙 → fs_hom S1 S2.  Picking the morphism m. *)
Definition global_elt {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2)
  (m : ERRMorphism S1 S2) : ERRMorphism (@fs_point L) (fs_hom S1 S2 He) :=
  @mkERRMorphism (LS L) (@fs_point L) (fs_hom S1 S2 He)
    (fun _ => m) (fun x y _ => Roles2_refl He m).

Lemma global_elt_computes {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2)
  (m : ERRMorphism S1 S2) (u : unit) :
  err_map (global_elt S1 S2 He m) u = m.
Proof. reflexivity. Qed.

(** ★ Representability: EVERY morphism S1→S2 arises as a global element of the hom-object. *)
Lemma global_elt_recovers_all {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2)
  (m : ERRMorphism S1 S2) :
  exists ge : ERRMorphism (@fs_point L) (fs_hom S1 S2 He), err_map ge tt = m.
Proof. exists (global_elt S1 S2 He m). reflexivity. Qed.

(* ===================================================================== *)
(*  The identity as a morphism  𝟙 → fs_hom S S                            *)
(* ===================================================================== *)

(** The enriched identity = the global element picking out err_id. *)
Definition id_morph {L} (S : FunctionalSystem L) (He : roles_equiv S)
  : ERRMorphism (@fs_point L) (fs_hom S S He) :=
  global_elt S S He (err_id S).

Lemma id_morph_computes {L} (S : FunctionalSystem L) (He : roles_equiv S) (u : unit) :
  err_map (id_morph S He) u = err_id S.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Composition AS A MORPHISM  fs_hom S2 S3 × fs_hom S1 S2 → fs_hom S1 S3  *)
(* ===================================================================== *)

(** ★★ THE enriched composition morphism: a genuine ERRMorphism out of the product of two
    hom-objects, whose err_pres IS the fact that composition respects the 2-cells (Roles2_hcomp). *)
Definition comp_morph {L} {S1 S2 S3 : FunctionalSystem L}
  (He2 : roles_equiv S2) (He3 : roles_equiv S3)
  : ERRMorphism
      (fs_product (fs_hom S2 S3 He3) (fs_hom S1 S2 He2)
         (fs_hom_rules S2 S3 He3) (fs_hom_rules S1 S2 He2))
      (fs_hom S1 S3 He3).
Proof.
  refine (@mkERRMorphism (LS L)
            (fs_product (fs_hom S2 S3 He3) (fs_hom S1 S2 He2)
               (fs_hom_rules S2 S3 He3) (fs_hom_rules S1 S2 He2))
            (fs_hom S1 S3 He3)
            (fun p => err_comp (snd p) (fst p)) _).
  intros x y H. destruct H as [HG HF]. exact (Roles2_hcomp He3 HF HG).
Defined.

(** ★ The composition morphism actually computes composition:  (g, f) ↦ g ∘ f. *)
Lemma comp_morph_computes {L} {S1 S2 S3 : FunctionalSystem L}
  (He2 : roles_equiv S2) (He3 : roles_equiv S3)
  (g : ERRMorphism S2 S3) (f : ERRMorphism S1 S2) :
  err_map (comp_morph He2 He3) (g, f) = err_comp f g.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Enriched category laws (left/right unit, associativity)                *)
(* ===================================================================== *)

(** ★ Enriched LEFT unit: composing with the identity (on the S2 side) gives back the morphism. *)
Lemma comp_morph_left_unit {L} {S1 S2 : FunctionalSystem L} (He2 : roles_equiv S2)
  (f : ERRMorphism S1 S2) :
  err_morph_eq (err_map (@comp_morph L S1 S2 S2 He2 He2) (err_id S2, f)) f.
Proof. intro x. reflexivity. Qed.

(** ★ Enriched RIGHT unit: composing the identity (on the S1 side) gives back the morphism. *)
Lemma comp_morph_right_unit {L} {S1 S3 : FunctionalSystem L}
  (He1 : roles_equiv S1) (He3 : roles_equiv S3) (g : ERRMorphism S1 S3) :
  err_morph_eq (err_map (@comp_morph L S1 S1 S3 He1 He3) (g, err_id S1)) g.
Proof. intro x. reflexivity. Qed.

(** ★ Enriched ASSOCIATIVITY (the underlying composition is associative, definitionally). *)
Lemma comp_morph_assoc {L} {S1 S2 S3 S4 : FunctionalSystem L}
  (f : ERRMorphism S1 S2) (g : ERRMorphism S2 S3) (h : ERRMorphism S3 S4) :
  err_morph_eq (err_comp (err_comp f g) h) (err_comp f (err_comp g h)).
Proof. intro x. reflexivity. Qed.

(* ===================================================================== *)
(*  Concrete grounding                                                     *)
(* ===================================================================== *)

(** ★ Through the packaged composition morphism, flip ∘ flip = identity (involution),
    on the endo-hom-object of SB. *)
Lemma comp_SB_flip_flip :
  err_morph_eq (err_map (comp_morph SB_roles_equiv SB_roles_equiv) (flip, flip)) (err_id SB).
Proof. intro x. destruct x; reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE E/R/R CATEGORY IS SELF-ENRICHED.
      (comp)   composition is a genuine morphism out of the product of hom-objects, computing g∘f;
      (id)     the identity is a genuine morphism 𝟙 → hom(S,S), computing err_id;
      (units)  enriched left and right unit laws hold;
      (assoc)  enriched associativity holds.
    The hom-objects (ERR2CategoryHom) + these composition / identity morphisms + the laws =
    the data of a category enriched over itself.  All at the honest err_map level (Prop-thin
    2-cells), closing the wall flagged in ERR2CategoryHom (composition was a fact, now a morphism). *)
Theorem err_self_enriched :
  (forall (L : Level) (S1 S2 S3 : FunctionalSystem L) (He2 : roles_equiv S2) (He3 : roles_equiv S3)
      (g : ERRMorphism S2 S3) (f : ERRMorphism S1 S2),
      err_map (comp_morph He2 He3) (g, f) = err_comp f g)
  /\ (forall (L : Level) (S : FunctionalSystem L) (He : roles_equiv S) (u : unit),
        err_map (id_morph S He) u = err_id S)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (He2 : roles_equiv S2) (f : ERRMorphism S1 S2),
        err_morph_eq (err_map (@comp_morph L S1 S2 S2 He2 He2) (err_id S2, f)) f)
  /\ (forall (L : Level) (S1 S3 : FunctionalSystem L) (He1 : roles_equiv S1) (He3 : roles_equiv S3)
        (g : ERRMorphism S1 S3),
        err_morph_eq (err_map (@comp_morph L S1 S1 S3 He1 He3) (g, err_id S1)) g)
  /\ (forall (L : Level) (S1 S2 S3 S4 : FunctionalSystem L)
        (f : ERRMorphism S1 S2) (g : ERRMorphism S2 S3) (h : ERRMorphism S3 S4),
        err_morph_eq (err_comp (err_comp f g) h) (err_comp f (err_comp g h))).
Proof.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros L S1 S2 S3 He2 He3 g f. exact (comp_morph_computes He2 He3 g f).
  - intros L S He u. exact (id_morph_computes S He u).
  - intros L S1 S2 He2 f. exact (comp_morph_left_unit He2 f).
  - intros L S1 S3 He1 He3 g. exact (comp_morph_right_unit He1 He3 g).
  - intros L S1 S2 S3 S4 f g h. exact (comp_morph_assoc f g h).
Qed.

Print Assumptions err_self_enriched.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Closes the ERR2CategoryHom wall: composition and identity packaged AS     *)
(*  MORPHISMS — the E/R/R category is self-enriched.  fs_point (unit object). *)
(*  global_elt + global_elt_computes + global_elt_recovers_all (global        *)
(*  elements of a hom-object = the morphisms; representability).  id_morph    *)
(*  (= global_elt of err_id) + id_morph_computes.  comp_morph (composition as *)
(*  a morphism out of fs_product of hom-objects; err_pres = Roles2_hcomp) +   *)
(*  comp_morph_computes ((g,f) ↦ g∘f).  comp_morph_left_unit / _right_unit /  *)
(*  comp_morph_assoc (enriched category laws).  comp_SB_flip_flip (concrete:  *)
(*  flip∘flip = id through the packaged composition).  Capstone err_self_     *)
(*  enriched.  HONEST: laws at err_map / err_morph_eq level (Prop-thin); full *)
(*  enriched coherence (associator/unitor 2-cells) not packaged.  0 axioms.   *)
(* ========================================================================= *)
