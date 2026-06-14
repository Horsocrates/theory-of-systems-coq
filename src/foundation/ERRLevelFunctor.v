(** * ERRLevelFunctor.v — the level-bump is a FULL FAITHFUL FUNCTOR (the vertical structure).

    The horizontal structure (within one level: bicomplete, 2-categorical, self-enriched) is built.
    The VERTICAL structure — the P1 level hierarchy — so far had only fs_lift (ERRActualization) as an
    OBJECT map.  This file makes it a genuine FUNCTOR  FunctionalSystem L → FunctionalSystem (LS L):
    it acts on morphisms (lift_morphism), preserves identity and composition, and is FULL and
    FAITHFUL.  So the hierarchy is a TOWER OF FULL EMBEDDINGS, and the categorical structure
    transports up it.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the level-bump is functorial — it acts on MORPHISMS, not just objects, preserving identity and
      composition, BECAUSE it preserves the whole triad (carrier and Roles), so a morphism's data
      (err_map + err_pres) transports verbatim one level up.  fs_lift is the embed functor of the P1
      hierarchy.
    Roles (L4): lift_morphism = the action on arrows (the same err_map / err_pres retyped at LS L);
      the functor laws (lift_id, lift_comp) and full-faithfulness are the structure it carries.
    Elements (L1+P4): the morphisms and their underlying Element-maps; the products-as-elements that
      become elements one level up (Products(L) = Elements(L+1)).
    P4 diagnostic (could it be otherwise?):
      no — Products(L) = Elements(L+1) means the carrier is IDENTICAL across the bump, so the hom-sets
      are identical: the embedding is forced to be FULL and FAITHFUL (no data lost, none added).
    Honesty wall:
      this is the EMBED functor (UP the hierarchy).  There is NO total forgetful functor DOWN (an
      (L+1)-system's elements need not all be graded < L), so NO adjunction is claimed here (contrast
      LevelAdjunction for the legacy indexed-System notion — honest).  Product preservation is shown at
      the TRIAD level (carrier + Roles equal by reflexivity); full record equality of fs_lift(product)
      and product(fs_lift,fs_lift) needs proof-irrelevance on the fs_functional / fs_level_valid fields
      (the usual PI wall), so it is stated as triad-equality, not Leibniz object-equality.  Reuses
      ERRActualization (fs_lift) + ERRComposition + ERRIso.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.     (* ERRMorphism, err_map, err_pres, err_comp, err_id, err_morph_eq, mkERRMorphism, fs_product *)
From ToS Require Import foundation.ERRActualization.    (* fs_lift, lift_elements, lift_roles, lift_rules *)
From ToS Require Import foundation.ERRIso.              (* iso *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  The functor's action on morphisms                                      *)
(* ===================================================================== *)

(** ★★ The level-bump acts on MORPHISMS: a morphism S1 → S2 (at L) lifts to a morphism
    (fs_lift S1) → (fs_lift S2) (at LS L) — the SAME underlying data (fs_lift preserves carrier and
    Roles), retyped one level up. *)
Definition lift_morphism {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2)
  : ERRMorphism (fs_lift S1) (fs_lift S2).
Proof.
  refine (@mkERRMorphism (LS L) (fs_lift S1) (fs_lift S2) (err_map m) _).
  exact (err_pres m).
Defined.

(** The action on the underlying Element-map is the identity (computes). *)
Lemma lift_morphism_map {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2)
  (x : get_Elements (fs_lift S1)) :
  err_map (lift_morphism m) x = err_map m x.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Functor laws                                                           *)
(* ===================================================================== *)

(** ★ The functor preserves identities. *)
Lemma lift_id {L} (S : FunctionalSystem L) :
  err_morph_eq (lift_morphism (err_id S)) (err_id (fs_lift S)).
Proof. intro x. reflexivity. Qed.

(** ★ The functor preserves composition. *)
Lemma lift_comp {L} {S1 S2 S3 : FunctionalSystem L}
  (m : ERRMorphism S1 S2) (n : ERRMorphism S2 S3) :
  err_morph_eq (lift_morphism (err_comp m n)) (err_comp (lift_morphism m) (lift_morphism n)).
Proof. intro x. reflexivity. Qed.

(* ===================================================================== *)
(*  Full and faithful (a full embedding)                                   *)
(* ===================================================================== *)

(** ★ FAITHFUL: distinct morphisms lift to distinct morphisms. *)
Lemma lift_faithful {L} {S1 S2 : FunctionalSystem L} (m1 m2 : ERRMorphism S1 S2) :
  err_morph_eq (lift_morphism m1) (lift_morphism m2) -> err_morph_eq m1 m2.
Proof. intros H x. exact (H x). Qed.

(** ★★ FULL: every morphism between lifted systems comes from a morphism below (the carrier is
    preserved, so the data of an (LS L)-morphism IS the data of an L-morphism). *)
Lemma lift_full {L} {S1 S2 : FunctionalSystem L} (m' : ERRMorphism (fs_lift S1) (fs_lift S2)) :
  exists m : ERRMorphism S1 S2, err_morph_eq (lift_morphism m) m'.
Proof.
  exists (@mkERRMorphism L S1 S2 (err_map m') (err_pres m')).
  intro x. reflexivity.
Qed.

(* ===================================================================== *)
(*  Preservation of structure                                              *)
(* ===================================================================== *)

(** ★ The functor preserves isomorphisms (full embeddings do). *)
Lemma lift_preserves_iso {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2) :
  iso m -> iso (lift_morphism m).
Proof.
  intros [n [Hmn Hnm]]. exists (lift_morphism n). split.
  - intro x. exact (Hmn x).
  - intro x. exact (Hnm x).
Qed.

(** ★★ The functor preserves products at the triad level: the lift of a product has the same
    carrier and Roles as the product of the lifts.  (Full record equality needs proof-irrelevance on
    the proof fields — the PI wall — so we state triad-equality.) *)
Lemma lift_preserves_product_triad {L} {S1 S2 : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution) :
  get_Elements (fs_lift (fs_product S1 S2 H1 H2))
    = get_Elements (fs_product (fs_lift S1) (fs_lift S2) H1 H2)
  /\ get_Roles (fs_lift (fs_product S1 S2 H1 H2))
    = get_Roles (fs_product (fs_lift S1) (fs_lift S2) H1 H2).
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE LEVEL-BUMP IS A FULL FAITHFUL FUNCTOR.
      (action)  lift_morphism : (S1 → S2 at L)  ↦  (fs_lift S1 → fs_lift S2 at LS L);
      (laws)    preserves identity and composition;
      (full + faithful)  the hom-sets are identical across the bump — a full embedding;
      (structure)  preserves isomorphisms and (the triad of) products.
    So the P1 level hierarchy is a TOWER OF FULL EMBEDDINGS, transporting the within-level
    categorical structure up.  Honest: embed only (no forgetful adjunction down). *)
Theorem err_level_functor :
  (forall (L : Level) (S : FunctionalSystem L),
     err_morph_eq (lift_morphism (err_id S)) (err_id (fs_lift S)))
  /\ (forall (L : Level) (S1 S2 S3 : FunctionalSystem L) (m : ERRMorphism S1 S2) (n : ERRMorphism S2 S3),
        err_morph_eq (lift_morphism (err_comp m n)) (err_comp (lift_morphism m) (lift_morphism n)))
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (m1 m2 : ERRMorphism S1 S2),
        err_morph_eq (lift_morphism m1) (lift_morphism m2) -> err_morph_eq m1 m2)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (m' : ERRMorphism (fs_lift S1) (fs_lift S2)),
        exists m : ERRMorphism S1 S2, err_morph_eq (lift_morphism m) m')
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (m : ERRMorphism S1 S2),
        iso m -> iso (lift_morphism m)).
Proof.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros L S. exact (lift_id S).
  - intros L S1 S2 S3 m n. exact (lift_comp m n).
  - intros L S1 S2 m1 m2 H. exact (lift_faithful m1 m2 H).
  - intros L S1 S2 m'. exact (lift_full m').
  - intros L S1 S2 m. exact (lift_preserves_iso m).
Qed.

Print Assumptions err_level_functor.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The level-bump fs_lift as a FULL FAITHFUL FUNCTOR (the vertical axis).    *)
(*  lift_morphism (action on arrows) + lift_morphism_map.  lift_id / lift_    *)
(*  comp (functor laws).  lift_faithful + lift_full (a full embedding — the    *)
(*  hom-sets are identical across the bump).  lift_preserves_iso + lift_       *)
(*  preserves_product_triad (preserves isos and the triad of products).       *)
(*  Capstone err_level_functor.  The P1 hierarchy is a tower of full          *)
(*  embeddings, transporting the within-level categorical structure up.       *)
(*  HONEST: embed only (no total forgetful functor down ⟹ no adjunction);     *)
(*  product preservation at the triad level (full record equality = PI wall). *)
(* ========================================================================= *)
