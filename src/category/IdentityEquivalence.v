(** * IdentityEquivalence.v — The identity equivalence C ~= C as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: the identity functor as both directions of an equivalence
    Roles:    unit/counit and their inverses are all identity transformations
    Rules:    every round-trip is an identity law of C (constitution)
    Status:   a concrete witness that every category is equivalent to itself

    Builds on: stdlib/Category.v, stdlib/Functor.v, category/FunctorCategory.v,
               category/NaturalIsomorphism.v, category/EquivalenceOfCategories.v.

    Together with equiv_sym (EquivalenceOfCategories.v) this gives reflexivity
    and symmetry of "~="; transitivity (whiskered composition of equivalences)
    is left for a later step.

    STATUS: 2 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import category.FunctorCategory.
From ToS Require Import category.NaturalIsomorphism.
From ToS Require Import category.EquivalenceOfCategories.

(* ================================================================= *)
(*  The two identity natural transformations id_C <-> id_C . id_C    *)
(* ================================================================= *)

Definition nt_id_to_comp (C : Category) :
  NatTrans C C (id_functor C) (compose_functor C C C (id_functor C) (id_functor C)).
Proof.
  apply (mkNatTrans C C (id_functor C)
           (compose_functor C C C (id_functor C) (id_functor C))
           (fun a => cat_id C a)).
  intros a b f. simpl.
  apply (cat_mor_eq_trans C a b
    (cat_comp C a b b (cat_id C b) f) f (cat_comp C a a b f (cat_id C a))).
  - apply cat_id_l.
  - apply cat_mor_eq_sym. apply cat_id_r.
Defined.

Definition nt_comp_to_id (C : Category) :
  NatTrans C C (compose_functor C C C (id_functor C) (id_functor C)) (id_functor C).
Proof.
  apply (mkNatTrans C C (compose_functor C C C (id_functor C) (id_functor C))
           (id_functor C)
           (fun a => cat_id C a)).
  intros a b f. simpl.
  apply (cat_mor_eq_trans C a b
    (cat_comp C a b b (cat_id C b) f) f (cat_comp C a a b f (cat_id C a))).
  - apply cat_id_l.
  - apply cat_mor_eq_sym. apply cat_id_r.
Defined.

(* ================================================================= *)
(*  The identity equivalence                                         *)
(* ================================================================= *)

Definition id_equiv (C : Category) : CatEquiv C C.
Proof.
  apply (mkCatEquiv C C (id_functor C) (id_functor C)
           (nt_id_to_comp C) (nt_comp_to_id C)
           (nt_comp_to_id C) (nt_id_to_comp C)).
  - intro a. simpl. apply cat_id_l.   (* unit_sect   *)
  - intro a. simpl. apply cat_id_l.   (* unit_retr   *)
  - intro a. simpl. apply cat_id_l.   (* counit_sect *)
  - intro a. simpl. apply cat_id_l.   (* counit_retr *)
Defined.

(* ================================================================= *)
(*  Properties of the identity equivalence                           *)
(* ================================================================= *)

(** Its unit is componentwise the identity *)
Lemma id_equiv_unit_components : forall (C : Category) (a : cat_obj C),
  cat_mor_eq C a a (nt_comp (ce_unit (id_equiv C)) a) (cat_id C a).
Proof.
  intros C a. simpl. apply cat_mor_eq_refl.
Qed.

(** The forward functor of the identity equivalence is essentially surjective
    (a sanity instance of equiv_F_ess_surjective) *)
Lemma id_equiv_ess_surjective : forall (C : Category),
  is_ess_surjective C C (ce_F (id_equiv C)).
Proof.
  intro C. apply (equiv_F_ess_surjective C C (id_equiv C)).
Qed.

(* ================================================================= *)
(*  Summary: 2 Qed, 0 Admitted, 0 axioms                            *)
(*    id_equiv_unit_components, id_equiv_ess_surjective               *)
(*  (nt_id_to_comp, nt_comp_to_id, id_equiv are Definitions)         *)
(* ================================================================= *)
