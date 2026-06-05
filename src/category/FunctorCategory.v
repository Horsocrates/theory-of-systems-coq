(** * FunctorCategory.v — The functor category [C,D] as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: functors C -> D (objects), natural transformations (morphisms)
    Roles:    id_nat_trans -> Neutral, vertical composition -> Combinator
    Rules:    the category laws hold COMPONENTWISE from D's laws (constitution)
    Status:   the hom-category [C,D]; an isomorphism in [C,D] = natural isomorphism

    Builds on: stdlib/Category.v (Category, is_iso), stdlib/Functor.v
               (Functor, NatTrans, id_nat_trans, vert_comp_nat_trans).

    Why this and not "Cat" (categories as objects, functors as morphisms):
    functor equality is type-dependent (fmor lives over fobj), so "Cat" needs
    transport along object equalities.  The functor category [C,D] has NO such
    obstruction: morphisms are natural transformations whose components all
    have a fixed shape, and equality is componentwise — every law reduces to
    the corresponding law of D, applied at each object.  This is the clean,
    fully constructive piece of "categories form a category".

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.

(* ================================================================= *)
(*  Morphism equality in [C,D]: componentwise equality of nat-trans  *)
(* ================================================================= *)

Definition nt_eq (C D : Category) (F G : Functor C D)
  (alpha beta : NatTrans C D F G) : Prop :=
  forall a, cat_mor_eq D (fobj F a) (fobj G a) (nt_comp alpha a) (nt_comp beta a).

(* ================================================================= *)
(*  The functor category [C,D]                                       *)
(* ================================================================= *)

(** Objects = functors C -> D, morphisms = natural transformations,
    identity = id_nat_trans, composition = vertical composition.
    Every category law follows componentwise from D's laws. *)
Definition FunctorCat (C D : Category) : Category.
Proof.
  apply (mkCategory
    (Functor C D)
    (fun F G => NatTrans C D F G)
    (fun F G => nt_eq C D F G)
    (fun F => id_nat_trans C D F)
    (fun F G H beta alpha => vert_comp_nat_trans C D F G H alpha beta)).
  - (* cat_mor_eq_refl *)
    intros F G f. unfold nt_eq. intros a. apply cat_mor_eq_refl.
  - (* cat_mor_eq_sym *)
    intros F G f g Hfg. unfold nt_eq in *. intros a.
    apply cat_mor_eq_sym. apply Hfg.
  - (* cat_mor_eq_trans *)
    intros F G f g h Hfg Hgh. unfold nt_eq in *. intros a.
    apply (cat_mor_eq_trans D _ _ (nt_comp f a) (nt_comp g a) (nt_comp h a)).
    + apply Hfg.
    + apply Hgh.
  - (* cat_comp_compat *)
    intros F G H beta beta' alpha alpha' Hbeta Halpha. unfold nt_eq in *. intros a.
    simpl. apply cat_comp_compat.
    + apply Hbeta.
    + apply Halpha.
  - (* cat_assoc *)
    intros F G H K f g h. unfold nt_eq. intros a. simpl. apply cat_assoc.
  - (* cat_id_l *)
    intros F G f. unfold nt_eq. intros a. simpl. apply cat_id_l.
  - (* cat_id_r *)
    intros F G f. unfold nt_eq. intros a. simpl. apply cat_id_r.
Defined.

(* ================================================================= *)
(*  Basic facts                                                      *)
(* ================================================================= *)

(** The morphism equality of [C,D] is exactly componentwise equality *)
Lemma FunctorCat_mor_eq_iff : forall (C D : Category) (F G : Functor C D)
  (alpha beta : NatTrans C D F G),
  cat_mor_eq (FunctorCat C D) F G alpha beta <->
  (forall a, cat_mor_eq D (fobj F a) (fobj G a) (nt_comp alpha a) (nt_comp beta a)).
Proof.
  intros C D F G alpha beta. split; intro H; exact H.
Qed.

(** The identity morphism of [C,D] is componentwise the identity of D *)
Lemma FunctorCat_id_component : forall (C D : Category) (F : Functor C D) (a : cat_obj C),
  cat_mor_eq D (fobj F a) (fobj F a)
    (nt_comp (cat_id (FunctorCat C D) F) a)
    (cat_id D (fobj F a)).
Proof.
  intros C D F a. simpl. apply cat_mor_eq_refl.
Qed.

(** Composition in [C,D] is componentwise composition in D *)
Lemma FunctorCat_comp_component : forall (C D : Category) (F G H : Functor C D)
  (beta : NatTrans C D G H) (alpha : NatTrans C D F G) (a : cat_obj C),
  cat_mor_eq D (fobj F a) (fobj H a)
    (nt_comp (cat_comp (FunctorCat C D) F G H beta alpha) a)
    (cat_comp D (fobj F a) (fobj G a) (fobj H a) (nt_comp beta a) (nt_comp alpha a)).
Proof.
  intros C D F G H beta alpha a. simpl. apply cat_mor_eq_refl.
Qed.

(** KEY BRIDGE: an isomorphism in [C,D] is a componentwise (pointwise)
    isomorphism in D — i.e. a natural isomorphism gives an iso at each object. *)
Lemma FunctorCat_iso_componentwise : forall (C D : Category) (F G : Functor C D)
  (eta : NatTrans C D F G),
  is_iso (FunctorCat C D) F G eta ->
  forall a, is_iso D (fobj F a) (fobj G a) (nt_comp eta a).
Proof.
  intros C D F G eta [delta [Hgf Hfg]] a.
  (* Hgf : cat_comp[C,D] delta eta = id_F  (componentwise) *)
  (* Hfg : cat_comp[C,D] eta delta = id_G  (componentwise) *)
  specialize (Hgf a). specialize (Hfg a). simpl in Hgf, Hfg.
  exists (nt_comp delta a). split.
  - exact Hgf.
  - exact Hfg.
Qed.

(* ================================================================= *)
(*  Summary: 4 Qed, 0 Admitted, 0 axioms                            *)
(*    FunctorCat_mor_eq_iff, FunctorCat_id_component,                 *)
(*    FunctorCat_comp_component, FunctorCat_iso_componentwise         *)
(* ================================================================= *)
