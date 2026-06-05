(** * YonedaEmbedding.v — The Yoneda embedding is full and faithful

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: morphisms h : y -> x, natural transformations Hom(x,-) => Hom(y,-)
    Roles:    the embedding y |-> Hom(y,-) = "represent an object by its system of
              morphisms"; yoneda_embed_mor h = the induced transformation
              (precomposition by h)
    Rules:    full + faithful = the bijection cat_mor C y x ~= Nat(Hom(x,-),Hom(y,-)),
              a direct corollary of the Yoneda lemma at F := Hom(y,-) (constitution)
    Status:   yoneda_embed_mor; the embedding is faithful and full

    P4 diagnostic.  "An object is its representable functor" is a role-level
    identification, not a reduction of the object to a completed set of morphisms.
    Faithful+full is a rule of one-to-one reconstruction, not a size claim.  This
    is the categorical form of P3: the identity of an object is given through its
    roles (its morphisms); an iso of representables matches an iso of objects.

    Builds on: stdlib/Category.v, stdlib/Functor.v, category/SetoidCategory.v,
               category/YonedaLemma.v.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import category.SetoidCategory.
From ToS Require Import category.YonedaLemma.

(* ================================================================= *)
(*  The embedding on morphisms                                       *)
(* ================================================================= *)

(** A morphism h : y -> x induces a natural transformation
    Hom(x,-) => Hom(y,-) by precomposition with h.  This is exactly the
    Yoneda inverse applied to h, viewed as an element of Hom(y,-)(x). *)
Definition yoneda_embed_mor (C : Category) (x y : cat_obj C) (h : cat_mor C y x) :
  NatTrans C SetoidCat (representable C x) (representable C y) :=
  yoneda_from C x (representable C y) h.

(** Its component sends g : x -> a to g . h : y -> a (precomposition by h) *)
Lemma yoneda_embed_mor_component : forall (C : Category) (x y : cat_obj C)
  (h : cat_mor C y x) (a : cat_obj C) (g : cat_mor C x a),
  st_eq (sm_map (nt_comp (yoneda_embed_mor C x y h) a) g) (cat_comp C y x a g h).
Proof.
  intros C x y h a g. simpl. apply cat_mor_eq_refl.
Qed.

(* ================================================================= *)
(*  Faithful: the embedding is injective on morphisms (up to ~)      *)
(* ================================================================= *)

Lemma yoneda_faithful : forall (C : Category) (x y : cat_obj C)
  (h h' : cat_mor C y x),
  (forall (a : cat_obj C) (g : cat_mor C x a),
     st_eq (sm_map (nt_comp (yoneda_embed_mor C x y h) a) g)
           (sm_map (nt_comp (yoneda_embed_mor C x y h') a) g)) ->
  cat_mor_eq C y x h h'.
Proof.
  intros C x y h h' Heq.
  (* h ~ Y(embed h) ~ Y(embed h') ~ h'  *)
  apply (cat_mor_eq_trans C y x h
           (yoneda_to C x (representable C y) (yoneda_embed_mor C x y h))).
  - apply cat_mor_eq_sym. apply (yoneda_to_from C x (representable C y) h).
  - apply (cat_mor_eq_trans C y x
             (yoneda_to C x (representable C y) (yoneda_embed_mor C x y h))
             (yoneda_to C x (representable C y) (yoneda_embed_mor C x y h'))).
    + exact (Heq x (cat_id C x)).
    + apply (yoneda_to_from C x (representable C y) h').
Qed.

(* ================================================================= *)
(*  Full: every natural transformation comes from a morphism         *)
(* ================================================================= *)

Lemma yoneda_full : forall (C : Category) (x y : cat_obj C)
  (alpha : NatTrans C SetoidCat (representable C x) (representable C y)),
  exists h : cat_mor C y x,
    forall (a : cat_obj C) (g : cat_mor C x a),
      st_eq (sm_map (nt_comp (yoneda_embed_mor C x y h) a) g)
            (sm_map (nt_comp alpha a) g).
Proof.
  intros C x y alpha.
  exists (yoneda_to C x (representable C y) alpha).
  intros a g.
  apply (yoneda_from_to C x (representable C y) alpha a g).
Qed.

(* ================================================================= *)
(*  Summary: 3 Qed, 0 Admitted, 0 axioms                            *)
(*    yoneda_embed_mor_component, yoneda_faithful, yoneda_full        *)
(*    (yoneda_embed_mor is a Definition)                             *)
(* ================================================================= *)
