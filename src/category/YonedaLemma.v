(** * YonedaLemma.v — The Yoneda lemma as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: morphisms g : x -> a, elements u of F(x), natural transformations
              Hom(x,-) => F, and the representable functor Hom(x,-) itself
    Roles:    Hom(x,-) = "probing C from x"; a natural transformation = a coherent
              family of probes; alpha_x(id_x) = the distinguished representative;
              the Yoneda map Y = "evaluate the family at the identity"
    Rules:    the bijection Nat(Hom(x,-),F) ~= F(x) is GOVERNED BY NATURALITY:
              the naturality square forces alpha_a(g) = F(g)(alpha_x(id_x)), so the
              whole family collapses to one element (constitution)
    Status:   Yoneda map both ways; both round-trips; Yoneda uniqueness

    P4 diagnostic.  "The set of all natural transformations" is not a completed
    object; the content is the FINITE reconstruction rule g |-> F(g)(u) from one
    seed u = alpha_x(id_x).  The Yoneda lemma is a role-level identification (a
    reconstruction process), not a claim about a completed set's cardinality.
    It dissolves the puzzle "how can one element know the whole natural family":
    naturality is the law, the element is the seed.  This is the categorical form
    of "an object is determined by its morphisms" (kin to P3).

    Builds on: stdlib/Category.v, stdlib/Functor.v, category/SetoidCategory.v.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import category.SetoidCategory.

(* ================================================================= *)
(*  The hom-setoid and the representable functor Hom(x,-)            *)
(* ================================================================= *)

(** The hom-set cat_mor C x a, with cat_mor_eq as its equivalence *)
Definition hom_setoid (C : Category) (x a : cat_obj C) : Setoid :=
  mkSetoid (cat_mor C x a) (cat_mor_eq C x a)
    (cat_mor_eq_refl C x a) (cat_mor_eq_sym C x a) (cat_mor_eq_trans C x a).

(** The covariant representable functor Hom(x,-) : C -> SetoidCat,
    acting on morphisms by post-composition. *)
Definition representable (C : Category) (x : cat_obj C) : Functor C SetoidCat.
Proof.
  apply (mkFunctor C SetoidCat
    (fun a => hom_setoid C x a)
    (fun a b (f : cat_mor C a b) =>
       mkSetoidMor (hom_setoid C x a) (hom_setoid C x b)
         (fun g => cat_comp C x a b f g)
         (fun g g' (H : cat_mor_eq C x a g g') =>
            cat_comp_compat C x a b f f g g' (cat_mor_eq_refl C a b f) H))).
  - (* fmor_compat *)
    intros a b f f' Hff'. intro g. simpl.
    apply cat_comp_compat; [ exact Hff' | apply cat_mor_eq_refl ].
  - (* fmor_id *)
    intros a. intro g. simpl. apply cat_id_l.
  - (* fmor_comp *)
    intros a b c f g0. intro k. simpl.
    apply cat_mor_eq_sym. apply (cat_assoc C x a b c k f g0).
Defined.

(* ================================================================= *)
(*  The Yoneda maps                                                  *)
(* ================================================================= *)

(** Y : Nat(Hom(x,-), F) -> F x,  alpha |-> alpha_x(id_x) *)
Definition yoneda_to (C : Category) (x : cat_obj C) (F : Functor C SetoidCat)
  (alpha : NatTrans C SetoidCat (representable C x) F) : st_carrier (fobj F x) :=
  sm_map (nt_comp alpha x) (cat_id C x).

(** Y^{-1} : F x -> Nat(Hom(x,-), F),  u |-> (a |-> (g |-> F(g)(u))) *)
Definition yoneda_from (C : Category) (x : cat_obj C) (F : Functor C SetoidCat)
  (u : st_carrier (fobj F x)) : NatTrans C SetoidCat (representable C x) F.
Proof.
  apply (mkNatTrans C SetoidCat (representable C x) F
    (fun a => mkSetoidMor (hom_setoid C x a) (fobj F a)
       (fun g => sm_map (fmor F g) u)
       (fun g g' (H : cat_mor_eq C x a g g') => fmor_compat F g g' H u))).
  (* naturality: F(h.k)(u) = F(h)(F(k)(u)) *)
  intros a b h. intro k. simpl. exact (fmor_comp F k h u).
Defined.

(* ================================================================= *)
(*  Yoneda lemma: Y and Y^{-1} are mutually inverse                  *)
(* ================================================================= *)

(** Y . Y^{-1} = id :  evaluating the reconstructed family at id_x gives u back
    (via F(id_x) = id) *)
Lemma yoneda_to_from : forall (C : Category) (x : cat_obj C)
  (F : Functor C SetoidCat) (u : st_carrier (fobj F x)),
  st_eq (yoneda_to C x F (yoneda_from C x F u)) u.
Proof.
  intros C x F u. unfold yoneda_to. simpl.
  apply (fmor_id F x).
Qed.

(** Y^{-1} . Y = id :  the family reconstructed from alpha_x(id_x) is alpha
    (componentwise), by naturality of alpha *)
Lemma yoneda_from_to : forall (C : Category) (x : cat_obj C)
  (F : Functor C SetoidCat)
  (alpha : NatTrans C SetoidCat (representable C x) F)
  (a : cat_obj C) (k : cat_mor C x a),
  st_eq (sm_map (nt_comp (yoneda_from C x F (yoneda_to C x F alpha)) a) k)
        (sm_map (nt_comp alpha a) k).
Proof.
  intros C x F alpha a k. simpl.
  apply (st_trans (y := sm_map (nt_comp alpha a) (cat_comp C x x a k (cat_id C x)))).
  - apply st_sym. exact (nt_natural alpha k (cat_id C x)).
  - apply (sm_resp (nt_comp alpha a)). apply (cat_id_r C x a k).
Qed.

(** Yoneda uniqueness: a natural transformation Hom(x,-) => F is determined by
    its value at id_x.  If two have equal Yoneda images, they agree everywhere. *)
Lemma yoneda_unique : forall (C : Category) (x : cat_obj C)
  (F : Functor C SetoidCat)
  (alpha beta : NatTrans C SetoidCat (representable C x) F),
  st_eq (yoneda_to C x F alpha) (yoneda_to C x F beta) ->
  forall (a : cat_obj C) (k : cat_mor C x a),
    st_eq (sm_map (nt_comp alpha a) k) (sm_map (nt_comp beta a) k).
Proof.
  intros C x F alpha beta Hxy a k.
  (* alpha_a(k) ~ F(k)(Y alpha) ~ F(k)(Y beta) ~ beta_a(k) *)
  apply (st_trans (y := sm_map (fmor F k) (yoneda_to C x F alpha))).
  - apply st_sym. apply (yoneda_from_to C x F alpha a k).
  - apply (st_trans (y := sm_map (fmor F k) (yoneda_to C x F beta))).
    + apply (sm_resp (fmor F k)). exact Hxy.
    + apply (yoneda_from_to C x F beta a k).
Qed.

(* ================================================================= *)
(*  Summary: 3 Qed, 0 Admitted, 0 axioms                            *)
(*    yoneda_to_from, yoneda_from_to, yoneda_unique                  *)
(*    (hom_setoid, representable, yoneda_to, yoneda_from are defs)    *)
(* ================================================================= *)
