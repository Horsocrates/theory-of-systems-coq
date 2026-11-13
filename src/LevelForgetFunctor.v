(** * LevelForgetFunctor.v — Forgetting a level as a FUNCTOR, and the
      adjunction embed -| forget as a record

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, chapter I.1, 2026-11-13):

    Elements: systems of level L (objects of [SystemCat L]); FORGETTABLE
              systems of level LS L (objects of a full subcategory of
              [SystemCat (LS L)]); morphisms between them.
    Roles:    [is_forgettable] — the role that admits a system of the upper
              level to the passage down; embedding and forgetting — the two
              directions of the passage between adjacent levels; unit and
              counit — the two comparisons after a round trip.
    Rules:    (1) forgettable systems form a category (a full subcategory);
              (2) forgetting is a functor on it — identity, composition and
                  respect of morphism equality hold;
              (3) embedding lands in the forgettable systems and is a
                  functor into that category;
              (4) forgetting after embedding returns the same system;
              (5) embedding is LEFT adjoint to forgetting: an [Adjunction]
                  record whose two triangle identities hold, with natural
                  unit and counit and a bijection of morphism sets;
              (6) the restriction to forgettable systems is forced: on the
                  first step there is no functor at all from
                  [SystemCat (LS L1)] to [SystemCat L1], and on every step
                  some system is not forgettable.
    P4 diagnostic ("could it be otherwise?"): nothing infinite is used.
              Forced: the restriction of forgetting to a subcategory (P1
              obstructs total forgetting). Not forced: nothing is chosen —
              the subcategory is cut out by a decidable predicate.

    Before this file the passage down was given by lemmas with an explicit
    forgettability hypothesis (LevelFunctors.v, LevelAdjunction.v), and
    "we cannot form a proper Functor instance for it" was true of the whole
    category [SystemCat (LS L)]. Here the functor is formed on the part of
    that category where forgetting is defined.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import UniversePolymorphism.
From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import stdlib.Adjunction.
From ToS Require Import SystemCategory.
From ToS Require Import LevelFunctors.
From ToS Require Import LevelAdjunction.

(* ========================================================================= *)
(*  1. THE CATEGORY OF FORGETTABLE SYSTEMS                                   *)
(* ========================================================================= *)

(** The full subcategory of a category C on the objects with property P:
    objects are pairs (object, proof of P); morphisms, their equality,
    identities and composition are those of C. *)
Definition full_subcat (C : Category) (P : cat_obj C -> Prop) : Category :=
  mkCategory
    { a : cat_obj C | P a }
    (fun a b => cat_mor C (proj1_sig a) (proj1_sig b))
    (fun a b => cat_mor_eq C (proj1_sig a) (proj1_sig b))
    (fun a => cat_id C (proj1_sig a))
    (fun a b c => cat_comp C (proj1_sig a) (proj1_sig b) (proj1_sig c))
    (fun a b => cat_mor_eq_refl C (proj1_sig a) (proj1_sig b))
    (fun a b => cat_mor_eq_sym C (proj1_sig a) (proj1_sig b))
    (fun a b => cat_mor_eq_trans C (proj1_sig a) (proj1_sig b))
    (fun a b c => cat_comp_compat C (proj1_sig a) (proj1_sig b) (proj1_sig c))
    (fun a b c d => cat_assoc C (proj1_sig a) (proj1_sig b) (proj1_sig c) (proj1_sig d))
    (fun a b => cat_id_l C (proj1_sig a) (proj1_sig b))
    (fun a b => cat_id_r C (proj1_sig a) (proj1_sig b)).

(** Forgettable systems of level LS L. *)
Definition ForgettableCat (L : Level) : Category :=
  full_subcat (SystemCat (LS L)) (is_forgettable L).

(* ========================================================================= *)
(*  2. THE TWO FUNCTORS                                                      *)
(* ========================================================================= *)

(** Forgetting: a functor from forgettable systems of level LS L to systems
    of level L. *)
Definition ForgetFunctor (L : Level) : Functor (ForgettableCat L) (SystemCat L).
Proof.
  apply (mkFunctor (ForgettableCat L) (SystemCat L)
    (fun A => forget_obj L (proj1_sig A) (proj2_sig A))
    (fun A B f => forget_mor L (proj1_sig A) (proj1_sig B)
                    (proj2_sig A) (proj2_sig B) f)).
  - intros A B f g Heq. apply forget_mor_compat. exact Heq.
  - intros A. apply forget_mor_id.
  - intros A B C f g. simpl. apply forget_mor_comp.
Defined.

(** Embedding lands in the forgettable systems: a functor from systems of
    level L to forgettable systems of level LS L. *)
Definition EmbedToForgettable (L : Level) : Functor (SystemCat L) (ForgettableCat L).
Proof.
  apply (mkFunctor (SystemCat L) (ForgettableCat L)
    (fun S => exist _ (embed_obj L S) (embed_is_forgettable L S))
    (fun S1 S2 (f : SystemMorphism L S1 S2) => embed_mor L S1 S2 f)).
  - intros S1 S2 f g Heq. apply embed_mor_compat. exact Heq.
  - intros S. apply embed_mor_id.
  - intros S1 S2 S3 f g. simpl. apply embed_mor_comp.
Defined.

(** Forgetting after embedding returns the same system. *)
Theorem Forget_Embed_obj : forall (L : Level) (S : System L),
  fobj (ForgetFunctor L) (fobj (EmbedToForgettable L) S) = S.
Proof. intros L S. simpl. apply forget_embed_roundtrip. Qed.

(** The embedding into forgettable systems is the old embedding followed by
    the inclusion of the subcategory: on objects it is [embed_obj]. *)
Theorem EmbedToForgettable_obj : forall (L : Level) (S : System L),
  proj1_sig (fobj (EmbedToForgettable L) S) = embed_obj L S.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*  3. THE ADJUNCTION embed -| forget                                        *)
(* ========================================================================= *)

(** Embedding on the left, forgetting on the right; unit and counit are the
    components already defined in LevelAdjunction.v. *)
Definition LevelAdj (L : Level) : Adjunction (SystemCat L) (ForgettableCat L) :=
  mkAdj (SystemCat L) (ForgettableCat L)
    (EmbedToForgettable L)
    (ForgetFunctor L)
    (fun S => adjunction_unit_component L S)
    (fun T => adjunction_counit_component L (proj1_sig T) (proj2_sig T)).

(** Both triangle identities hold: the record is an adjunction. *)
Theorem level_adj_is_adjunction : forall L : Level, is_adjunction (LevelAdj L).
Proof.
  intro L. split.
  - unfold triangle_left. intro S. cbv zeta. simpl.
    intro e. reflexivity.
  - unfold triangle_right. intro T. cbv zeta. simpl.
    intro e. reflexivity.
Qed.

(** The unit is natural. *)
Theorem level_adj_unit_natural : forall (L : Level) (S1 S2 : System L)
  (f : cat_mor (SystemCat L) S1 S2),
  cat_mor_eq (SystemCat L) S1
    (fobj (ForgetFunctor L) (fobj (EmbedToForgettable L) S2))
    (cat_comp (SystemCat L) _ _ _
       (fmor (ForgetFunctor L) (fmor (EmbedToForgettable L) f))
       (adj_unit (LevelAdj L) S1))
    (cat_comp (SystemCat L) _ _ _
       (adj_unit (LevelAdj L) S2) f).
Proof. intros L S1 S2 f e. reflexivity. Qed.

(** The counit is natural. *)
Theorem level_adj_counit_natural : forall (L : Level)
  (T1 T2 : cat_obj (ForgettableCat L))
  (k : cat_mor (ForgettableCat L) T1 T2),
  cat_mor_eq (ForgettableCat L)
    (fobj (EmbedToForgettable L) (fobj (ForgetFunctor L) T1)) T2
    (cat_comp (ForgettableCat L)
       (fobj (EmbedToForgettable L) (fobj (ForgetFunctor L) T1)) T1 T2
       k (adj_counit (LevelAdj L) T1))
    (cat_comp (ForgettableCat L)
       (fobj (EmbedToForgettable L) (fobj (ForgetFunctor L) T1))
       (fobj (EmbedToForgettable L) (fobj (ForgetFunctor L) T2)) T2
       (adj_counit (LevelAdj L) T2)
       (fmor (EmbedToForgettable L) (fmor (ForgetFunctor L) k))).
Proof. intros L T1 T2 k e. reflexivity. Qed.

(** The adjunction as a bijection of morphism sets:
    Hom(embed S, T) ~ Hom(S, forget T), T forgettable. *)
Theorem embed_forget_hom_bijection : forall (L : Level) (S : System L)
  (T : cat_obj (ForgettableCat L)),
  (forall f : cat_mor (ForgettableCat L) (fobj (EmbedToForgettable L) S) T,
     cat_mor_eq (ForgettableCat L) (fobj (EmbedToForgettable L) S) T
       (adj_backward L S (proj1_sig T) (proj2_sig T)
          (adj_forward L S (proj1_sig T) (proj2_sig T) f)) f) /\
  (forall g : cat_mor (SystemCat L) S (fobj (ForgetFunctor L) T),
     cat_mor_eq (SystemCat L) S (fobj (ForgetFunctor L) T)
       (adj_forward L S (proj1_sig T) (proj2_sig T)
          (adj_backward L S (proj1_sig T) (proj2_sig T) g)) g).
Proof.
  intros L S T. exact (level_adjunction L S (proj1_sig T) (proj2_sig T)).
Qed.

(* ========================================================================= *)
(*  4. THE RESTRICTION IS FORCED                                             *)
(* ========================================================================= *)

(** On the first step there is no functor at all from the whole category of
    systems of level LS L1 down to level L1: the base category has no
    objects, and the upper one has. *)
Theorem no_functor_to_base :
  forall F : Functor (SystemCat (LS L1)) (SystemCat L1), False.
Proof.
  intro F.
  pose (S := fobj F (unit_system (LS L1) L1 (level_lt_LS L1))).
  exact (L1_criterion_absurd (sys_criterion L1 S)).
Qed.

(** On every step the subcategory is proper: some system of level LS L is
    not an object of [ForgettableCat L]. (P1_obstructs_total_forget, restated
    for the subcategory.) *)
Theorem forgettable_subcategory_is_proper : forall L : Level,
  exists S : System (LS L),
    ~ exists A : cat_obj (ForgettableCat L), proj1_sig A = S.
Proof.
  intro L. destruct (P1_obstructs_total_forget L) as [S HS].
  exists S. intros [A HA]. apply HS. rewrite <- HA. exact (proj2_sig A).
Qed.
