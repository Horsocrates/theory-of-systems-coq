(** * EquivalenceOfCategories.v — Equivalence of categories as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: two functors with explicit inverse unit/counit transformations
    Roles:    ce_F / ce_G -> the two directions; unit/counit + their inverses
    Rules:    the four round-trips hold componentwise (constitution)
    Status:   unit and counit are natural isomorphisms; equivalence is
              symmetric; an equivalence is essentially surjective both ways

    Builds on: stdlib/Category.v, stdlib/Functor.v, category/FunctorCategory.v,
               category/NaturalIsomorphism.v.

    Design note: the inverses of unit and counit are carried as DATA (natural
    transformations) with the round-trip equations as Prop fields, rather than
    a bare "NaturalIso" (which is an existential, Prop).  This keeps the witness
    constructive, so the symmetric equivalence D ~= C is a pure permutation of
    fields — no extraction of data from a proof.

    An equivalence C ~= D is weaker than an isomorphism of categories: we do NOT
    require G.F = id on the nose, only id_C ~= G.F and F.G ~= id_D — "same up to
    role", the categorical echo of P3 (isomorphism is not Leibniz equality).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import category.FunctorCategory.
From ToS Require Import category.NaturalIsomorphism.

(* ================================================================= *)
(*  Equivalence of categories (with explicit inverses)               *)
(* ================================================================= *)

Record CatEquiv (C D : Category) := mkCatEquiv {
  ce_F : Functor C D;
  ce_G : Functor D C;
  ce_unit       : NatTrans C C (id_functor C) (compose_functor C D C ce_G ce_F);
  ce_unit_inv   : NatTrans C C (compose_functor C D C ce_G ce_F) (id_functor C);
  ce_counit     : NatTrans D D (compose_functor D C D ce_F ce_G) (id_functor D);
  ce_counit_inv : NatTrans D D (id_functor D) (compose_functor D C D ce_F ce_G);
  (* unit . unit_inv = id  (on G.F) *)
  ce_unit_sect : forall a,
    cat_mor_eq C _ _
      (cat_comp C _ _ _ (nt_comp ce_unit a) (nt_comp ce_unit_inv a))
      (cat_id C (fobj (compose_functor C D C ce_G ce_F) a));
  (* unit_inv . unit = id  (on id_C) *)
  ce_unit_retr : forall a,
    cat_mor_eq C a a
      (cat_comp C _ _ _ (nt_comp ce_unit_inv a) (nt_comp ce_unit a))
      (cat_id C a);
  (* counit . counit_inv = id  (on id_D) *)
  ce_counit_sect : forall d,
    cat_mor_eq D d d
      (cat_comp D _ _ _ (nt_comp ce_counit d) (nt_comp ce_counit_inv d))
      (cat_id D d);
  (* counit_inv . counit = id  (on F.G) *)
  ce_counit_retr : forall d,
    cat_mor_eq D _ _
      (cat_comp D _ _ _ (nt_comp ce_counit_inv d) (nt_comp ce_counit d))
      (cat_id D (fobj (compose_functor D C D ce_F ce_G) d));
}.

Arguments ce_F {C D} _.
Arguments ce_G {C D} _.
Arguments ce_unit {C D} _.
Arguments ce_unit_inv {C D} _.
Arguments ce_counit {C D} _.
Arguments ce_counit_inv {C D} _.
Arguments ce_unit_sect {C D} _ _.
Arguments ce_unit_retr {C D} _ _.
Arguments ce_counit_sect {C D} _ _.
Arguments ce_counit_retr {C D} _ _.

(* ================================================================= *)
(*  Unit and counit are natural isomorphisms                         *)
(* ================================================================= *)

Lemma ce_unit_is_nat_iso : forall (C D : Category) (E : CatEquiv C D),
  NaturalIso C C (id_functor C) (compose_functor C D C (ce_G E) (ce_F E)) (ce_unit E).
Proof.
  intros C D E. exists (ce_unit_inv E). split.
  - intro a. simpl. apply (ce_unit_retr E).
  - intro a. simpl. apply (ce_unit_sect E).
Qed.

Lemma ce_counit_is_nat_iso : forall (C D : Category) (E : CatEquiv C D),
  NaturalIso D D (compose_functor D C D (ce_F E) (ce_G E)) (id_functor D) (ce_counit E).
Proof.
  intros C D E. exists (ce_counit_inv E). split.
  - intro d. simpl. apply (ce_counit_retr E).
  - intro d. simpl. apply (ce_counit_sect E).
Qed.

(* ================================================================= *)
(*  Functor properties                                               *)
(* ================================================================= *)

Definition is_ess_surjective (C D : Category) (F : Functor C D) : Prop :=
  forall d : cat_obj D, exists (c : cat_obj C) (f : cat_mor D (fobj F c) d),
    is_iso D (fobj F c) d f.

Definition is_faithful (C D : Category) (F : Functor C D) : Prop :=
  forall a b (f g : cat_mor C a b),
    cat_mor_eq D (fobj F a) (fobj F b) (fmor F f) (fmor F g) ->
    cat_mor_eq C a b f g.

Definition is_full (C D : Category) (F : Functor C D) : Prop :=
  forall a b (h : cat_mor D (fobj F a) (fobj F b)),
    exists f : cat_mor C a b,
      cat_mor_eq D (fobj F a) (fobj F b) (fmor F f) h.

(* ----- pointwise iso of unit/counit ----- *)

Lemma equiv_counit_components_iso : forall (C D : Category) (E : CatEquiv C D)
  (d : cat_obj D),
  is_iso D (fobj (ce_F E) (fobj (ce_G E) d)) d (nt_comp (ce_counit E) d).
Proof.
  intros C D E d.
  apply (nat_iso_components D D
    (compose_functor D C D (ce_F E) (ce_G E)) (id_functor D)
    (ce_counit E) (ce_counit_is_nat_iso C D E) d).
Qed.

Lemma equiv_unit_components_iso : forall (C D : Category) (E : CatEquiv C D)
  (c : cat_obj C),
  is_iso C c (fobj (ce_G E) (fobj (ce_F E) c)) (nt_comp (ce_unit E) c).
Proof.
  intros C D E c.
  apply (nat_iso_components C C
    (id_functor C) (compose_functor C D C (ce_G E) (ce_F E))
    (ce_unit E) (ce_unit_is_nat_iso C D E) c).
Qed.

(* ----- essential surjectivity in both directions ----- *)

Lemma equiv_F_ess_surjective : forall (C D : Category) (E : CatEquiv C D),
  is_ess_surjective C D (ce_F E).
Proof.
  intros C D E d.
  exists (fobj (ce_G E) d). exists (nt_comp (ce_counit E) d).
  apply equiv_counit_components_iso.
Qed.

Lemma equiv_G_ess_surjective : forall (C D : Category) (E : CatEquiv C D),
  is_ess_surjective D C (ce_G E).
Proof.
  intros C D E c.
  destruct (iso_sym C c (fobj (ce_G E) (fobj (ce_F E) c))
    (nt_comp (ce_unit E) c) (equiv_unit_components_iso C D E c)) as [g Hg].
  exists (fobj (ce_F E) c). exists g. exact Hg.
Qed.

(* ================================================================= *)
(*  Symmetry: swap F<->G, unit<->counit (a pure field permutation)   *)
(* ================================================================= *)

Definition equiv_sym (C D : Category) (E : CatEquiv C D) : CatEquiv D C :=
  mkCatEquiv D C
    (ce_G E) (ce_F E)
    (ce_counit_inv E) (ce_counit E)
    (ce_unit_inv E)   (ce_unit E)
    (ce_counit_retr E) (ce_counit_sect E)
    (ce_unit_retr E)   (ce_unit_sect E).

(* ================================================================= *)
(*  ce_F (and ce_G) preserve isomorphisms                            *)
(* ================================================================= *)

Lemma equiv_F_preserves_iso : forall (C D : Category) (E : CatEquiv C D)
  (a b : cat_obj C) (f : cat_mor C a b),
  is_iso C a b f ->
  is_iso D (fobj (ce_F E) a) (fobj (ce_F E) b) (fmor (ce_F E) f).
Proof.
  intros C D E a b f Hf.
  apply (fmor_preserves_iso C D (ce_F E) a b f Hf).
Qed.

(* ================================================================= *)
(*  Summary: 7 Qed, 0 Admitted, 0 axioms                            *)
(*    ce_unit_is_nat_iso, ce_counit_is_nat_iso                        *)
(*    equiv_counit_components_iso, equiv_unit_components_iso          *)
(*    equiv_F_ess_surjective, equiv_G_ess_surjective                 *)
(*    equiv_F_preserves_iso                                           *)
(*  (equiv_sym is a Definition; is_ess_surjective/faithful/full defs) *)
(* ================================================================= *)
