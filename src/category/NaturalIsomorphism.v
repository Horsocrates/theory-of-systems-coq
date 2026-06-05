(** * NaturalIsomorphism.v — Natural isomorphisms as ToS isomorphisms in [C,D]

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: natural transformations that are invertible
    Roles:    a natural iso = an isomorphism IN the functor category [C,D]
    Rules:    reflexivity / symmetry / transitivity inherited from is_iso;
              the inverse components are AUTOMATICALLY natural (the crown)
    Status:   natural iso <-> componentwise iso (with naturality of the inverse)

    Builds on: stdlib/Category.v, stdlib/Functor.v, category/FunctorCategory.v.

    Design: a natural isomorphism between F, G : C -> D is exactly an
    isomorphism in the functor category [C,D].  So refl/sym/trans come for
    free from the generic is_iso lemmas (iso_refl/iso_sym/iso_trans) applied
    to FunctorCat C D.  The substantive content is the converse bridge:
    if a natural transformation is a *pointwise* isomorphism, then the chosen
    inverse components are themselves natural — "the inverse of a natural
    isomorphism is natural" (natural_inverse_is_natural).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import category.FunctorCategory.

(* ================================================================= *)
(*  Natural isomorphism = isomorphism in the functor category        *)
(* ================================================================= *)

Definition NaturalIso (C D : Category) (F G : Functor C D)
  (eta : NatTrans C D F G) : Prop :=
  is_iso (FunctorCat C D) F G eta.

(* ----- refl / sym / trans inherited from is_iso on [C,D] ----- *)

(** The identity natural transformation is a natural isomorphism *)
Lemma nat_iso_id : forall (C D : Category) (F : Functor C D),
  NaturalIso C D F F (id_nat_trans C D F).
Proof.
  intros C D F. exact (iso_refl (FunctorCat C D) F).
Qed.

(** A natural isomorphism has a natural-isomorphism inverse *)
Lemma nat_iso_sym : forall (C D : Category) (F G : Functor C D)
  (eta : NatTrans C D F G),
  NaturalIso C D F G eta -> exists delta, NaturalIso C D G F delta.
Proof.
  intros C D F G eta H. exact (iso_sym (FunctorCat C D) F G eta H).
Qed.

(** Natural isomorphisms compose (vertically) *)
Lemma nat_iso_trans : forall (C D : Category) (F G H : Functor C D)
  (eta : NatTrans C D F G) (theta : NatTrans C D G H),
  NaturalIso C D F G eta -> NaturalIso C D G H theta ->
  NaturalIso C D F H (vert_comp_nat_trans C D F G H eta theta).
Proof.
  intros C D F G H eta theta Heta Htheta.
  exact (iso_trans (FunctorCat C D) F G H eta theta Heta Htheta).
Qed.

(* ----- natural iso => pointwise iso (and mono, epi) ----- *)

(** A natural isomorphism is a pointwise (componentwise) isomorphism *)
Lemma nat_iso_components : forall (C D : Category) (F G : Functor C D)
  (eta : NatTrans C D F G),
  NaturalIso C D F G eta ->
  forall a, is_iso D (fobj F a) (fobj G a) (nt_comp eta a).
Proof.
  intros C D F G eta H a. apply (FunctorCat_iso_componentwise C D F G eta H).
Qed.

(** Each component of a natural isomorphism is monic *)
Lemma nat_iso_component_mono : forall (C D : Category) (F G : Functor C D)
  (eta : NatTrans C D F G),
  NaturalIso C D F G eta ->
  forall a, is_mono D (fobj F a) (fobj G a) (nt_comp eta a).
Proof.
  intros C D F G eta H a. apply iso_is_mono. apply nat_iso_components. exact H.
Qed.

(** Each component of a natural isomorphism is epic *)
Lemma nat_iso_component_epi : forall (C D : Category) (F G : Functor C D)
  (eta : NatTrans C D F G),
  NaturalIso C D F G eta ->
  forall a, is_epi D (fobj F a) (fobj G a) (nt_comp eta a).
Proof.
  intros C D F G eta H a. apply iso_is_epi. apply nat_iso_components. exact H.
Qed.

(* ================================================================= *)
(*  CROWN: the inverse of a natural isomorphism is natural           *)
(* ================================================================= *)

(** If [eta : F => G] has componentwise two-sided inverses [inv a], then the
    family [inv] is itself natural.  This is the heart of "a pointwise iso of
    functors is a natural iso": one need not assume the inverse natural — it
    is forced by the naturality of [eta] and the inverse equations. *)
Lemma natural_inverse_is_natural :
  forall (C D : Category) (F G : Functor C D) (eta : NatTrans C D F G)
    (inv : forall a, cat_mor D (fobj G a) (fobj F a)),
  (forall a, cat_mor_eq D (fobj G a) (fobj G a)
     (cat_comp D (fobj G a) (fobj F a) (fobj G a) (nt_comp eta a) (inv a))
     (cat_id D (fobj G a))) ->
  (forall a, cat_mor_eq D (fobj F a) (fobj F a)
     (cat_comp D (fobj F a) (fobj G a) (fobj F a) (inv a) (nt_comp eta a))
     (cat_id D (fobj F a))) ->
  forall a b (h : cat_mor C a b),
    cat_mor_eq D (fobj G a) (fobj F b)
      (cat_comp D (fobj G a) (fobj G b) (fobj F b) (inv b) (fmor G h))
      (cat_comp D (fobj G a) (fobj F a) (fobj F b) (fmor F h) (inv a)).
Proof.
  intros C D F G eta inv Hei Hie a b h.
  set (Fa := fobj F a). set (Fb := fobj F b).
  set (Ga := fobj G a). set (Gb := fobj G b).
  set (Fh := fmor F h). set (Gh := fmor G h).
  set (ea := nt_comp eta a). set (eb := nt_comp eta b).
  set (ia := inv a). set (ib := inv b).
  (* goal: ib . Gh == Fh . ia  (both Ga -> Fb).  Prove via reversed chain. *)
  apply cat_mor_eq_sym.
  (* now: Fh . ia == ib . Gh *)
  (* M1: Fh.ia == (id_Fb . Fh).ia *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Fa Fb Fh ia)
    (cat_comp D Ga Fa Fb (cat_comp D Fa Fb Fb (cat_id D Fb) Fh) ia)
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_comp_compat; [ apply cat_mor_eq_sym; apply cat_id_l | apply cat_mor_eq_refl ]. }
  (* M2: replace id_Fb by ib.eb  (Hie b: ib.eb = id_Fb) *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Fa Fb (cat_comp D Fa Fb Fb (cat_id D Fb) Fh) ia)
    (cat_comp D Ga Fa Fb (cat_comp D Fa Fb Fb (cat_comp D Fb Gb Fb ib eb) Fh) ia)
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_comp_compat; [ | apply cat_mor_eq_refl ].
    apply cat_comp_compat; [ apply cat_mor_eq_sym; apply (Hie b) | apply cat_mor_eq_refl ]. }
  (* M3: (ib.eb).Fh == ib.(eb.Fh)  by sym assoc *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Fa Fb (cat_comp D Fa Fb Fb (cat_comp D Fb Gb Fb ib eb) Fh) ia)
    (cat_comp D Ga Fa Fb (cat_comp D Fa Gb Fb ib (cat_comp D Fa Fb Gb eb Fh)) ia)
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_comp_compat; [ | apply cat_mor_eq_refl ].
    apply cat_mor_eq_sym. apply (cat_assoc D Fa Fb Gb Fb Fh eb ib). }
  (* M4: eb.Fh == Gh.ea  (naturality of eta) *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Fa Fb (cat_comp D Fa Gb Fb ib (cat_comp D Fa Fb Gb eb Fh)) ia)
    (cat_comp D Ga Fa Fb (cat_comp D Fa Gb Fb ib (cat_comp D Fa Ga Gb Gh ea)) ia)
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_comp_compat; [ | apply cat_mor_eq_refl ].
    apply cat_comp_compat; [ apply cat_mor_eq_refl | apply (nt_natural eta h) ]. }
  (* M5: ib.(Gh.ea) == (ib.Gh).ea  by assoc *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Fa Fb (cat_comp D Fa Gb Fb ib (cat_comp D Fa Ga Gb Gh ea)) ia)
    (cat_comp D Ga Fa Fb (cat_comp D Fa Ga Fb (cat_comp D Ga Gb Fb ib Gh) ea) ia)
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_comp_compat; [ | apply cat_mor_eq_refl ].
    apply (cat_assoc D Fa Ga Gb Fb ea Gh ib). }
  (* M6: ((ib.Gh).ea).ia == (ib.Gh).(ea.ia)  by sym assoc *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Fa Fb (cat_comp D Fa Ga Fb (cat_comp D Ga Gb Fb ib Gh) ea) ia)
    (cat_comp D Ga Ga Fb (cat_comp D Ga Gb Fb ib Gh) (cat_comp D Ga Fa Ga ea ia))
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_mor_eq_sym.
    apply (cat_assoc D Ga Fa Ga Fb ia ea (cat_comp D Ga Gb Fb ib Gh)). }
  (* M7: ea.ia == id_Ga  (Hei a) *)
  apply (cat_mor_eq_trans D Ga Fb
    (cat_comp D Ga Ga Fb (cat_comp D Ga Gb Fb ib Gh) (cat_comp D Ga Fa Ga ea ia))
    (cat_comp D Ga Ga Fb (cat_comp D Ga Gb Fb ib Gh) (cat_id D Ga))
    (cat_comp D Ga Gb Fb ib Gh)).
  { apply cat_comp_compat; [ apply cat_mor_eq_refl | apply (Hei a) ]. }
  (* M8: (ib.Gh).id_Ga == ib.Gh  by id_r *)
  apply (cat_id_r D Ga Fb (cat_comp D Ga Gb Fb ib Gh)).
Qed.

(* ================================================================= *)
(*  Summary: 8 Qed, 0 Admitted, 0 axioms                            *)
(*    nat_iso_id, nat_iso_sym, nat_iso_trans                          *)
(*    nat_iso_components, nat_iso_component_mono, nat_iso_component_epi*)
(*    natural_inverse_is_natural (crown)                              *)
(* ================================================================= *)
