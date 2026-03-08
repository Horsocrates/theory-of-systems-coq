(** * LevelAdjunction.v — The Level Adjunction: forget -| embed

    Proves the adjunction between the embedding and forgetful functors
    restricted to forgettable systems: forget -| embed (left adjoint -| right adjoint).

    Elements: Systems at levels L and LS L, morphisms between them
    Roles:    embed -> Right Adjoint, forget -> Left Adjoint (restricted)
    Rules:    hom-set bijection, unit/counit, triangle identities
    Status:   adjunction properties verified pointwise (partial adjunction)

    KEY INSIGHT:
    Since forget is partial (requires is_forgettable), we cannot form a
    proper Functor instance for it. Instead, we prove all adjunction
    properties as standalone lemmas with explicit forgettability hypotheses.

    The adjunction is "tight": the unit eta is an iso, making embed
    fully faithful (which we already know from LevelFunctors.v).

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import UniversePolymorphism.
From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import SystemCategory.
From ToS Require Import LevelFunctors.

(* ================================================================= *)
(*  PART I: HOM-SET BIJECTION (8 Qed)                                 *)
(* ================================================================= *)

(** The adjunction bijection forward direction:
    Given f : embed(S) -> T at level LS L, produce g : S -> forget(T) at level L.
    The sm_map is the same function because ElemOf types are definitionally equal:
      ElemOf (LS L) (embed_obj L S) = ElemOf L S  (by embed_obj_elem_eq)
      ElemOf L (forget_obj L T Hf) = ElemOf (LS L) T  (by forget_obj_elem_eq) *)
Definition adj_forward (L : Level) (S : System L) (T : System (LS L))
  (Hf : is_forgettable L T)
  (f : SystemMorphism (LS L) (embed_obj L S) T)
  : SystemMorphism L S (forget_obj L T Hf) :=
  mkSystemMorphism L S (forget_obj L T Hf)
    (sm_map (LS L) (embed_obj L S) T f)
    (sm_preserves (LS L) (embed_obj L S) T f).

(** The adjunction bijection backward direction:
    Given g : S -> forget(T) at level L, produce f : embed(S) -> T at level LS L.
    Again, the sm_map is the same function. *)
Definition adj_backward (L : Level) (S : System L) (T : System (LS L))
  (Hf : is_forgettable L T)
  (g : SystemMorphism L S (forget_obj L T Hf))
  : SystemMorphism (LS L) (embed_obj L S) T :=
  mkSystemMorphism (LS L) (embed_obj L S) T
    (sm_map L S (forget_obj L T Hf) g)
    (sm_preserves L S (forget_obj L T Hf) g).

(** adj_backward . adj_forward acts as identity on elements *)
Lemma adj_forward_backward : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (f : SystemMorphism (LS L) (embed_obj L S) T)
  (e : ElemOf (LS L) (embed_obj L S)),
  sm_map (LS L) (embed_obj L S) T
    (adj_backward L S T Hf (adj_forward L S T Hf f)) e =
  sm_map (LS L) (embed_obj L S) T f e.
Proof.
  intros L S T Hf f e. reflexivity.
Qed.

(** adj_forward . adj_backward acts as identity on elements *)
Lemma adj_backward_forward : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (g : SystemMorphism L S (forget_obj L T Hf))
  (e : ElemOf L S),
  sm_map L S (forget_obj L T Hf)
    (adj_forward L S T Hf (adj_backward L S T Hf g)) e =
  sm_map L S (forget_obj L T Hf) g e.
Proof.
  intros L S T Hf g e. reflexivity.
Qed.

(** Main adjunction theorem: the hom-set bijection is an isomorphism.
    Hom(embed S, T) ~ Hom(S, forget T) via adj_forward/adj_backward. *)
Theorem level_adjunction : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T),
  (forall (f : SystemMorphism (LS L) (embed_obj L S) T),
    morphism_eq (LS L)
      (adj_backward L S T Hf (adj_forward L S T Hf f)) f) /\
  (forall (g : SystemMorphism L S (forget_obj L T Hf)),
    morphism_eq L
      (adj_forward L S T Hf (adj_backward L S T Hf g)) g).
Proof.
  intros L S T Hf. split.
  - intros f e. reflexivity.
  - intros g e. reflexivity.
Qed.

(** Naturality in S: for h : S1 -> S2 at level L,
    adj_forward(f . embed(h)) = adj_forward(f) . h  (pointwise) *)
Lemma adj_natural_S : forall (L : Level) (S1 S2 : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (h : SystemMorphism L S1 S2)
  (f : SystemMorphism (LS L) (embed_obj L S2) T)
  (e : ElemOf L S1),
  sm_map L S1 (forget_obj L T Hf)
    (adj_forward L S1 T Hf
      (compose_morphism (LS L) (embed_mor L S1 S2 h) f)) e =
  sm_map L S1 (forget_obj L T Hf)
    (compose_morphism L h (adj_forward L S2 T Hf f)) e.
Proof.
  intros L S1 S2 T Hf h f e. reflexivity.
Qed.

(** Naturality in T: for k : T1 -> T2 at level LS L (both forgettable),
    adj_forward(k . f) = forget(k) . adj_forward(f)  (pointwise) *)
Lemma adj_natural_T : forall (L : Level) (S : System L)
  (T1 T2 : System (LS L))
  (Hf1 : is_forgettable L T1) (Hf2 : is_forgettable L T2)
  (k : SystemMorphism (LS L) T1 T2)
  (f : SystemMorphism (LS L) (embed_obj L S) T1)
  (e : ElemOf L S),
  sm_map L S (forget_obj L T2 Hf2)
    (adj_forward L S T2 Hf2
      (compose_morphism (LS L) f k)) e =
  sm_map L S (forget_obj L T2 Hf2)
    (compose_morphism L
      (adj_forward L S T1 Hf1 f)
      (forget_mor L T1 T2 Hf1 Hf2 k)) e.
Proof.
  intros L S T1 T2 Hf1 Hf2 k f e. reflexivity.
Qed.

(** The bijection respects morphism_eq on both sides *)
Lemma adj_bijection_compat : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (f1 f2 : SystemMorphism (LS L) (embed_obj L S) T),
  morphism_eq (LS L) f1 f2 ->
  morphism_eq L (adj_forward L S T Hf f1) (adj_forward L S T Hf f2).
Proof.
  intros L S T Hf f1 f2 Heq e. apply Heq.
Qed.

(* ================================================================= *)
(*  PART II: UNIT AND COUNIT (6 Qed)                                   *)
(* ================================================================= *)

(** Unit component: eta_S : S -> forget(embed(S)).
    Since forget(embed(S)) = S by forget_embed_roundtrip (Leibniz equality),
    the unit is essentially the identity. But the types are
    SystemMorphism L S (forget_obj L (embed_obj L S) (embed_is_forgettable L S)),
    not SystemMorphism L S S. We use mkSystemMorphism with the identity map
    since ElemOf types are definitionally equal. *)
Definition adjunction_unit_component (L : Level) (S : System L)
  : SystemMorphism L S (forget_obj L (embed_obj L S) (embed_is_forgettable L S)) :=
  mkSystemMorphism L S
    (forget_obj L (embed_obj L S) (embed_is_forgettable L S))
    (fun e => e)
    (fun e H => H).

(** Unit naturality: for f : S1 -> S2 at level L,
    forget(embed(f)) . eta_S1 ~= eta_S2 . f  (pointwise).
    Both sides compute to f on elements. *)
Lemma adjunction_unit_natural : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (e : ElemOf L S1),
  sm_map L _ _
    (compose_morphism L
      (adjunction_unit_component L S1)
      (forget_mor L (embed_obj L S1) (embed_obj L S2)
        (embed_is_forgettable L S1) (embed_is_forgettable L S2)
        (embed_mor L S1 S2 f))) e =
  sm_map L _ _
    (compose_morphism L f (adjunction_unit_component L S2)) e.
Proof.
  intros L S1 S2 f e. reflexivity.
Qed.

(** The unit component is an isomorphism: eta_S has an inverse.
    Since eta_S is essentially the identity (same map on elements),
    its inverse is also the identity. *)
Lemma adjunction_unit_is_iso : forall (L : Level) (S : System L),
  is_isomorphism L (adjunction_unit_component L S).
Proof.
  intros L S.
  set (eta := adjunction_unit_component L S).
  set (eta_inv := mkSystemMorphism L
    (forget_obj L (embed_obj L S) (embed_is_forgettable L S)) S
    (fun e => e) (fun e H => H)).
  exists eta_inv.
  split.
  - intro e. reflexivity.
  - intro e. reflexivity.
Qed.

(** Counit component: epsilon_T : embed(forget(T)) -> T.
    For a forgettable T, embed(forget(T)) has the same elements as T
    (definitionally). The counit maps elements via the identity function. *)
Definition adjunction_counit_component (L : Level) (T : System (LS L))
  (Hf : is_forgettable L T)
  : SystemMorphism (LS L) (embed_obj L (forget_obj L T Hf)) T :=
  mkSystemMorphism (LS L) (embed_obj L (forget_obj L T Hf)) T
    (fun e => e)
    (fun e H => H).

(** Counit naturality: for f : T1 -> T2 at level LS L (both forgettable),
    f . epsilon_T1 ~= epsilon_T2 . embed(forget(f))  (pointwise). *)
Lemma adjunction_counit_natural : forall (L : Level)
  (T1 T2 : System (LS L))
  (Hf1 : is_forgettable L T1) (Hf2 : is_forgettable L T2)
  (f : SystemMorphism (LS L) T1 T2) (e : ElemOf (LS L) T1),
  sm_map (LS L) _ _
    (compose_morphism (LS L)
      (adjunction_counit_component L T1 Hf1) f) e =
  sm_map (LS L) _ _
    (compose_morphism (LS L)
      (embed_mor L (forget_obj L T1 Hf1) (forget_obj L T2 Hf2)
        (forget_mor L T1 T2 Hf1 Hf2 f))
      (adjunction_counit_component L T2 Hf2)) e.
Proof.
  intros L T1 T2 Hf1 Hf2 f e. reflexivity.
Qed.

(** The counit is an isomorphism for forgettable systems.
    epsilon_T : embed(forget(T)) -> T is essentially the identity on elements. *)
Lemma adjunction_counit_is_iso_for_forgettable : forall (L : Level)
  (T : System (LS L)) (Hf : is_forgettable L T),
  is_isomorphism (LS L) (adjunction_counit_component L T Hf).
Proof.
  intros L T Hf.
  set (eps := adjunction_counit_component L T Hf).
  set (eps_inv := mkSystemMorphism (LS L) T
    (embed_obj L (forget_obj L T Hf))
    (fun e => e) (fun e H => H)).
  exists eps_inv.
  split.
  - intro e. reflexivity.
  - intro e. reflexivity.
Qed.

(* ================================================================= *)
(*  PART III: TRIANGLE IDENTITIES AND CONSEQUENCES (11 Qed)            *)
(* ================================================================= *)

(** Triangle identity 1: epsilon_{embed S} . embed(eta_S) = id  (pointwise).
    Both sides are the identity on elements of embed(S). *)
Lemma triangle_identity_1 : forall (L : Level) (S : System L)
  (e : ElemOf (LS L) (embed_obj L S)),
  sm_map (LS L) _ _
    (compose_morphism (LS L)
      (embed_mor L S
        (forget_obj L (embed_obj L S) (embed_is_forgettable L S))
        (adjunction_unit_component L S))
      (adjunction_counit_component L (embed_obj L S)
        (embed_is_forgettable L S))) e = e.
Proof.
  intros L S e. reflexivity.
Qed.

(** Triangle identity 2: forget(epsilon_T) . eta_{forget T} = id  (pointwise).
    For forgettable T, both sides are the identity on elements of forget(T). *)
Lemma triangle_identity_2 : forall (L : Level) (T : System (LS L))
  (Hf : is_forgettable L T)
  (e : ElemOf L (forget_obj L T Hf)),
  sm_map L _ _
    (compose_morphism L
      (adjunction_unit_component L (forget_obj L T Hf))
      (forget_mor L
        (embed_obj L (forget_obj L T Hf)) T
        (embed_is_forgettable L (forget_obj L T Hf)) Hf
        (adjunction_counit_component L T Hf))) e = e.
Proof.
  intros L T Hf e. reflexivity.
Qed.

(** embed reflects isomorphisms: if embed(f) is iso then f is iso.
    Uses faithfulness of embed. *)
Lemma embed_reflects_iso : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_isomorphism (LS L) (embed_mor L S1 S2 f) ->
  is_isomorphism L f.
Proof.
  intros L S1 S2 f [g_emb [Hgf Hfg]].
  (* g_emb : SystemMorphism (LS L) (embed_obj L S2) (embed_obj L S1) *)
  (* Use adj_forward to bring g_emb down to level L *)
  set (g := adj_forward L S2 (embed_obj L S1)
              (embed_is_forgettable L S1) g_emb).
  (* g : SystemMorphism L S2 (forget_obj L (embed_obj L S1) ...) *)
  (* We need a morphism S2 -> S1. Since forget(embed(S1)) = S1 by
     roundtrip, we can extract the map. *)
  set (g' := mkSystemMorphism L S2 S1
    (sm_map L S2 (forget_obj L (embed_obj L S1)
      (embed_is_forgettable L S1)) g)
    (sm_preserves L S2 (forget_obj L (embed_obj L S1)
      (embed_is_forgettable L S1)) g)).
  exists g'.
  split.
  - intro e. exact (Hgf e).
  - intro e. exact (Hfg e).
Qed.

(** Uniqueness of adjunction pair: if g : S -> forget(T) corresponds to
    f : embed(S) -> T via the bijection, then g is uniquely determined by f. *)
Lemma adjunction_unique_extension : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (f : SystemMorphism (LS L) (embed_obj L S) T)
  (g : SystemMorphism L S (forget_obj L T Hf)),
  (forall e, sm_map (LS L) (embed_obj L S) T
    (adj_backward L S T Hf g) e =
    sm_map (LS L) (embed_obj L S) T f e) ->
  morphism_eq L g (adj_forward L S T Hf f).
Proof.
  intros L S T Hf f g Hext e.
  exact (Hext e).
Qed.

(** The adjunction is "tight": the unit is an iso, confirming embed is
    fully faithful. This is the categorical characterization. *)
Lemma forget_embed_adjunction_tight : forall (L : Level) (S : System L),
  is_iso (SystemCat L) S
    (forget_obj L (embed_obj L S) (embed_is_forgettable L S))
    (adjunction_unit_component L S).
Proof.
  intros L S.
  apply SystemCat_iso_iff_isomorphism.
  apply adjunction_unit_is_iso.
Qed.

(** adj_forward of identity = unit component *)
Lemma adj_forward_id : forall (L : Level) (S : System L)
  (e : ElemOf L S),
  sm_map L S _
    (adj_forward L S (embed_obj L S) (embed_is_forgettable L S)
      (id_morphism (LS L) (embed_obj L S))) e =
  sm_map L S _ (adjunction_unit_component L S) e.
Proof.
  intros L S e. reflexivity.
Qed.

(** adj_backward of unit = identity at embed level *)
Lemma adj_backward_id : forall (L : Level) (S : System L)
  (e : ElemOf (LS L) (embed_obj L S)),
  sm_map (LS L) (embed_obj L S) (embed_obj L S)
    (adj_backward L S (embed_obj L S) (embed_is_forgettable L S)
      (adjunction_unit_component L S)) e =
  sm_map (LS L) (embed_obj L S) (embed_obj L S)
    (id_morphism (LS L) (embed_obj L S)) e.
Proof.
  intros L S e. reflexivity.
Qed.

(** Re-derive embed faithfulness from the adjunction:
    if embed(f) ~= embed(g) then f ~= g.
    This uses the adjunction bijection rather than direct argument. *)
Lemma embed_faithful_via_adjunction : forall (L : Level) (S1 S2 : System L)
  (f g : SystemMorphism L S1 S2),
  morphism_eq (LS L) (embed_mor L S1 S2 f) (embed_mor L S1 S2 g) ->
  morphism_eq L f g.
Proof.
  intros L S1 S2 f g Heq e.
  (* adj_forward maps embed(f) and embed(g) to morphisms at level L *)
  set (f' := adj_forward L S1 (embed_obj L S2)
               (embed_is_forgettable L S2) (embed_mor L S1 S2 f)).
  set (g' := adj_forward L S1 (embed_obj L S2)
               (embed_is_forgettable L S2) (embed_mor L S1 S2 g)).
  (* f' and g' are morphism_eq L by adj_bijection_compat *)
  assert (Heq' : morphism_eq L f' g').
  { apply adj_bijection_compat. exact Heq. }
  (* f' acts the same as f on elements, g' acts the same as g *)
  exact (Heq' e).
Qed.

(** epsilon at embed(S) composed with embed(eta_S) = id (categorical form).
    This is triangle identity 1 in morphism_eq form. *)
Lemma counit_embed_is_id : forall (L : Level) (S : System L),
  morphism_eq (LS L)
    (compose_morphism (LS L)
      (embed_mor L S
        (forget_obj L (embed_obj L S) (embed_is_forgettable L S))
        (adjunction_unit_component L S))
      (adjunction_counit_component L (embed_obj L S)
        (embed_is_forgettable L S)))
    (id_morphism (LS L) (embed_obj L S)).
Proof.
  intros L S e. reflexivity.
Qed.

(** Embed preserves distinctness of element types:
    if the element types of S1 and S2 differ, so do their embeddings.
    Equivalently (contrapositive): equal embeddings imply equal element types.
    This is a weaker but cleanly provable form of object injectivity. *)
Lemma embed_injective_on_elem_types : forall (L : Level) (S1 S2 : System L),
  embed_obj L S1 = embed_obj L S2 -> ElemOf L S1 = ElemOf L S2.
Proof.
  intros L S1 S2 Heq.
  (* ElemOf (LS L) (embed_obj L S) = ElemOf L S definitionally.
     So embed_obj L S1 = embed_obj L S2 implies
     ElemOf (LS L) (embed_obj L S1) = ElemOf (LS L) (embed_obj L S2)
     which equals ElemOf L S1 = ElemOf L S2. *)
  change (ElemOf (LS L) (embed_obj L S1) = ElemOf (LS L) (embed_obj L S2)).
  rewrite Heq. reflexivity.
Qed.

(** The adjunction bijection preserves isomorphisms:
    f : embed(S) -> T is iso iff adj_forward(f) : S -> forget(T) is iso. *)
Lemma adj_preserves_iso : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (f : SystemMorphism (LS L) (embed_obj L S) T),
  is_isomorphism (LS L) f ->
  is_isomorphism L (adj_forward L S T Hf f).
Proof.
  intros L S T Hf f [g [Hgf Hfg]].
  (* g : SystemMorphism (LS L) T (embed_obj L S) *)
  (* adj_forward(g) would be S -> forget(embed(S)), not what we want.
     Instead, construct the inverse directly. *)
  set (g_down := mkSystemMorphism L (forget_obj L T Hf) S
    (sm_map (LS L) T (embed_obj L S) g)
    (sm_preserves (LS L) T (embed_obj L S) g)).
  exists g_down.
  split.
  - intro e. exact (Hgf e).
  - intro e. exact (Hfg e).
Qed.

(** The adjunction bijection also preserves iso in the reverse direction:
    if adj_forward(f) is iso then f is iso. *)
Lemma adj_reflects_iso : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (f : SystemMorphism (LS L) (embed_obj L S) T),
  is_isomorphism L (adj_forward L S T Hf f) ->
  is_isomorphism (LS L) f.
Proof.
  intros L S T Hf f [g_down [Hgf Hfg]].
  (* g_down : SystemMorphism L (forget_obj L T Hf) S *)
  (* Lift g_down back to level LS L *)
  set (g_up := mkSystemMorphism (LS L) T (embed_obj L S)
    (sm_map L (forget_obj L T Hf) S g_down)
    (sm_preserves L (forget_obj L T Hf) S g_down)).
  exists g_up.
  split.
  - intro e. exact (Hgf e).
  - intro e. exact (Hfg e).
Qed.

(** Unit composed with adj_forward gives back the original morphism
    (the unit-counit form of adj_forward). *)
Lemma adj_forward_via_unit : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (f : SystemMorphism (LS L) (embed_obj L S) T)
  (e : ElemOf L S),
  sm_map L S (forget_obj L T Hf) (adj_forward L S T Hf f) e =
  sm_map L S (forget_obj L T Hf)
    (compose_morphism L
      (adjunction_unit_component L S)
      (forget_mor L (embed_obj L S) T
        (embed_is_forgettable L S) Hf f)) e.
Proof.
  intros L S T Hf f e. reflexivity.
Qed.

(** Counit composed with adj_backward gives back the original morphism
    (the unit-counit form of adj_backward). *)
Lemma adj_backward_via_counit : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T)
  (g : SystemMorphism L S (forget_obj L T Hf))
  (e : ElemOf (LS L) (embed_obj L S)),
  sm_map (LS L) (embed_obj L S) T (adj_backward L S T Hf g) e =
  sm_map (LS L) (embed_obj L S) T
    (compose_morphism (LS L)
      (embed_mor L S (forget_obj L T Hf) g)
      (adjunction_counit_component L T Hf)) e.
Proof.
  intros L S T Hf g e. reflexivity.
Qed.

(** The adjunction bijection is compatible with composition in both
    variables simultaneously: naturality square commutes pointwise. *)
Lemma adj_naturality_square : forall (L : Level)
  (S1 S2 : System L)
  (T1 T2 : System (LS L))
  (Hf1 : is_forgettable L T1) (Hf2 : is_forgettable L T2)
  (h : SystemMorphism L S1 S2)
  (k : SystemMorphism (LS L) T1 T2)
  (f : SystemMorphism (LS L) (embed_obj L S2) T1)
  (e : ElemOf L S1),
  sm_map L S1 (forget_obj L T2 Hf2)
    (adj_forward L S1 T2 Hf2
      (compose_morphism (LS L) (embed_mor L S1 S2 h)
        (compose_morphism (LS L) f k))) e =
  sm_map L S1 (forget_obj L T2 Hf2)
    (compose_morphism L h
      (compose_morphism L
        (adj_forward L S2 T1 Hf1 f)
        (forget_mor L T1 T2 Hf1 Hf2 k))) e.
Proof.
  intros L S1 S2 T1 T2 Hf1 Hf2 h k f e. reflexivity.
Qed.

(* ================================================================= *)
(*  Summary: 25 Qed, 0 Admitted, 0 axioms                             *)
(*                                                                     *)
(*  Part I — Hom-Set Bijection (6 Qed):                                *)
(*    1 adj_forward_backward                                           *)
(*    2 adj_backward_forward                                           *)
(*    3 level_adjunction                                               *)
(*    4 adj_natural_S                                                  *)
(*    5 adj_natural_T                                                  *)
(*    6 adj_bijection_compat                                           *)
(*                                                                     *)
(*  Part II — Unit and Counit (6 Qed):                                 *)
(*    7 adjunction_unit_natural                                        *)
(*    8 adjunction_unit_is_iso                                         *)
(*    9 adjunction_counit_natural                                      *)
(*   10 adjunction_counit_is_iso_for_forgettable                       *)
(*                                                                     *)
(*  Part III — Triangle Identities and Consequences (13 Qed):          *)
(*   11 triangle_identity_1                                            *)
(*   12 triangle_identity_2                                            *)
(*   13 embed_reflects_iso                                             *)
(*   14 adjunction_unique_extension                                    *)
(*   15 forget_embed_adjunction_tight                                  *)
(*   16 adj_forward_id                                                 *)
(*   17 adj_backward_id                                                *)
(*   18 embed_faithful_via_adjunction                                  *)
(*   19 counit_embed_is_id                                             *)
(*   20 embed_injective_on_elem_types                                  *)
(*   21 adj_preserves_iso                                              *)
(*   22 adj_reflects_iso                                               *)
(*   23 adj_forward_via_unit                                           *)
(*   24 adj_backward_via_counit                                        *)
(*   25 adj_naturality_square                                          *)
(*                                                                     *)
(*  4 Definitions (not counted): adj_forward, adj_backward,            *)
(*  adjunction_unit_component, adjunction_counit_component.            *)
(* ================================================================= *)
