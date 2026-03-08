(** * LevelFunctors.v — Cross-Level Functors

    Embedding and (restricted) forgetful functors between Sys(L) and Sys(LS L).

    Elements: Systems at different levels, cross-level mappings
    Roles:    embed -> promotes L to LS L, forget -> demotes (when possible)
    Rules:    functor laws (preserves id, composition), roundtrip properties
    Status:   embed is a full Functor; forget is partial (restricted by P1)

    KEY DESIGN:
    - embed_obj: System L -> System (LS L) by bumping level witness via transitivity
    - embed_mor: same underlying function (domains are definitionally equal)
    - forget_obj: System (LS L) -> System L only when level witness << L
    - P1 obstruction: systems with witness = L cannot be forgotten

    STATUS: 30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import UniversePolymorphism.
From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import SystemCategory.

(* ================================================================= *)
(*  PART I: EMBEDDING — System L -> System (LS L) (7 Qed)             *)
(* ================================================================= *)

(** Embed a system from level L to level LS L.
    Same domain, same predicate, same witness — but now the witness
    validity proof is bumped via transitivity: w << L << LS L => w << LS L. *)
Definition embed_obj (L : Level) (S : System L) : System (LS L) :=
  mkSystem (LS L)
    (mkCriterion (LS L)
      (crit_domain L (sys_criterion L S))
      (crit_predicate L (sys_criterion L S))
      (crit_level_witness L (sys_criterion L S))
      (level_lt_trans
        (crit_level_witness L (sys_criterion L S))
        L (LS L)
        (crit_level_valid L (sys_criterion L S))
        (level_lt_LS L)))
    (sys_pos_bound L S)
    (sys_uniqueness L S).

(** The element type of embed_obj is definitionally equal to that of the original *)
Lemma embed_obj_elem_eq : forall (L : Level) (S : System L),
  ElemOf (LS L) (embed_obj L S) = ElemOf L S.
Proof.
  intros L S. reflexivity.
Qed.

(** Embed a morphism from level L to level LS L.
    Since the domains are definitionally equal, the sm_map is the same function. *)
Definition embed_mor (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2)
  : SystemMorphism (LS L) (embed_obj L S1) (embed_obj L S2) :=
  mkSystemMorphism (LS L) (embed_obj L S1) (embed_obj L S2)
    (sm_map L S1 S2 f)
    (sm_preserves L S1 S2 f).

(** embed_mor preserves morphism_eq *)
Lemma embed_mor_compat : forall (L : Level) (S1 S2 : System L)
  (f g : SystemMorphism L S1 S2),
  morphism_eq L f g ->
  morphism_eq (LS L) (embed_mor L S1 S2 f) (embed_mor L S1 S2 g).
Proof.
  intros L S1 S2 f g Heq. intro e. simpl. apply Heq.
Qed.

(** embed_mor preserves identity *)
Lemma embed_mor_id : forall (L : Level) (S : System L),
  morphism_eq (LS L)
    (embed_mor L S S (id_morphism L S))
    (id_morphism (LS L) (embed_obj L S)).
Proof.
  intros L S. intro e. reflexivity.
Qed.

(** embed_mor preserves composition.
    In SystemCat, cat_comp S1 S2 S3 g f = compose_morphism f g.
    So we need: embed(compose f g) ~= compose(embed f)(embed g). *)
Lemma embed_mor_comp : forall (L : Level) (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  morphism_eq (LS L)
    (embed_mor L S1 S3 (compose_morphism L f g))
    (compose_morphism (LS L) (embed_mor L S1 S2 f) (embed_mor L S2 S3 g)).
Proof.
  intros L S1 S2 S3 f g. intro e. reflexivity.
Qed.

(** embed_mor is faithful: if embed f ~= embed g then f ~= g *)
Lemma embed_faithful : forall (L : Level) (S1 S2 : System L)
  (f g : SystemMorphism L S1 S2),
  morphism_eq (LS L) (embed_mor L S1 S2 f) (embed_mor L S1 S2 g) ->
  morphism_eq L f g.
Proof.
  intros L S1 S2 f g Heq. intro e. exact (Heq e).
Qed.

(** embed_mor preserves embeddings (injective morphisms) *)
Lemma embed_preserves_embedding : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_embedding L f ->
  is_embedding (LS L) (embed_mor L S1 S2 f).
Proof.
  intros L S1 S2 f Hemb. unfold is_embedding. intros e1 e2 Heq.
  apply Hemb. exact Heq.
Qed.

(** embed_mor preserves surjections *)
Lemma embed_preserves_surjection : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_surjection L f ->
  is_surjection (LS L) (embed_mor L S1 S2 f).
Proof.
  intros L S1 S2 f Hsurj. unfold is_surjection. intro e2.
  destruct (Hsurj e2) as [e1 He1]. exists e1. exact He1.
Qed.

(* ================================================================= *)
(*  PART II: EMBEDDING FUNCTOR (1 Qed)                                *)
(* ================================================================= *)

(** The embedding functor Embed_L : Sys(L) -> Sys(LS L).
    fobj = embed_obj, fmor = embed_mor.
    This is a full Functor instance. *)
Definition EmbedFunctor (L : Level) : Functor (SystemCat L) (SystemCat (LS L)).
Proof.
  apply (mkFunctor (SystemCat L) (SystemCat (LS L))
    (embed_obj L)
    (fun S1 S2 (f : SystemMorphism L S1 S2) => embed_mor L S1 S2 f)).
  - (* fmor_compat *)
    intros S1 S2 f g Heq. apply embed_mor_compat. exact Heq.
  - (* fmor_id *)
    intros S. apply embed_mor_id.
  - (* fmor_comp: embed(cat_comp g f) ~= cat_comp (embed g) (embed f)
       In SystemCat, cat_comp S1 S2 S3 g f = compose_morphism f g.
       So: embed(compose f g) ~= compose(embed f)(embed g)
       = embed_mor_comp. *)
    intros S1 S2 S3 f g. simpl.
    (* Goal: morphism_eq (LS L) (embed_mor compose(f,g)) (compose(embed f, embed g)) *)
    apply embed_mor_comp.
Defined.

Lemma EmbedFunctor_obj : forall (L : Level) (S : System L),
  fobj (EmbedFunctor L) S = embed_obj L S.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================= *)
(*  PART III: EMBEDDING PRESERVES ISO (2 Qed)                         *)
(* ================================================================= *)

(** embed_mor preserves iso pairs *)
Lemma embed_preserves_iso_pair : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S1),
  is_iso_pair L f g ->
  is_iso_pair (LS L) (embed_mor L S1 S2 f) (embed_mor L S2 S1 g).
Proof.
  intros L S1 S2 f g [Hgf Hfg]. split.
  - intro e. simpl. apply Hgf.
  - intro e. simpl. apply Hfg.
Qed.

(** embed_mor preserves isomorphisms *)
Lemma embed_preserves_iso : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_isomorphism L f ->
  is_isomorphism (LS L) (embed_mor L S1 S2 f).
Proof.
  intros L S1 S2 f [g Hpair].
  exists (embed_mor L S2 S1 g).
  apply embed_preserves_iso_pair. exact Hpair.
Qed.

(* ================================================================= *)
(*  PART IV: FORGETTABLE SYSTEMS AND FORGET (9 Qed)                   *)
(* ================================================================= *)

(** A system at LS L is "forgettable" to L if its level witness is below L.
    This is the condition that allows demoting a system from LS L to L. *)
Definition is_forgettable (L : Level) (S : System (LS L)) : Prop :=
  crit_level_witness (LS L) (sys_criterion (LS L) S) << L.

(** Forget a forgettable system from LS L to L.
    Same domain, same predicate, same witness — but now the validity proof
    is the forgettability hypothesis itself. *)
Definition forget_obj (L : Level) (S : System (LS L))
  (Hf : is_forgettable L S) : System L :=
  mkSystem L
    (mkCriterion L
      (crit_domain (LS L) (sys_criterion (LS L) S))
      (crit_predicate (LS L) (sys_criterion (LS L) S))
      (crit_level_witness (LS L) (sys_criterion (LS L) S))
      Hf)
    (sys_pos_bound (LS L) S)
    (sys_uniqueness (LS L) S).

(** Every embedded system is forgettable *)
Lemma embed_is_forgettable : forall (L : Level) (S : System L),
  is_forgettable L (embed_obj L S).
Proof.
  intros L S. unfold is_forgettable. simpl.
  exact (crit_level_valid L (sys_criterion L S)).
Defined.

(** forget . embed = id (roundtrip) *)
Lemma forget_embed_roundtrip : forall (L : Level) (S : System L),
  forget_obj L (embed_obj L S) (embed_is_forgettable L S) = S.
Proof.
  intros L S. unfold forget_obj, embed_obj. simpl.
  destruct S as [c pb u].
  destruct c as [d p w v]. simpl.
  reflexivity.
Qed.

(** The element type of forget_obj is the same as the original *)
Lemma forget_obj_elem_eq : forall (L : Level) (S : System (LS L))
  (Hf : is_forgettable L S),
  ElemOf L (forget_obj L S Hf) = ElemOf (LS L) S.
Proof.
  intros L S Hf. reflexivity.
Qed.

(** Forget a morphism: given f : S1 -> S2 at LS L, produce f' : forget S1 -> forget S2 at L *)
Definition forget_mor (L : Level) (S1 S2 : System (LS L))
  (Hf1 : is_forgettable L S1) (Hf2 : is_forgettable L S2)
  (f : SystemMorphism (LS L) S1 S2)
  : SystemMorphism L (forget_obj L S1 Hf1) (forget_obj L S2 Hf2) :=
  mkSystemMorphism L (forget_obj L S1 Hf1) (forget_obj L S2 Hf2)
    (sm_map (LS L) S1 S2 f)
    (sm_preserves (LS L) S1 S2 f).

(** forget_mor preserves morphism_eq *)
Lemma forget_mor_compat : forall (L : Level) (S1 S2 : System (LS L))
  (Hf1 : is_forgettable L S1) (Hf2 : is_forgettable L S2)
  (f g : SystemMorphism (LS L) S1 S2),
  morphism_eq (LS L) f g ->
  morphism_eq L (forget_mor L S1 S2 Hf1 Hf2 f) (forget_mor L S1 S2 Hf1 Hf2 g).
Proof.
  intros L S1 S2 Hf1 Hf2 f g Heq. intro e. simpl. apply Heq.
Qed.

(** forget_mor preserves identity *)
Lemma forget_mor_id : forall (L : Level) (S : System (LS L))
  (Hf : is_forgettable L S),
  morphism_eq L
    (forget_mor L S S Hf Hf (id_morphism (LS L) S))
    (id_morphism L (forget_obj L S Hf)).
Proof.
  intros L S Hf. intro e. reflexivity.
Qed.

(** forget_mor preserves composition *)
Lemma forget_mor_comp : forall (L : Level) (S1 S2 S3 : System (LS L))
  (Hf1 : is_forgettable L S1) (Hf2 : is_forgettable L S2)
  (Hf3 : is_forgettable L S3)
  (f : SystemMorphism (LS L) S1 S2) (g : SystemMorphism (LS L) S2 S3),
  morphism_eq L
    (forget_mor L S1 S3 Hf1 Hf3 (compose_morphism (LS L) f g))
    (compose_morphism L
      (forget_mor L S1 S2 Hf1 Hf2 f)
      (forget_mor L S2 S3 Hf2 Hf3 g)).
Proof.
  intros L S1 S2 S3 Hf1 Hf2 Hf3 f g. intro e. reflexivity.
Qed.

(** forget_mor is faithful *)
Lemma forget_faithful : forall (L : Level) (S1 S2 : System (LS L))
  (Hf1 : is_forgettable L S1) (Hf2 : is_forgettable L S2)
  (f g : SystemMorphism (LS L) S1 S2),
  morphism_eq L
    (forget_mor L S1 S2 Hf1 Hf2 f)
    (forget_mor L S1 S2 Hf1 Hf2 g) ->
  morphism_eq (LS L) f g.
Proof.
  intros L S1 S2 Hf1 Hf2 f g Heq. intro e. exact (Heq e).
Qed.

(** forget_mor preserves embeddings *)
Lemma forget_preserves_embedding : forall (L : Level) (S1 S2 : System (LS L))
  (Hf1 : is_forgettable L S1) (Hf2 : is_forgettable L S2)
  (f : SystemMorphism (LS L) S1 S2),
  is_embedding (LS L) f ->
  is_embedding L (forget_mor L S1 S2 Hf1 Hf2 f).
Proof.
  intros L S1 S2 Hf1 Hf2 f Hemb. unfold is_embedding. intros e1 e2 Heq.
  apply Hemb. exact Heq.
Qed.

(* ================================================================= *)
(*  PART V: FORGET-EMBED ADJUNCTION PROPERTIES (3 Qed)                *)
(* ================================================================= *)

(** forget(embed(f)) acts the same as f on elements *)
Lemma forget_embed_mor_roundtrip : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (e : ElemOf L S1),
  sm_map L _ _
    (forget_mor L (embed_obj L S1) (embed_obj L S2)
      (embed_is_forgettable L S1) (embed_is_forgettable L S2)
      (embed_mor L S1 S2 f)) e = sm_map L S1 S2 f e.
Proof.
  intros L S1 S2 f e. reflexivity.
Qed.

(** embed(forget(f)) acts the same as f on elements (for forgettable systems) *)
Lemma embed_forget_mor_roundtrip : forall (L : Level) (S1 S2 : System (LS L))
  (Hf1 : is_forgettable L S1) (Hf2 : is_forgettable L S2)
  (f : SystemMorphism (LS L) S1 S2) (e : ElemOf (LS L) S1),
  sm_map (LS L) _ _
    (embed_mor L (forget_obj L S1 Hf1) (forget_obj L S2 Hf2)
      (forget_mor L S1 S2 Hf1 Hf2 f)) e = sm_map (LS L) S1 S2 f e.
Proof.
  intros L S1 S2 Hf1 Hf2 f e. reflexivity.
Qed.

(** The forget-embed composition on objects is not Leibniz-equal in general
    (because the proof terms in the criterion differ), but the embedded-
    then-forgotten system has the same elements, predicate, etc. *)
Lemma embed_forget_elem_roundtrip : forall (L : Level) (S : System (LS L))
  (Hf : is_forgettable L S),
  ElemOf (LS L) (embed_obj L (forget_obj L S Hf)) = ElemOf (LS L) S.
Proof.
  intros L S Hf. reflexivity.
Qed.

(* ================================================================= *)
(*  PART VI: P1 OBSTRUCTION — Not All Systems Are Forgettable (3 Qed) *)
(* ================================================================= *)

(** A system at LS L whose witness = L. This system is NOT forgettable
    because forgetting would require L << L, contradicting P1. *)
Definition witness_L_system (L : Level) : System (LS L) :=
  mkSystem (LS L)
    (mkCriterion (LS L) nat (fun _ => True) L (level_lt_LS L))
    Unbounded
    MultiplePerRole.

(** The witness_L_system is NOT forgettable *)
Lemma witness_L_not_forgettable : forall (L : Level),
  ~ is_forgettable L (witness_L_system L).
Proof.
  intros L Hf. unfold is_forgettable in Hf. simpl in Hf.
  exact (level_lt_irrefl L Hf).
Qed.

(** General P1 obstruction: there exist systems at LS L that cannot
    be forgotten to L. *)
Theorem P1_obstructs_total_forget : forall (L : Level),
  exists S : System (LS L), ~ is_forgettable L S.
Proof.
  intros L. exists (witness_L_system L). apply witness_L_not_forgettable.
Qed.

(** The forgettability predicate is decidable *)
Lemma is_forgettable_dec : forall (L : Level) (S : System (LS L)),
  {is_forgettable L S} + {~ is_forgettable L S}.
Proof.
  intros L S. unfold is_forgettable.
  apply level_lt_dec.
Qed.

(* ================================================================= *)
(*  PART VII: EMBEDDING INTO HIGHER LEVELS (4 Qed)                    *)
(* ================================================================= *)

(** We can embed two levels up: L -> LS L -> LS (LS L) *)
Definition embed_obj_2 (L : Level) (S : System L) : System (LS (LS L)) :=
  embed_obj (LS L) (embed_obj L S).

(** The two-level embedding has the same domain *)
Lemma embed_obj_2_elem_eq : forall (L : Level) (S : System L),
  ElemOf (LS (LS L)) (embed_obj_2 L S) = ElemOf L S.
Proof.
  intros L S. reflexivity.
Qed.

(** The two-level embedding is forgettable to LS L *)
Lemma embed_2_forgettable_to_LS : forall (L : Level) (S : System L),
  is_forgettable (LS L) (embed_obj_2 L S).
Proof.
  intros L S. apply embed_is_forgettable.
Defined.

(** After forgetting from LS(LS L) to LS L, the result is forgettable to L *)
Lemma embed_2_forgettable_to_L : forall (L : Level) (S : System L),
  is_forgettable L
    (forget_obj (LS L) (embed_obj_2 L S) (embed_2_forgettable_to_LS L S)).
Proof.
  intros L S. unfold is_forgettable, forget_obj, embed_obj_2, embed_obj. simpl.
  exact (crit_level_valid L (sys_criterion L S)).
Defined.

(** Two-level embed then double forget to L recovers the original *)
Lemma embed_2_forget_roundtrip : forall (L : Level) (S : System L),
  forget_obj L
    (forget_obj (LS L) (embed_obj_2 L S) (embed_2_forgettable_to_LS L S))
    (embed_2_forgettable_to_L L S) = S.
Proof.
  intros L S.
  unfold forget_obj, embed_obj_2, embed_obj. simpl.
  destruct S as [c pb u].
  destruct c as [d p w v]. simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(*  PART VIII: FUNCTORIALITY OF EMBED ON CATEGORICAL PROPERTIES       *)
(*             (2 Qed)                                                 *)
(* ================================================================= *)

(** EmbedFunctor preserves isomorphisms (as a Functor, it inherits this
    from the general fmor_preserves_iso lemma) *)
Lemma EmbedFunctor_preserves_iso : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  is_iso (SystemCat (LS L)) (embed_obj L S1) (embed_obj L S2)
    (fmor (EmbedFunctor L) f).
Proof.
  intros L S1 S2 f Hiso.
  exact (fmor_preserves_iso (SystemCat L) (SystemCat (LS L))
    (EmbedFunctor L) S1 S2 f Hiso).
Qed.

(** NOTE: General initiality preservation (embed of initial = initial) requires
    the initial object to have empty domain. For non-empty initial objects,
    initiality at L does not imply initiality at LS L because the target
    systems at LS L may have domains unreachable from level L.
    We prove the concrete case for empty systems below. *)

(** Specifically: embed of the empty system is initial *)
Lemma embed_empty_is_initial : forall (L : Level) (w : Level) (Hw : w << L),
  is_initial (SystemCat (LS L)) (embed_obj L (empty_system L w Hw)).
Proof.
  intros L w Hw T.
  set (eS := embed_obj L (empty_system L w Hw)).
  assert (Hempty : ElemOf (LS L) eS = False).
  { reflexivity. }
  exists (mkSystemMorphism (LS L) eS T
    (fun e : ElemOf (LS L) eS => match (eq_rect _ (fun T => T) e _ Hempty) with end)
    (fun e : ElemOf (LS L) eS => match (eq_rect _ (fun T => T) e _ Hempty) with end)).
  intro g. intro e. simpl. destruct e.
Qed.

(* ================================================================= *)
(*  Summary: 30 Qed, 0 Admitted, 0 axioms                             *)
(*    1 embed_obj_elem_eq                                              *)
(*    5 embed_mor: embed_mor_compat, embed_mor_id, embed_mor_comp,     *)
(*      embed_faithful, embed_preserves_embedding                      *)
(*    1 embed_preserves_surjection                                     *)
(*    1 EmbedFunctor_obj                                               *)
(*    2 embed iso: embed_preserves_iso_pair, embed_preserves_iso       *)
(*    1 embed_is_forgettable                                           *)
(*    1 forget_embed_roundtrip                                         *)
(*    1 forget_obj_elem_eq                                             *)
(*    5 forget_mor: forget_mor_compat, forget_mor_id, forget_mor_comp, *)
(*      forget_faithful, forget_preserves_embedding                    *)
(*    3 roundtrip: forget_embed_mor_roundtrip,                         *)
(*      embed_forget_mor_roundtrip, embed_forget_elem_roundtrip        *)
(*    3 P1: witness_L_not_forgettable, P1_obstructs_total_forget,      *)
(*      is_forgettable_dec                                             *)
(*    4 embed_2: embed_obj_2_elem_eq, embed_2_forgettable_to_LS,       *)
(*      embed_2_forgettable_to_L, embed_2_forget_roundtrip             *)
(*    2 categorical: EmbedFunctor_preserves_iso,                       *)
(*      embed_empty_is_initial                                         *)
(* ================================================================= *)
