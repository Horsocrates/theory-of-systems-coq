(** * SystemCategory.v — Sys(L) as Category Instance

    Bridges SystemMorphism.v -> Category.v: constructs the category Sys(L)
    whose objects are System L, morphisms are SystemMorphism L, and equality
    is pointwise morphism_eq.

    Elements: Systems at level L (objects), SystemMorphisms (arrows)
    Roles:    identity morphism -> cat_id, composition -> cat_comp (with swap!)
    Rules:    associativity, identity laws, composition compatibility
    Status:   SystemCat is a valid Category; bridge lemmas for iso/mono/epi

    KEY DESIGN DECISION — Composition Order Swap:
      cat_comp S1 S2 S3 g f = compose_morphism L f g
      Category.v: cat_comp a b c takes g:b->c FIRST, then f:a->b SECOND
      SystemMorphism.v: compose_morphism takes f:S1->S2 FIRST, then g:S2->S3 SECOND
      Both compute g . f, but argument order is reversed.

    CONSEQUENCE:
      cat_id_l requires compose_morphism f (id_morphism S2) ~= f  (= compose_id_right)
      cat_id_r requires compose_morphism (id_morphism S1) f ~= f  (= compose_id_left)

    STATUS: 29 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import UniversePolymorphism.
From ToS Require Import stdlib.Category.

(* ================================================================= *)
(*  PART I: COMPOSITION COMPATIBILITY (1 Qed)                         *)
(* ================================================================= *)

(** Composition respects morphism_eq on both arguments.
    Needed for cat_comp_compat in the Category record. *)
Lemma compose_compat : forall (L : Level) (S1 S2 S3 : System L)
  (f f' : SystemMorphism L S2 S3) (g g' : SystemMorphism L S1 S2),
  morphism_eq L f f' ->
  morphism_eq L g g' ->
  morphism_eq L (compose_morphism L g f) (compose_morphism L g' f').
Proof.
  intros L S1 S2 S3 f f' g g' Hf Hg.
  intro e. simpl.
  rewrite (Hg e).
  rewrite (Hf (sm_map L S1 S2 g' e)).
  reflexivity.
Qed.

(* ================================================================= *)
(*  PART II: THE CATEGORY INSTANCE (1 Qed)                            *)
(* ================================================================= *)

(** Sys(L): the category of systems at level L.
    Objects = System L, Morphisms = SystemMorphism L,
    Equality = morphism_eq (pointwise), Composition = compose_morphism (swapped). *)
Definition SystemCat (L : Level) : Category := mkCategory
  (* cat_obj *)    (System L)
  (* cat_mor *)    (SystemMorphism L)
  (* cat_mor_eq *) (fun S1 S2 => @morphism_eq L S1 S2)
  (* cat_id *)     (id_morphism L)
  (* cat_comp — SWAP: cat_comp S1 S2 S3 g f = compose_morphism L f g *)
  (fun S1 S2 S3 (g : SystemMorphism L S2 S3) (f : SystemMorphism L S1 S2) =>
    compose_morphism L f g)
  (* cat_mor_eq_refl *)
  (fun S1 S2 f => @morphism_eq_refl L S1 S2 f)
  (* cat_mor_eq_sym *)
  (fun S1 S2 f g => @morphism_eq_sym L S1 S2 f g)
  (* cat_mor_eq_trans *)
  (fun S1 S2 f g h => @morphism_eq_trans L S1 S2 f g h)
  (* cat_comp_compat: g~=g', f~=f' => compose f g ~= compose f' g' *)
  (fun S1 S2 S3 g g' f f' Hg Hf =>
    compose_compat L S1 S2 S3 g g' f f' Hg Hf)
  (* cat_assoc: compose(f, compose(g, h)) = compose(compose(f, g), h)
     cat_assoc says: comp(h, comp(g, f)) = comp(comp(h, g), f)
     In swapped form: compose(f, compose(g, h)) = ... wait, let me be precise.
     cat_assoc a b c d f g h : comp(h, comp(g, f)) ~= comp(comp(h, g), f)
     where a=S1, b=S2, c=S3, d=S4, f:S1->S2, g:S2->S3, h:S3->S4
     LHS = comp S1 S3 S4 h (comp S1 S2 S3 g f) = compose(compose(f,g), h)
     RHS = comp S1 S2 S4 (comp S2 S3 S4 h g) f = compose(f, compose(g,h))
     So we need compose(compose(f,g), h) ~= compose(f, compose(g,h))
     This is compose_assoc L f g h. *)
  (fun S1 S2 S3 S4 f g h => @compose_assoc L S1 S2 S3 S4 f g h)
  (* cat_id_l: comp S1 S2 S2 (id S2) f ~= f
     = compose(f, id S2) ~= f = compose_id_right *)
  (fun S1 S2 f => @compose_id_right L S1 S2 f)
  (* cat_id_r: comp S1 S1 S2 f (id S1) ~= f
     = compose(id S1, f) ~= f = compose_id_left *)
  (fun S1 S2 f => @compose_id_left L S1 S2 f).

Lemma SystemCat_valid : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  cat_mor_eq (SystemCat L) S1 S2
    (cat_comp (SystemCat L) S1 S2 S2 (cat_id (SystemCat L) S2) f) f.
Proof.
  intros L S1 S2 f. simpl. intro e. reflexivity.
Qed.

(* ================================================================= *)
(*  PART III: BRIDGE LEMMAS — Categorical <-> SystemMorphism (10 Qed) *)
(* ================================================================= *)

(** The swap is correct: cat_comp in SystemCat L computes compose_morphism *)
Lemma SystemCat_comp_is_compose : forall (L : Level) (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  cat_comp (SystemCat L) S1 S2 S3 g f = compose_morphism L f g.
Proof.
  intros. reflexivity.
Qed.

(** Identity in SystemCat is id_morphism *)
Lemma SystemCat_id_is_id : forall (L : Level) (S : System L),
  cat_id (SystemCat L) S = id_morphism L S.
Proof.
  intros. reflexivity.
Qed.

(** Morphism equality in SystemCat is morphism_eq *)
Lemma SystemCat_eq_is_morphism_eq : forall (L : Level) (S1 S2 : System L)
  (f g : SystemMorphism L S1 S2),
  cat_mor_eq (SystemCat L) S1 S2 f g <-> morphism_eq L f g.
Proof.
  intros L S1 S2 f g. split; intro H; exact H.
Qed.

(** is_iso in SystemCat corresponds to is_isomorphism in SystemMorphism.v *)
Lemma SystemCat_iso_iff_isomorphism : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f <-> is_isomorphism L f.
Proof.
  intros L S1 S2 f. split.
  - (* is_iso -> is_isomorphism *)
    intros [g [Hgf Hfg]].
    exists g. split.
    + (* g . f = id, i.e., forall e, sm_map g (sm_map f e) = e *)
      (* Hgf : cat_mor_eq S1 S1 (comp S1 S2 S1 g f) (id S1) *)
      (* = morphism_eq (compose_morphism f g) (id_morphism S1) *)
      intro e. exact (Hgf e).
    + (* f . g = id *)
      intro e. exact (Hfg e).
  - (* is_isomorphism -> is_iso *)
    intros [g [Hgf Hfg]].
    exists g. split.
    + (* comp S1 S2 S1 g f ~= id S1 *)
      (* = compose_morphism f g ~= id_morphism S1 *)
      intro e. simpl. apply Hgf.
    + (* comp S2 S1 S2 f g ~= id S2 *)
      intro e. simpl. apply Hfg.
Qed.

(** NOTE: Categorical mono does NOT directly imply embedding (injectivity)
    in Sys(L) because constructing "point" morphisms requires a valid level
    witness. The reverse direction (embedding -> mono) holds unconditionally.
    For iso morphisms, both directions hold via iso_pair properties. *)

(** Embedding implies mono in SystemCat *)
Lemma embedding_implies_SystemCat_mono : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_embedding L f ->
  is_mono (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 f Hemb.
  unfold is_mono. intros z g1 g2 Heq.
  simpl in Heq. intro e. simpl.
  apply Hemb.
  exact (Heq e).
Qed.

(** Surjection implies epi in SystemCat *)
Lemma surjection_implies_SystemCat_epi : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_surjection L f ->
  is_epi (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 f Hsurj.
  unfold is_epi. intros z g1 g2 Heq.
  intro e2. simpl in *.
  destruct (Hsurj e2) as [e1 He1].
  rewrite <- He1.
  exact (Heq e1).
Qed.

(** is_iso_pair in SystemMorphism gives is_iso in SystemCat *)
Lemma iso_pair_gives_SystemCat_iso : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S1),
  is_iso_pair L f g ->
  is_iso (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 f g [Hgf Hfg].
  exists g. split.
  - intro e. simpl. apply Hgf.
  - intro e. simpl. apply Hfg.
Qed.

(** Conversely: is_iso in SystemCat gives is_iso_pair *)
Lemma SystemCat_iso_gives_iso_pair : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  exists g, is_iso_pair L f g.
Proof.
  intros L S1 S2 f [g [Hgf Hfg]].
  exists g. split.
  - intro e. exact (Hgf e).
  - intro e. exact (Hfg e).
Qed.

(** Identity is iso in SystemCat (via the bridge) *)
Lemma SystemCat_id_iso : forall (L : Level) (S : System L),
  is_iso (SystemCat L) S S (id_morphism L S).
Proof.
  intros L S.
  apply iso_pair_gives_SystemCat_iso with (g := id_morphism L S).
  exact (id_iso_pair L S).
Qed.

(** Composition of isos in SystemCat *)
Lemma SystemCat_iso_compose : forall (L : Level) (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  is_iso (SystemCat L) S1 S2 f ->
  is_iso (SystemCat L) S2 S3 g ->
  is_iso (SystemCat L) S1 S3 (cat_comp (SystemCat L) S1 S2 S3 g f).
Proof.
  intros L S1 S2 S3 f g Hf Hg.
  apply (iso_trans (SystemCat L) S1 S2 S3 f g Hf Hg).
Qed.

(* ================================================================= *)
(*  PART IV: EMPTY AND UNIT SYSTEMS (8 Qed)                           *)
(* ================================================================= *)

(** Empty system: domain = False. Requires a level witness w << L. *)
Definition empty_system (L : Level) (w : Level) (Hw : w << L) : System L :=
  mkSystem L
    (mkCriterion L False (fun e => match e with end) w Hw)
    Unbounded
    MultiplePerRole.

(** Unit system: domain = unit, predicate = True. *)
Definition unit_system (L : Level) (w : Level) (Hw : w << L) : System L :=
  mkSystem L
    (mkCriterion L unit (fun _ => True) w Hw)
    (Finite 1)
    UniquePerRole.

(** The unique morphism from the empty system to any system *)
Definition empty_morphism (L : Level) (w : Level) (Hw : w << L) (S : System L)
  : SystemMorphism L (empty_system L w Hw) S :=
  mkSystemMorphism L (empty_system L w Hw) S
    (fun e : False => match e with end)
    (fun (e : False) => match e with end).

(** All morphisms from empty system are equal (vacuous) *)
Lemma empty_morphism_unique : forall (L : Level) (w : Level) (Hw : w << L)
  (S : System L) (f g : SystemMorphism L (empty_system L w Hw) S),
  morphism_eq L f g.
Proof.
  intros L w Hw S f g. intro e. destruct e.
Qed.

(** Empty system is initial in SystemCat *)
Lemma empty_is_initial : forall (L : Level) (w : Level) (Hw : w << L),
  is_initial (SystemCat L) (empty_system L w Hw).
Proof.
  intros L w Hw S.
  exists (empty_morphism L w Hw S).
  intro g. apply empty_morphism_unique.
Qed.

(** For LS levels, we can construct an empty system without needing a witness argument *)
Definition empty_system_LS (L : Level) : System (LS L) :=
  empty_system (LS L) L (level_lt_LS L).

(** empty_system_LS is initial *)
Lemma empty_system_LS_is_initial : forall (L : Level),
  is_initial (SystemCat (LS L)) (empty_system_LS L).
Proof.
  intros L. apply empty_is_initial.
Qed.

(** The unique morphism from any system to the unit system *)
Definition to_unit_morphism (L : Level) (w : Level) (Hw : w << L) (S : System L)
  : SystemMorphism L S (unit_system L w Hw) :=
  mkSystemMorphism L S (unit_system L w Hw)
    (fun _ => tt)
    (fun _ _ => I).

(** All morphisms to the unit system are equal *)
Lemma unit_morphism_unique : forall (L : Level) (w : Level) (Hw : w << L)
  (S : System L) (f g : SystemMorphism L S (unit_system L w Hw)),
  morphism_eq L f g.
Proof.
  intros L w Hw S f g. intro e. simpl.
  destruct (sm_map L S (unit_system L w Hw) f e).
  destruct (sm_map L S (unit_system L w Hw) g e).
  reflexivity.
Qed.

(** Unit system is terminal in SystemCat *)
Lemma unit_is_terminal : forall (L : Level) (w : Level) (Hw : w << L),
  is_terminal (SystemCat L) (unit_system L w Hw).
Proof.
  intros L w Hw S.
  exists (to_unit_morphism L w Hw S).
  intro g. apply unit_morphism_unique.
Qed.

(* ================================================================= *)
(*  PART V: STRUCTURAL PROPERTIES OF SystemCat (8 Qed)                *)
(* ================================================================= *)

(** Two initial objects in SystemCat are isomorphic *)
Lemma SystemCat_initial_unique : forall (L : Level) (S1 S2 : System L),
  is_initial (SystemCat L) S1 ->
  is_initial (SystemCat L) S2 ->
  exists f : SystemMorphism L S1 S2, is_iso (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 H1 H2.
  exact (initial_unique_up_to_iso (SystemCat L) S1 S2 H1 H2).
Qed.

(** Two terminal objects in SystemCat are isomorphic *)
Lemma SystemCat_terminal_unique : forall (L : Level) (S1 S2 : System L),
  is_terminal (SystemCat L) S1 ->
  is_terminal (SystemCat L) S2 ->
  exists f : SystemMorphism L S1 S2, is_iso (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 H1 H2.
  exact (terminal_unique_up_to_iso (SystemCat L) S1 S2 H1 H2).
Qed.

(** Isomorphism in SystemCat is symmetric *)
Lemma SystemCat_iso_sym : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  exists g : SystemMorphism L S2 S1, is_iso (SystemCat L) S2 S1 g.
Proof.
  intros L S1 S2 f Hiso.
  exact (iso_sym (SystemCat L) S1 S2 f Hiso).
Qed.

(** Every iso in SystemCat is mono *)
Lemma SystemCat_iso_is_mono : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  is_mono (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 f Hiso.
  exact (iso_is_mono (SystemCat L) S1 S2 f Hiso).
Qed.

(** Every iso in SystemCat is epi *)
Lemma SystemCat_iso_is_epi : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  is_epi (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 f Hiso.
  exact (iso_is_epi (SystemCat L) S1 S2 f Hiso).
Qed.

(** Composition of monos in SystemCat *)
Lemma SystemCat_comp_mono : forall (L : Level) (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  is_mono (SystemCat L) S1 S2 f ->
  is_mono (SystemCat L) S2 S3 g ->
  is_mono (SystemCat L) S1 S3 (cat_comp (SystemCat L) S1 S2 S3 g f).
Proof.
  intros L S1 S2 S3 f g Hf Hg.
  exact (comp_mono (SystemCat L) S1 S2 S3 f g Hf Hg).
Qed.

(** Composition of epis in SystemCat *)
Lemma SystemCat_comp_epi : forall (L : Level) (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  is_epi (SystemCat L) S1 S2 f ->
  is_epi (SystemCat L) S2 S3 g ->
  is_epi (SystemCat L) S1 S3 (cat_comp (SystemCat L) S1 S2 S3 g f).
Proof.
  intros L S1 S2 S3 f g Hf Hg.
  exact (comp_epi (SystemCat L) S1 S2 S3 f g Hf Hg).
Qed.

(** Iso in SystemCat implies iso in opposite category *)
Lemma SystemCat_iso_in_opposite : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  is_iso (opposite_cat (SystemCat L)) S2 S1 f.
Proof.
  intros L S1 S2 f Hiso.
  exact (iso_in_opposite (SystemCat L) S1 S2 f Hiso).
Qed.

(* ================================================================= *)
(*  PART VI: P1 CONNECTION — Level Separation (4 Qed)                 *)
(* ================================================================= *)

(** SystemCat at level L1 has no systems with empty criterion domain,
    because no witness w << L1 exists. More precisely: there is no
    valid Criterion at L1 with domain = False or True — the level witness
    condition blocks construction. *)
Lemma no_system_at_L1_with_witness : forall (w : Level), ~ (w << L1).
Proof.
  intros w H. simpl in H. exact H.
Qed.

(** At L1, any system must have its witness below L1, which is impossible.
    Thus: Criterion L1 is only constructible if there exists w << L1.
    But no such w exists. This means: the only systems at L1 are those
    with criteria whose level_valid proof uses an impossible hypothesis. *)

(** If we have a system at L1, its level witness is below L1 — but nothing is *)
Lemma L1_criterion_absurd : forall (C : Criterion L1),
  False.
Proof.
  intros C.
  exact (no_system_at_L1_with_witness
    (crit_level_witness L1 C)
    (crit_level_valid L1 C)).
Qed.

(** SystemCat at L1 is trivially a category with no objects (in essence).
    Any statement about morphisms in SystemCat L1 is vacuously true
    because no System L1 can be constructed. *)
Lemma SystemCat_L1_vacuous : forall (S : System L1) (P : Prop), P.
Proof.
  intros S. exfalso.
  exact (L1_criterion_absurd (sys_criterion L1 S)).
Qed.

(** SystemCat at LS levels always has initial and terminal objects *)
Lemma SystemCat_LS_has_initial_and_terminal : forall (L : Level),
  (exists S, is_initial (SystemCat (LS L)) S) /\
  (exists S, is_terminal (SystemCat (LS L)) S).
Proof.
  intros L. split.
  - exists (empty_system (LS L) L (level_lt_LS L)).
    apply empty_is_initial.
  - exists (unit_system (LS L) L (level_lt_LS L)).
    apply unit_is_terminal.
Qed.

(* ================================================================= *)
(*  Summary: 29 Qed, 0 Admitted, 0 axioms                             *)
(*    1 compose_compat                                                 *)
(*    1 SystemCat_valid                                                *)
(*    3 bridge (comp, id, eq): SystemCat_comp_is_compose,              *)
(*      SystemCat_id_is_id, SystemCat_eq_is_morphism_eq                *)
(*    2 iso bridge: iso_pair_gives_SystemCat_iso,                      *)
(*      SystemCat_iso_gives_iso_pair                                   *)
(*    2 iso/mono bridge: embedding_implies_SystemCat_mono,             *)
(*      surjection_implies_SystemCat_epi                               *)
(*    2 iso: SystemCat_id_iso, SystemCat_iso_compose                   *)
(*    4 empty/unit: empty_morphism_unique, empty_is_initial,           *)
(*      empty_system_LS_is_initial, unit_morphism_unique               *)
(*    1 unit: unit_is_terminal                                         *)
(*    2 universal: SystemCat_initial_unique, SystemCat_terminal_unique *)
(*    3 structural: SystemCat_iso_sym, SystemCat_iso_is_mono,          *)
(*      SystemCat_iso_is_epi                                           *)
(*    3 compositions: SystemCat_comp_mono, SystemCat_comp_epi,         *)
(*      SystemCat_iso_in_opposite                                      *)
(*    4 P1: no_system_at_L1_with_witness, L1_criterion_absurd,         *)
(*      SystemCat_L1_vacuous, SystemCat_LS_has_initial_and_terminal    *)
(* ================================================================= *)
