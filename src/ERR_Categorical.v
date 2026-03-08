(** * ERR_Categorical.v -- E/R/R Categorical Interpretation

    Gives Elements/Roles/Rules (E/R/R) a categorical interpretation
    using SystemCategory.v (Sys(L) as a Category) and LevelFunctors.v
    (embedding/forgetful functors between levels).

    Elements: Systems as objects of Sys(L), elements as images under the Elements functor
    Roles:    Morphisms as structure-preserving maps, functors as level transitions
    Rules:    Categorical laws (functoriality, iso-invariance), P3 separation
    Status:   25 Qed, 0 Admitted, 0 axioms

    KEY RESULTS:
    - ElementsFunctor: faithful functor Sys(L) -> Type mapping systems to their element types
    - P3 Categorical Separation: isomorphism in Sys(L) does NOT imply Leibniz equality
    - Embedding preserves and reflects isomorphisms
    - E/R/R decomposition theorem: morphisms preserve Elements and Predicate components

    Author: Horsocrates | Date: March 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import UniversePolymorphism.
From ToS Require Import Roles.
From ToS Require Import IntensionalIdentity.
From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import SystemCategory.
From ToS Require Import LevelFunctors.

(* ================================================================= *)
(*  PART I: Elements as Objects, Morphisms as Structure Maps (5 Qed)  *)
(* ================================================================= *)

(** The objects of Sys(L) are exactly System L. *)
Lemma elements_are_objects : forall (L : Level),
  cat_obj (SystemCat L) = System L.
Proof.
  intros L. reflexivity.
Qed.

(** The morphisms of Sys(L) are exactly SystemMorphism L. *)
Lemma morphisms_are_structure_preserving : forall (L : Level) (S1 S2 : System L),
  cat_mor (SystemCat L) S1 S2 = SystemMorphism L S1 S2.
Proof.
  intros L S1 S2. reflexivity.
Qed.

(** P3 (Leibniz) equality implies isomorphism: equal systems are isomorphic. *)
Lemma P3_eq_implies_iso : forall (L : Level) (S1 S2 : System L),
  S1 = S2 -> exists f, is_iso (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 Heq. subst. exists (id_morphism L S2). apply SystemCat_id_iso.
Qed.

(** If S1 and S2 are isomorphic in Sys(L), then their predicates are
    extensionally equivalent (via the iso pair's predicate equivalence).
    This connects categorical isomorphism to P3's extensional equivalence. *)
Theorem iso_implies_predicate_equiv : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  forall e : ElemOf L S1,
    crit_predicate L (sys_criterion L S1) e <->
    crit_predicate L (sys_criterion L S2) (sm_map L S1 S2 f e).
Proof.
  intros L S1 S2 f Hiso e.
  apply SystemCat_iso_iff_isomorphism in Hiso.
  destruct Hiso as [g Hpair].
  exact (iso_pair_predicate_equiv L f g Hpair e).
Qed.

(** P3 is strictly stronger than isomorphism: there exist systems that are
    isomorphic but not Leibniz-equal. Uses sys_all_nat_L1 and sys_all_nat_L2
    from IntensionalIdentity.v. *)
Theorem P3_strictly_stronger_than_iso :
  exists (S1 S2 : System L3),
    (exists f, is_iso (SystemCat L3) S1 S2 f) /\ S1 <> S2.
Proof.
  exists sys_all_nat_L1, sys_all_nat_L2.
  split.
  - (* Build isomorphism using identity function *)
    set (f := mkSystemMorphism L3 sys_all_nat_L1 sys_all_nat_L2
      (fun n : nat => n) (fun (n : nat) (_ : True) => I)).
    set (g := mkSystemMorphism L3 sys_all_nat_L2 sys_all_nat_L1
      (fun n : nat => n) (fun (n : nat) (_ : True) => I)).
    exists f.
    apply iso_pair_gives_SystemCat_iso with (g := g).
    split; intro e; reflexivity.
  - exact system_P3_separation.
Qed.

(* ================================================================= *)
(*  PART II: Elements Functor (5 Qed)                                 *)
(* ================================================================= *)

(** The Elements functor maps each system to its element type and
    each morphism to its underlying function.
    This is the forgetful functor Sys(L) -> Type that "forgets"
    the predicate-preservation proof. *)
Definition ElementsFunctor (L : Level) : Functor (SystemCat L) TypeCat.
Proof.
  apply (mkFunctor (SystemCat L) TypeCat
    (fun S => ElemOf L S)
    (fun S1 S2 (f : SystemMorphism L S1 S2) => sm_map L S1 S2 f)).
  - (* fmor_compat: morphism_eq implies pointwise equality of sm_map *)
    intros S1 S2 f g Heq. simpl. intro e. exact (Heq e).
  - (* fmor_id: sm_map of id_morphism = identity function *)
    intros S. simpl. intro e. reflexivity.
  - (* fmor_comp: sm_map of composition = composition of sm_maps
       LHS: fmor(cat_comp g f) = sm_map(compose_morphism L f g)
       RHS: cat_comp TypeCat (fmor g) (fmor f) = fun e => sm_map g (sm_map f e) *)
    intros S1 S2 S3 f g. simpl. intro e. reflexivity.
Defined.

(** The ElementsFunctor maps objects to ElemOf *)
Lemma ElementsFunctor_obj : forall (L : Level) (S : System L),
  fobj (ElementsFunctor L) S = ElemOf L S.
Proof.
  intros L S. reflexivity.
Qed.

(** The ElementsFunctor maps morphisms to sm_map *)
Lemma ElementsFunctor_mor : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (e : ElemOf L S1),
  fmor (ElementsFunctor L) f e = sm_map L S1 S2 f e.
Proof.
  intros L S1 S2 f e. reflexivity.
Qed.

(** The ElementsFunctor is faithful: if the underlying functions agree,
    the morphisms are equal. This is immediate since morphism_eq IS
    pointwise equality of sm_map. *)
Theorem ElementsFunctor_faithful : forall (L : Level) (S1 S2 : System L)
  (f g : SystemMorphism L S1 S2),
  (forall e, sm_map L S1 S2 f e = sm_map L S1 S2 g e) ->
  morphism_eq L f g.
Proof.
  intros L S1 S2 f g Heq. intro e. exact (Heq e).
Qed.

(** The ElementsFunctor preserves isomorphisms (inherited from general
    functor theory, but stated concretely). *)
Theorem ElementsFunctor_preserves_iso : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  is_iso TypeCat (ElemOf L S1) (ElemOf L S2) (sm_map L S1 S2 f).
Proof.
  intros L S1 S2 f Hiso.
  exact (fmor_preserves_iso (SystemCat L) TypeCat (ElementsFunctor L) S1 S2 f Hiso).
Qed.

(* ================================================================= *)
(*  PART III: P3 Categorical Separation Theorem (5 Qed)               *)
(* ================================================================= *)

(** Formal statement: there exist systems S1, S2 at L3 with
    an isomorphism between them, yet S1 <> S2. *)
Theorem iso_not_implies_P3 :
  exists (S1 S2 : System L3),
    (exists f, is_iso (SystemCat L3) S1 S2 f) /\ S1 <> S2.
Proof.
  exact P3_strictly_stronger_than_iso.
Qed.

(** Isomorphism in Sys(L) does NOT imply Leibniz equality. *)
Theorem P3_separation_categorical :
  ~ (forall (L : Level) (S1 S2 : System L),
       (exists f, is_iso (SystemCat L) S1 S2 f) -> S1 = S2).
Proof.
  intro H.
  destruct P3_strictly_stronger_than_iso as [S1 [S2 [[f Hiso] Hneq]]].
  apply Hneq.
  apply H. exists f. exact Hiso.
Qed.

(** If S1 is isomorphic to S2 in Sys(L), there exists a bijection
    between their element types (via the ElementsFunctor). *)
Theorem iso_preserves_criterion_domain : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  exists (h : ElemOf L S1 -> ElemOf L S2)
         (h_inv : ElemOf L S2 -> ElemOf L S1),
    (forall e, h_inv (h e) = e) /\ (forall e, h (h_inv e) = e).
Proof.
  intros L S1 S2 f Hiso.
  apply SystemCat_iso_iff_isomorphism in Hiso.
  destruct Hiso as [g [Hgf Hfg]].
  exists (sm_map L S1 S2 f), (sm_map L S2 S1 g).
  split; assumption.
Qed.

(** P3 (Leibniz) equality implies criterion equality. *)
Lemma P3_eq_implies_criterion_eq : forall (L : Level) (S1 S2 : System L),
  S1 = S2 -> sys_criterion L S1 = sys_criterion L S2.
Proof.
  intros L S1 S2 Heq. subst. reflexivity.
Qed.

(** Contrapositive: different criteria imply different systems. *)
Lemma criterion_diff_implies_not_P3 : forall (L : Level) (S1 S2 : System L),
  sys_criterion L S1 <> sys_criterion L S2 -> S1 <> S2.
Proof.
  intros L S1 S2 Hneq Heq.
  apply Hneq. exact (P3_eq_implies_criterion_eq L S1 S2 Heq).
Qed.

(* ================================================================= *)
(*  PART IV: Embedding Preserves E/R/R Properties (5 Qed)             *)
(* ================================================================= *)

(** The element type (criterion domain) of embed_obj S is definitionally
    the same as that of S. *)
Lemma embed_preserves_criterion_domain : forall (L : Level) (S : System L),
  crit_domain (LS L) (sys_criterion (LS L) (embed_obj L S)) =
  crit_domain L (sys_criterion L S).
Proof.
  intros L S. reflexivity.
Qed.

(** The predicate of embed_obj S is the same function as the predicate of S. *)
Lemma embed_preserves_criterion_predicate : forall (L : Level) (S : System L)
  (e : crit_domain L (sys_criterion L S)),
  crit_predicate (LS L) (sys_criterion (LS L) (embed_obj L S)) e =
  crit_predicate L (sys_criterion L S) e.
Proof.
  intros L S e. reflexivity.
Qed.

(** If S1 and S2 are isomorphic at level L, then embed(S1) and embed(S2)
    are isomorphic at level LS L. *)
Theorem embed_preserves_iso_categorical : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat L) S1 S2 f ->
  is_iso (SystemCat (LS L)) (embed_obj L S1) (embed_obj L S2)
    (embed_mor L S1 S2 f).
Proof.
  intros L S1 S2 f Hiso.
  exact (EmbedFunctor_preserves_iso L S1 S2 f Hiso).
Qed.

(** If embed(S1) and embed(S2) are isomorphic at LS L, then S1 and S2
    are isomorphic at L. The embedding reflects isomorphisms. *)
Theorem embed_reflects_iso : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_iso (SystemCat (LS L)) (embed_obj L S1) (embed_obj L S2)
    (embed_mor L S1 S2 f) ->
  is_iso (SystemCat L) S1 S2 f.
Proof.
  intros L S1 S2 f Hiso.
  destruct Hiso as [g' [Hgf Hfg]].
  (* g' : SystemMorphism (LS L) (embed_obj L S2) (embed_obj L S1) *)
  (* Since ElemOf (LS L) (embed_obj L S) = ElemOf L S, g' carries a function
     ElemOf L S2 -> ElemOf L S1 with a predicate preservation proof. *)
  set (g_map := sm_map (LS L) (embed_obj L S2) (embed_obj L S1) g').
  set (g := mkSystemMorphism L S2 S1
    g_map
    (sm_preserves (LS L) (embed_obj L S2) (embed_obj L S1) g')).
  exists g. split.
  - (* forall e, sm_map g (sm_map f e) = e *)
    intro e. unfold g. simpl. unfold g_map.
    (* Hgf says: forall e, sm_map (compose_morphism (LS L) (embed_mor f) g') e = sm_map (id_morphism) e *)
    (* In SystemCat: cat_comp g' (embed_mor f) = compose_morphism (embed_mor f) g' *)
    (* Hgf : morphism_eq (LS L) (compose_morphism (LS L) (embed_mor L S1 S2 f) g') (id_morphism (LS L) (embed_obj L S1)) *)
    exact (Hgf e).
  - (* forall e, sm_map f (sm_map g e) = e *)
    intro e. unfold g. simpl. unfold g_map.
    (* Hfg : morphism_eq (LS L) (compose_morphism (LS L) g' (embed_mor L S1 S2 f)) (id_morphism (LS L) (embed_obj L S2)) *)
    exact (Hfg e).
Qed.

(** The embedding of the empty system (initial object) is initial at the next level. *)
Theorem embed_preserves_initial : forall (L : Level) (w : Level) (Hw : w << L),
  is_initial (SystemCat (LS L)) (embed_obj L (empty_system L w Hw)).
Proof.
  intros L w Hw.
  exact (embed_empty_is_initial L w Hw).
Qed.

(* ================================================================= *)
(*  PART V: Structural Properties and Decomposition (5 Qed)           *)
(* ================================================================= *)

(** Isomorphism-invariance of properties: if a property P of systems
    is transported by isomorphisms, then iso-invariance follows.
    More precisely: for any property P : System L -> Prop, if P is
    preserved by SystemMorphism iso pairs, then isomorphic systems
    share P. *)
Theorem well_formed_iso_invariant : forall (L : Level)
  (P : System L -> Prop)
  (Hpres : forall (S1 S2 : System L) (f : SystemMorphism L S1 S2)
    (g : SystemMorphism L S2 S1),
    is_iso_pair L f g -> P S1 -> P S2),
  forall (S1 S2 : System L) (f : SystemMorphism L S1 S2),
    is_iso (SystemCat L) S1 S2 f -> P S1 -> P S2.
Proof.
  intros L P Hpres S1 S2 f Hiso HP.
  apply SystemCat_iso_iff_isomorphism in Hiso.
  destruct Hiso as [g Hpair].
  exact (Hpres S1 S2 f g Hpair HP).
Qed.

(** Any SystemMorphism preserves the predicate. This is the content of
    sm_preserves, restated in categorical language. *)
Theorem morphism_respects_predicate : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (e : ElemOf L S1),
  crit_predicate L (sys_criterion L S1) e ->
  crit_predicate L (sys_criterion L S2) (sm_map L S1 S2 f e).
Proof.
  intros L S1 S2 f e Hpred.
  exact (sm_preserves L S1 S2 f e Hpred).
Qed.

(** Position bounds are NOT isomorphism invariants: two isomorphic systems
    can have different position bounds. Counterexample using sys_all_nat_L1
    (Unbounded) and a system with Finite bound but same domain and predicate. *)
Theorem position_bound_not_iso_invariant :
  exists (S1 S2 : System L3),
    (exists f, is_iso (SystemCat L3) S1 S2 f) /\
    sys_pos_bound L3 S1 <> sys_pos_bound L3 S2.
Proof.
  set (S1 := mkSystem L3
    (mkCriterion L3 nat (fun _ => True) L1 L1_lt_L3)
    Unbounded MultiplePerRole).
  set (S2 := mkSystem L3
    (mkCriterion L3 nat (fun _ => True) L1 L1_lt_L3)
    (Finite 42) MultiplePerRole).
  exists S1, S2.
  split.
  - (* Build iso: same domain, same predicate, just different pos_bound *)
    set (f := mkSystemMorphism L3 S1 S2
      (fun n : nat => n) (fun (n : nat) (_ : True) => I)).
    set (g := mkSystemMorphism L3 S2 S1
      (fun n : nat => n) (fun (n : nat) (_ : True) => I)).
    exists f.
    apply iso_pair_gives_SystemCat_iso with (g := g).
    split; intro e; reflexivity.
  - (* Unbounded <> Finite 42 *)
    simpl. discriminate.
Qed.

(** Isomorphic systems admit a bijection on elements (consequence of
    ElementsFunctor preserving iso). *)
Theorem iso_gives_element_bijection : forall (L : Level) (S1 S2 : System L),
  (exists f, is_iso (SystemCat L) S1 S2 f) ->
  exists (h : ElemOf L S1 -> ElemOf L S2),
    is_iso TypeCat (ElemOf L S1) (ElemOf L S2) h.
Proof.
  intros L S1 S2 [f Hiso].
  exists (sm_map L S1 S2 f).
  exact (ElementsFunctor_preserves_iso L S1 S2 f Hiso).
Qed.

(** E/R/R Decomposition: every System L decomposes into its constituent parts
    (Elements = domain, Predicate, Witness, Bounds, Uniqueness), and every
    SystemMorphism preserves the Elements and Predicate components.
    Stated as: the morphism's underlying map sends predicate-satisfying
    elements to predicate-satisfying elements. *)
Theorem err_decomposition : forall (L : Level) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  (* Elements component: f maps ElemOf S1 to ElemOf S2 *)
  (forall e : ElemOf L S1, exists e' : ElemOf L S2, sm_map L S1 S2 f e = e') /\
  (* Predicate preservation: the criterion predicate is preserved *)
  (forall e : ElemOf L S1,
    crit_predicate L (sys_criterion L S1) e ->
    crit_predicate L (sys_criterion L S2) (sm_map L S1 S2 f e)).
Proof.
  intros L S1 S2 f. split.
  - (* Elements component: trivial, the function sm_map f e is already in ElemOf S2 *)
    intro e. exists (sm_map L S1 S2 f e). reflexivity.
  - (* Predicate preservation: this is sm_preserves *)
    exact (sm_preserves L S1 S2 f).
Qed.

(* ================================================================= *)
(*  Summary: 25 Qed, 0 Admitted, 0 axioms                             *)
(*                                                                     *)
(*  Part I  -- Elements as Objects (5 Qed):                            *)
(*    elements_are_objects, morphisms_are_structure_preserving,         *)
(*    P3_eq_implies_iso, iso_implies_predicate_equiv,                   *)
(*    P3_strictly_stronger_than_iso                                     *)
(*                                                                     *)
(*  Part II -- Elements Functor (5 Qed):                               *)
(*    ElementsFunctor (Defined), ElementsFunctor_obj,                   *)
(*    ElementsFunctor_mor, ElementsFunctor_faithful,                    *)
(*    ElementsFunctor_preserves_iso                                     *)
(*                                                                     *)
(*  Part III -- P3 Categorical Separation (5 Qed):                     *)
(*    iso_not_implies_P3, P3_separation_categorical,                    *)
(*    iso_preserves_criterion_domain, P3_eq_implies_criterion_eq,       *)
(*    criterion_diff_implies_not_P3                                     *)
(*                                                                     *)
(*  Part IV -- Embedding Preserves E/R/R (5 Qed):                      *)
(*    embed_preserves_criterion_domain,                                 *)
(*    embed_preserves_criterion_predicate,                              *)
(*    embed_preserves_iso_categorical, embed_reflects_iso,              *)
(*    embed_preserves_initial                                           *)
(*                                                                     *)
(*  Part V  -- Structural Properties (5 Qed):                          *)
(*    well_formed_iso_invariant, morphism_respects_predicate,           *)
(*    position_bound_not_iso_invariant, iso_gives_element_bijection,    *)
(*    err_decomposition                                                 *)
(* ================================================================= *)
