(** * ERR2CategoryHom.v — the internal hom-object: the E/R/R category is ENRICHED OVER ITSELF.

    ERR2Category.v showed the Roles tier IS the 2-cell structure (Roles2 = a "Roles-homotopy"
    between parallel morphisms).  This file takes the next step: the set of morphisms between
    two systems, equipped with Roles2 as its Roles, IS ITSELF A FunctionalSystem.

      fs_hom S1 S2  :  FunctionalSystem (LS L)
        Elements = ERRMorphism S1 S2   (the morphisms ARE the elements)
        Roles    = Roles2              (the 2-cells ARE the roles)
        Rules    = EquivalenceConstitution

    So "hom of two systems is again a system" — the category is enriched over itself, and the
    hom-object lives ONE LEVEL UP (Products(L)=Elements(L+1) for the morphism tier).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the Constitution of the hom-object is the EquivalenceConstitution, and it holds precisely
      because Roles2 is reflexive / symmetric / transitive (ERR2Category) — which needs the
      TARGET S2 to have an equivalence Roles (roles_equiv S2).  Same Rules gate; here it makes
      the hom-OBJECT itself a well-constituted system.
    Roles (L4): the hom-object's Roles ARE the 2-cells (Roles2) — the second dimension of the
      base category becomes the FIRST dimension (Roles) of the object one level up.  Composition
      respects these Roles (the internal composition is a role-morphism = the enrichment).
    Elements (L1+P4): the carrier of the hom-object is the type of morphisms; each morphism is
      an actual map (a rule on the base carrier), assigned the systems' level L; the hom-object
      sits at LS L.  No completed infinity — a system at the next level whose elements are maps.
    P4 diagnostic (could it be otherwise?):
      the level is forced by P1 hierarchy: morphisms BETWEEN L-systems actualize as ELEMENTS of
      an (L+1)-system — this is exactly Products(L)=Elements(L+1) applied to the morphism tier.
      That the construction CLOSES (the hom-object is again an equivalence-system, so you can take
      hom of homs) is what "enriched over itself" means, and it is proved, not posited.
    Honesty wall:
      the hom-object is an equivalence-system only when the target has roles_equiv (the gate);
      the level assignment (morphism ↦ L) is a structural choice (bookkeeping, not deep);
      we prove the internal composition RESPECTS the hom-Roles (enrichment compatibility), but do
      NOT package the enriched composition as a single morphism  hom⊗hom → hom  (that needs the
      product of hom-objects + a map out of it — more machinery).  Reuses ERR2Category + the
      witness systems SB (full) / SDisc (discrete).  0 axioms.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.    (* ERRMorphism, err_map, err_comp, err_id, err_morph_eq *)
From ToS Require Import foundation.ERR2Category.        (* roles_equiv, equiv_system_roles_equiv, Roles2, Roles2_refl/sym/trans, Roles2_hcomp, Roles2_on_discrete_iff_eq *)
From ToS Require Import foundation.ERRDynamics.          (* SB : full-Roles bool system *)
From ToS Require Import foundation.ERRDynamicsArrow.     (* flip *)
From ToS Require Import foundation.ERRQuotient.          (* SDisc : discrete bool system *)

(* Record projections lose their implicit {L} across import — re-add. *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  The internal hom-object                                                *)
(* ===================================================================== *)

(** ★★ The HOM-OBJECT: morphisms-as-elements, 2-cells-as-Roles, equivalence-as-Rules.
    It lives one level up (LS L); each morphism (element) is assigned the systems' level L. *)
Definition fs_hom {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2)
  : FunctionalSystem (LS L).
Proof.
  refine (@mkFunctionalSystem (LS L)
            EquivalenceConstitution
            (ERRMorphism S1 S2)
            (@Roles2 L S1 S2)
            _
            (fun _ => L)
            (fun _ => _)).
  - unfold EquivalenceConstitution. split; [ | split ].
    + intro f. exact (Roles2_refl He f).
    + intros f g Hfg. exact (Roles2_sym He Hfg).
    + intros f g h Hfg Hgh. exact (Roles2_trans He Hfg Hgh).
  - simpl. left. reflexivity.
Defined.

(** The hom-object's triad reads off exactly: Elements / Roles / Rules. *)
Lemma fs_hom_elements {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2) :
  get_Elements (fs_hom S1 S2 He) = ERRMorphism S1 S2.
Proof. reflexivity. Qed.

Lemma fs_hom_roles {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2) :
  get_Roles (fs_hom S1 S2 He) = @Roles2 L S1 S2.
Proof. reflexivity. Qed.

Lemma fs_hom_rules {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2) :
  fs_constitution (fs_hom S1 S2 He) = EquivalenceConstitution.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  CLOSURE: the construction is enriched OVER ITSELF (it iterates)        *)
(* ===================================================================== *)

(** ★★ The hom-object is AGAIN an equivalence-system — so it is itself a valid TARGET, and the
    hom-construction can be iterated.  This is exactly what "enriched over itself" requires. *)
Lemma fs_hom_roles_equiv {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2) :
  roles_equiv (fs_hom S1 S2 He).
Proof. apply equiv_system_roles_equiv. exact (fs_hom_rules S1 S2 He). Qed.

(** Iteration made concrete: hom of the hom-object with itself is well-formed, two levels up.
    Its carrier = morphisms-between-hom-objects = the 2-cells re-presented as 1-morphisms. *)
Definition hom_iterated {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2)
  : FunctionalSystem (LS (LS L)) :=
  fs_hom (fs_hom S1 S2 He) (fs_hom S1 S2 He) (fs_hom_roles_equiv S1 S2 He).

Lemma hom_iterated_carrier {L} (S1 S2 : FunctionalSystem L) (He : roles_equiv S2) :
  get_Elements (hom_iterated S1 S2 He)
  = ERRMorphism (fs_hom S1 S2 He) (fs_hom S1 S2 He).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The internal composition is a role-morphism (enrichment compatibility) *)
(* ===================================================================== *)

(** ★★ Composition RESPECTS the hom-objects' Roles: if f,g are 2-cell-related in hom(S1,S2)
    and f',g' in hom(S2,S3), then their composites are 2-cell-related in hom(S1,S3).  This is
    Roles2_hcomp read in the language of the hom-objects = the enriched composition is continuous. *)
Lemma hom_comp_is_role_morphism {L} {S1 S2 S3 : FunctionalSystem L}
  (He2 : roles_equiv S2) (He3 : roles_equiv S3)
  (f g : ERRMorphism S1 S2) (f' g' : ERRMorphism S2 S3) :
  get_Roles (fs_hom S1 S2 He2) f g ->
  get_Roles (fs_hom S2 S3 He3) f' g' ->
  get_Roles (fs_hom S1 S3 He3) (err_comp f f') (err_comp g g').
Proof. intros H1 H2. exact (Roles2_hcomp He3 H1 H2). Qed.

(* ===================================================================== *)
(*  The hom-object's Roles are governed by the TARGET's Rules              *)
(* ===================================================================== *)

(** SB has the full Roles ⟹ its endo-hom-object relates DISTINCT maps (id and flip) as a Role:
    a genuine 2-cell living inside the hom-system. *)
Lemma SB_roles_equiv : roles_equiv SB.
Proof. unfold roles_equiv. split; [ | split ]; intros; exact I. Qed.

Lemma flip_id_related_in_hom :
  get_Roles (fs_hom SB SB SB_roles_equiv) (err_id SB) flip.
Proof. intro x. exact I. Qed.

(** SDisc has discrete Roles ⟹ its hom-object's own Roles ARE morphism equality: the hom-system
    "remembers" exactly equality of maps as its finest relation. *)
Definition SDisc_roles_equiv : roles_equiv SDisc :=
  equiv_system_roles_equiv SDisc eq_refl.

Lemma hom_into_discrete_roles_is_eq (S1 : FunctionalSystem L2) (f g : ERRMorphism S1 SDisc) :
  get_Roles (fs_hom S1 SDisc SDisc_roles_equiv) f g <-> err_morph_eq f g.
Proof. exact (Roles2_on_discrete_iff_eq S1 f g). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE E/R/R CATEGORY IS ENRICHED OVER ITSELF.
      (triad)    hom(S1,S2) is a genuine FunctionalSystem: Elements = morphisms, Roles = 2-cells,
                 Rules = equivalence;
      (closure)  it is again an equivalence-system ⟹ the construction iterates (hom of homs);
      (enriched) internal composition respects the hom-objects' Roles (the enrichment is continuous);
      (graded)   the hom-object's own Roles are governed by the target's Rules — full target gives
                 2-cells joining distinct maps, discrete target gives 2-cells = map equality.
    The second dimension of the base category (Roles-as-2-cells) becomes the first dimension
    (Roles) of an object one level up — Products(L)=Elements(L+1) for the morphism tier. *)
Theorem err_internal_hom :
  (forall (L : Level) (S1 S2 : FunctionalSystem L) (He : roles_equiv S2),
     get_Elements (fs_hom S1 S2 He) = ERRMorphism S1 S2
     /\ get_Roles (fs_hom S1 S2 He) = @Roles2 L S1 S2
     /\ fs_constitution (fs_hom S1 S2 He) = EquivalenceConstitution)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (He : roles_equiv S2),
        roles_equiv (fs_hom S1 S2 He))
  /\ (forall (L : Level) (S1 S2 S3 : FunctionalSystem L)
        (He2 : roles_equiv S2) (He3 : roles_equiv S3)
        (f g : ERRMorphism S1 S2) (f' g' : ERRMorphism S2 S3),
        get_Roles (fs_hom S1 S2 He2) f g ->
        get_Roles (fs_hom S2 S3 He3) f' g' ->
        get_Roles (fs_hom S1 S3 He3) (err_comp f f') (err_comp g g'))
  /\ get_Roles (fs_hom SB SB SB_roles_equiv) (err_id SB) flip
  /\ (forall (S1 : FunctionalSystem L2) (f g : ERRMorphism S1 SDisc),
        get_Roles (fs_hom S1 SDisc SDisc_roles_equiv) f g <-> err_morph_eq f g).
Proof.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros L S1 S2 He. split; [ | split ].
    + exact (fs_hom_elements S1 S2 He).
    + exact (fs_hom_roles S1 S2 He).
    + exact (fs_hom_rules S1 S2 He).
  - intros L S1 S2 He. exact (fs_hom_roles_equiv S1 S2 He).
  - intros L S1 S2 S3 He2 He3 f g f' g'. exact (hom_comp_is_role_morphism He2 He3 f g f' g').
  - exact flip_id_related_in_hom.
  - exact hom_into_discrete_roles_is_eq.
Qed.

Print Assumptions err_internal_hom.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  10 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The internal hom-object: the E/R/R category enriched over itself.         *)
(*  fs_hom (morphisms = Elements, Roles2 = Roles, equivalence = Rules, at     *)
(*  level LS L) + fs_hom_elements/roles/rules (triad).  fs_hom_roles_equiv    *)
(*  (CLOSURE: the hom-object is again equiv ⟹ iterates) + hom_iterated/       *)
(*  _carrier (hom of homs, two levels up).  hom_comp_is_role_morphism (the    *)
(*  internal composition respects the hom-Roles = enrichment compatibility).  *)
(*  SB_roles_equiv + flip_id_related_in_hom (full target ⟹ 2-cell joining     *)
(*  distinct maps lives in the hom) vs SDisc_roles_equiv + hom_into_discrete_ *)
(*  roles_is_eq (discrete target ⟹ hom-Roles = map equality).  Capstone       *)
(*  err_internal_hom.  HONEST: equiv-system only under the target gate; level *)
(*  assignment structural; enriched-composition-as-a-single-morphism not      *)
(*  packaged (compatibility shown).  0 axioms.                                *)
(* ========================================================================= *)
