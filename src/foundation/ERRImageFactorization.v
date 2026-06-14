(** * ERRImageFactorization.v — every morphism factors as (epi onto its image) ∘ (mono inclusion).

    The regular-category image factorization for E/R/R systems.  The IMAGE of f : S1 → S2 is the
    sub-system of S2 on the hit elements {y | ∃x, f x = y}.  Every morphism corestricts onto its
    image (an epi) followed by the inclusion of the image (a mono):  f = corestrict ; im_incl.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      every morphism passes through its IMAGE — the sub-system of the target on the elements actually
      hit; the factorization f = (epi onto image) ∘ (mono inclusion) is the regular-category structure.
      The image's Rules = the restriction-stable Rules of the target.
    Roles (L4): corestrict (epi onto the image, Roles-preserving) and im_incl (mono inclusion, with the
      target's Roles restricted to the image); the image's Roles = the target's, restricted.
    Elements (L1+P4): the image carrier = the hit elements (an ∃-defined sub-collection); corestrict
      sends x to f x viewed as an element of the image.
    P4 diagnostic (could it be otherwise?):
      the image is a SUB-system (carve by the ∃-predicate — an Element-side act, decidable when the
      fibers are); the image is forced (= exactly the hit elements); the only freedom — the inclusion's
      mono-ness (sig-injectivity) — is the proof-irrelevance wall.
    Honesty wall:
      the factorization and the epi-onto-the-image-carrier are proved 0-axiom; the inclusion's full
      mono-ness (left-cancellation) needs proof-irrelevance on the image predicate (∃, a Prop) — the
      SAME wall as the first-iso theorem and the equalizer, decidable-dissolvable (UIP_dec, cf
      ERRFiniteQuotient).  So we give the factorization + the carrier-surjective epi + the inclusion,
      and flag mono = PI.  Reuses fs_subsystem / fs_incl / equiv_restriction_stable (ERRTierIIResidue).
      0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.    (* ERRMorphism, err_map, err_pres, err_comp, err_morph_eq, mkERRMorphism *)
From ToS Require Import foundation.ERRTierIIResidue.   (* fs_subsystem, fs_incl, equiv_restriction_stable *)
From ToS Require Import foundation.ERRQuotient.         (* SDisc *)
From ToS Require Import foundation.ERRFirstIso.         (* fconst *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  The image object and the mono inclusion                                *)
(* ===================================================================== *)

(** The image predicate: the elements of S2 actually hit by f. *)
Definition im_pred {L} {S1 S2 : FunctionalSystem L} (f : ERRMorphism S1 S2)
  : get_Elements S2 -> Prop := fun y => exists x, err_map f x = y.

(** ★★ The IMAGE of f = the sub-system of S2 on the hit elements. *)
Definition fs_image {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2)
  : FunctionalSystem L :=
  fs_subsystem EquivalenceConstitution equiv_restriction_stable S2 H2 (im_pred f).

Lemma fs_image_carrier {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2) :
  get_Elements (fs_image H2 f) = { y : get_Elements S2 | exists x, err_map f x = y }.
Proof. reflexivity. Qed.

(** The MONO part: the inclusion of the image into S2. *)
Definition im_incl {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2)
  : ERRMorphism (fs_image H2 f) S2 :=
  fs_incl EquivalenceConstitution equiv_restriction_stable S2 H2 (im_pred f).

(** The inclusion's action is the projection (its mono-ness is the PI wall). *)
Lemma im_incl_proj {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2)
  (p : get_Elements (fs_image H2 f)) :
  err_map (im_incl H2 f) p = proj1_sig p.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The epi onto the image                                                 *)
(* ===================================================================== *)

(** ★★ The EPI part: f corestricted onto its image (x ↦ f x, witnessed as a hit element). *)
Definition corestrict {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2)
  : ERRMorphism S1 (fs_image H2 f).
Proof.
  refine (@mkERRMorphism L S1 (fs_image H2 f)
            (fun x => exist (im_pred f) (err_map f x) (ex_intro _ x eq_refl)) _).
  intros a b Hab. exact (err_pres f a b Hab).
Defined.

(** The corestriction's action, viewed in S2, is just f. *)
Lemma corestrict_proj {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2) (x : get_Elements S1) :
  proj1_sig (err_map (corestrict H2 f) x) = err_map f x.
Proof. reflexivity. Qed.

(** ★ The corestriction is SURJECTIVE onto the image carrier (the epi, at carrier level). *)
Lemma corestrict_surjective {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2) :
  forall y : get_Elements (fs_image H2 f),
    exists x, proj1_sig (err_map (corestrict H2 f) x) = proj1_sig y.
Proof.
  intros [y0 Hy0]. destruct Hy0 as [x Hx]. exists x. exact Hx.
Qed.

(* ===================================================================== *)
(*  The factorization                                                      *)
(* ===================================================================== *)

(** ★★ THE IMAGE FACTORIZATION:  f = corestrict ; im_incl. *)
Lemma image_factor {L} {S1 S2 : FunctionalSystem L}
  (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2) :
  err_morph_eq (err_comp (corestrict H2 f) (im_incl H2 f)) f.
Proof. intro x. reflexivity. Qed.

(* ===================================================================== *)
(*  Concrete grounding                                                     *)
(* ===================================================================== *)

(** The image of the constant-true map on the discrete bool system is exactly {true}. *)
Lemma image_fconst_true : im_pred fconst true.
Proof. exists true. reflexivity. Qed.

Lemma image_fconst_not_false : ~ im_pred fconst false.
Proof. intros [x H]. discriminate H. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ EVERY MORPHISM FACTORS THROUGH ITS IMAGE.
      (object)  the image is the sub-system of the target on the hit elements {y | ∃x, f x = y};
      (factor)  f = corestrict ; im_incl  (epi onto the image, then the inclusion);
      (epi)     the corestriction is surjective onto the image carrier;
      (image)   concretely, the image of the constant-true map on bool is {true}.
    This is the regular-category image factorization for E/R/R systems.  Honest: the inclusion's full
    mono-ness is the proof-irrelevance wall (decidable-dissolvable), so the epi is stated at carrier
    level and the factorization at the err_map level. *)
Theorem err_image_factorization :
  (forall (L : Level) (S1 S2 : FunctionalSystem L)
      (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2),
      get_Elements (fs_image H2 f) = { y : get_Elements S2 | exists x, err_map f x = y })
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L)
        (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2),
        err_morph_eq (err_comp (corestrict H2 f) (im_incl H2 f)) f)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L)
        (H2 : fs_constitution S2 = EquivalenceConstitution) (f : ERRMorphism S1 S2),
        forall y : get_Elements (fs_image H2 f),
          exists x, proj1_sig (err_map (corestrict H2 f) x) = proj1_sig y).
Proof.
  split; [ | split ].
  - intros L S1 S2 H2 f. exact (fs_image_carrier H2 f).
  - intros L S1 S2 H2 f. exact (image_factor H2 f).
  - intros L S1 S2 H2 f. exact (corestrict_surjective H2 f).
Qed.

Print Assumptions err_image_factorization.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Image factorization (regular-category structure).  im_pred (the hit       *)
(*  elements) + fs_image (= sub-system of S2 on them) + fs_image_carrier.     *)
(*  im_incl (mono inclusion) + im_incl_proj.  corestrict (epi onto the image) *)
(*  + corestrict_proj + corestrict_surjective (carrier-level epi).  image_    *)
(*  factor (f = corestrict ; im_incl).  image_fconst_true / _not_false        *)
(*  (concrete: image of const-true on bool = {true}).  Capstone err_image_    *)
(*  factorization.  HONEST: the inclusion's full mono-ness is the proof-       *)
(*  irrelevance wall (decidable-dissolvable); epi at carrier level, factor at  *)
(*  the err_map level.                                                        *)
(* ========================================================================= *)
