(** * ERRFirstIso.v — the first isomorphism theorem, made precise for the Roles-preserving category:
      it is exactly the OBSTACLE (c) analysis turned into a machine-checked theorem.

    Classically S/ker f ≅ im f.  In our category (morphisms PRESERVE Roles, not equality) we showed
    three obstacles; (a) carrier quotient-types and (b) proof irrelevance are UNFORCED (sidestepped by
    coarsening Roles / extensional identity), while (c) — "the kernel pair is a congruence" — is the
    genuine structural one.  This file proves exactly when (c) dissolves and what residue remains:

      ★ kernel f := (f x = f y) is ALWAYS an equivalence (kernel_equiv).
      ★ kernel f is a CONGRUENCE (⊇ Roles) IFF f is Roles-collapsing — it sends Roles-related elements
        to EQUAL ones (kernel_congruence_iff_roles_collapsing).  This is obstacle (c), exactly located:
        morphisms only preserve Roles, so the kernel-by-equality aligns with the Roles only for
        Roles-collapsing f.
      ★ For a Roles-collapsing f (into an equivalence-target), the FIRST ISO FRAGMENT holds 0-axiom:
        f factors as an EPI (the ④ kernel-quotient) followed by the mediator (first_iso_factor +
        first_iso_epi) — no quotient-type, no proof irrelevance.
      ★ The RESIDUE is exactly obstacle (a): the mediator is injective (so "≅ im f" would hold) IFF f
        is injective on the CARRIER (mediator_inj_iff_f_inj).  The coarsen-Roles quotient keeps the
        carrier, so it buys NO injectivity — the iso-onto-image step still needs carrier-merge (a).
      ★ Witness fconst (constant on a discrete source): Roles-collapsing, so it FACTORS, yet its
        mediator is NOT injective (fconst_factors_but_not_iso) — the residue is real.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      ker f is always an equivalence; it is a CONGRUENCE iff f is Roles-collapsing; for such f, f
      factors as epi (the kernel-quotient) ∘ mediator (the surviving first-iso fragment, 0-axiom); the
      "iso onto the image" step holds iff the mediator is injective, which equals f being injective on
      the CARRIER — exactly the residual obstacle (a).
    Roles (L4): kernel; roles_collapsing; the factorization (first_iso_factor / _epi); the residue
      (mediator_inj_iff_f_inj); the witness fconst.
    Elements (L1+P4): the morphism f; the carriers; the witness fconst.
    P4 diagnostic (could it be otherwise?):
      (c) dissolves EXACTLY when f collapses Roles to equality (roles_collapsing) — a forced condition
      on f, not an axiom.  What then remains (iso onto the image) is the UNFORCED carrier-merge (a),
      here proved to be precisely carrier-injectivity of f.
    Honesty wall:
      this is the FRAGMENT of the first iso theorem that holds 0-axiom in this category — factorization
      through the kernel-quotient (the ④ coarsen-Roles quotient) for Roles-collapsing f; the FULL
      S/ker f ≅ im f (iso onto the image) still needs carrier-merge = (a), and we PROVE the residue is
      exactly carrier-injectivity.  Needs the target to be an equivalence-system (for the mediator's
      Roles-preservation: Roles-related images are equal, hence T-related by reflexivity).  Reuses
      ERRComposition + ERRQuotient + ERRIso.  0 axioms.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, mkERRMorphism, err_map, err_comp, err_morph_eq *)
From ToS Require Import foundation.ERRQuotient.       (* congruence, fs_quotient, fs_quot, fs_quot_mediator, fs_quot_surjective, surjective, SDisc *)
From ToS Require Import foundation.ERRIso.            (* injective_map *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE KERNEL and the ROLES-COLLAPSING condition                         *)
(* ===================================================================== *)

(** The kernel pair of f: identified iff f sends them to the same target element. *)
Definition kernel {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  : get_Elements S -> get_Elements S -> Prop := fun x y => err_map f x = err_map f y.

(** f is ROLES-COLLAPSING if it sends Roles-related elements to EQUAL ones. *)
Definition roles_collapsing {L} {S T : FunctionalSystem L} (f : ERRMorphism S T) : Prop :=
  forall x y, get_Roles S x y -> err_map f x = err_map f y.

(** ★ The kernel is ALWAYS an equivalence (it is built from equality). *)
Lemma kernel_equiv : forall {L} {S T : FunctionalSystem L} (f : ERRMorphism S T),
  EquivalenceConstitution (get_Elements S) (kernel f).
Proof.
  intros L S T f. unfold EquivalenceConstitution, kernel. split; [ | split ].
  - intro x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z Hxy Hyz. transitivity (err_map f y); assumption.
Qed.

(** ★★ OBSTACLE (c), located exactly: the kernel is a CONGRUENCE iff f is Roles-collapsing.  (A
    morphism only preserves Roles, so the kernel-by-equality contains the Roles precisely when f
    collapses Roles to equality.) *)
Lemma kernel_congruence_iff_roles_collapsing :
  forall {L} {S T : FunctionalSystem L} (f : ERRMorphism S T),
  congruence S (kernel f) <-> roles_collapsing f.
Proof.
  intros L S T f. unfold congruence, roles_collapsing, kernel. split.
  - intros [_ H2]. exact H2.
  - intro H. split; [ exact (kernel_equiv f) | exact H ].
Qed.

(** The congruence handle for a Roles-collapsing f. *)
Definition kernel_cong {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  (Hrc : roles_collapsing f) : congruence S (kernel f) :=
  proj2 (kernel_congruence_iff_roles_collapsing f) Hrc.

(* ===================================================================== *)
(*  THE FIRST ISO FRAGMENT — factor through the kernel-quotient            *)
(* ===================================================================== *)

(** The Roles of an equivalence-system are reflexive. *)
Lemma roles_refl_of_equiv : forall {L} (T : FunctionalSystem L),
  fs_constitution T = EquivalenceConstitution -> forall y, get_Roles T y y.
Proof.
  intros L T HT y.
  assert (Heq : EquivalenceConstitution (get_Elements T) (get_Roles T))
    by (rewrite <- HT; exact (fs_functional T)).
  destruct Heq as [Hr _]. exact (Hr y).
Qed.

(** The kernel-quotient of S by f's kernel (the ④ coarsen-Roles quotient). *)
Definition first_iso_quotient {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  (Hrc : roles_collapsing f) : FunctionalSystem L :=
  fs_quotient S (kernel f) (kernel_cong f Hrc).

(** The induced mediator S/ker f -> T (the same underlying map as f). *)
Definition first_iso_mediator {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  (Hrc : roles_collapsing f) (HT : fs_constitution T = EquivalenceConstitution)
  : ERRMorphism (first_iso_quotient f Hrc) T.
Proof.
  unfold first_iso_quotient.
  apply (fs_quot_mediator (kernel f) (kernel_cong f Hrc) f).
  intros x y H. unfold kernel in H. rewrite H. apply (roles_refl_of_equiv T HT).
Defined.

(** ★★ FIRST ISO FRAGMENT: a Roles-collapsing f factors as the mediator after the kernel-quotient. *)
Lemma first_iso_factor : forall {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  (Hrc : roles_collapsing f) (HT : fs_constitution T = EquivalenceConstitution),
  err_morph_eq (err_comp (fs_quot S (kernel f) (kernel_cong f Hrc)) (first_iso_mediator f Hrc HT)) f.
Proof. intros L S T f Hrc HT x. reflexivity. Qed.

(** ★★ The kernel-quotient map is an EPI. *)
Lemma first_iso_epi : forall {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  (Hrc : roles_collapsing f),
  surjective (err_map (fs_quot S (kernel f) (kernel_cong f Hrc))).
Proof. intros. apply fs_quot_surjective. Qed.

(* ===================================================================== *)
(*  THE RESIDUE — the "iso onto the image" step is exactly obstacle (a)    *)
(* ===================================================================== *)

(** ★★ The mediator is injective (so "≅ im f" would hold) IFF f is injective on the CARRIER.  The
    coarsen-Roles quotient kept the carrier, so it bought NO injectivity — the iso-onto-image step
    still needs carrier-merge, exactly obstacle (a). *)
Lemma mediator_inj_iff_f_inj : forall {L} {S T : FunctionalSystem L} (f : ERRMorphism S T)
  (Hrc : roles_collapsing f) (HT : fs_constitution T = EquivalenceConstitution),
  injective_map (err_map (first_iso_mediator f Hrc HT)) <-> injective_map (err_map f).
Proof. intros. unfold injective_map. split; intro H; exact H. Qed.

(* ===================================================================== *)
(*  WITNESS — a genuinely collapsing morphism: factors, but not an iso     *)
(* ===================================================================== *)

(** SDisc has an equivalence constitution (its Roles are equality). *)
Definition SDisc_equiv : fs_constitution SDisc = EquivalenceConstitution := eq_refl.

(** A constant morphism on the discrete bool-system (sends everything to true). *)
Definition fconst : ERRMorphism SDisc SDisc :=
  @mkERRMorphism L2 SDisc SDisc (fun _ => true) (fun x y _ => eq_refl).

(** ★ fconst is Roles-collapsing (constant maps collapse everything). *)
Lemma fconst_collapsing : roles_collapsing fconst.
Proof. intros x y _. reflexivity. Qed.

(** ★ fconst is NOT injective on the carrier (true and false both map to true). *)
Lemma fconst_not_injective : ~ injective_map (err_map fconst).
Proof. intro H. specialize (H true false eq_refl). discriminate. Qed.

(** ★★ fconst FACTORS through its kernel-quotient (epi + mediator) yet the mediator is NOT injective —
    so there is no iso onto the image: the residue (a) is real, concretely. *)
Lemma fconst_factors_but_not_iso :
  err_morph_eq (err_comp (fs_quot SDisc (kernel fconst) (kernel_cong fconst fconst_collapsing))
                         (first_iso_mediator fconst fconst_collapsing SDisc_equiv)) fconst
  /\ ~ injective_map (err_map (first_iso_mediator fconst fconst_collapsing SDisc_equiv)).
Proof.
  split.
  - exact (first_iso_factor fconst fconst_collapsing SDisc_equiv).
  - intro H. apply fconst_not_injective.
    apply (proj1 (mediator_inj_iff_f_inj fconst fconst_collapsing SDisc_equiv)). exact H.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE FIRST ISO THEOREM, located in this category:
      (always)     ker f is an equivalence;
      ((c) exact)  ker f is a congruence iff f is Roles-collapsing;
      (fragment)   a Roles-collapsing f factors as epi (kernel-quotient) ∘ mediator (0-axiom);
      (residue=a)  the mediator is injective iff f is injective on the carrier — the iso-onto-image
                   step is exactly the carrier-merge obstacle (a).
    Obstacle (c) dissolves precisely for Roles-collapsing morphisms (the factorization holds with no
    quotient-type and no proof irrelevance); the only remaining gap to S/ker f ≅ im f is the unforced
    carrier-merge (a). *)
Theorem err_first_iso :
  (forall (L : Level) (S T : FunctionalSystem L) (f : ERRMorphism S T),
     EquivalenceConstitution (get_Elements S) (kernel f))
  /\ (forall (L : Level) (S T : FunctionalSystem L) (f : ERRMorphism S T),
        congruence S (kernel f) <-> roles_collapsing f)
  /\ (forall (L : Level) (S T : FunctionalSystem L) (f : ERRMorphism S T)
            (Hrc : roles_collapsing f) (HT : fs_constitution T = EquivalenceConstitution),
        err_morph_eq (err_comp (fs_quot S (kernel f) (kernel_cong f Hrc))
                               (first_iso_mediator f Hrc HT)) f
        /\ surjective (err_map (fs_quot S (kernel f) (kernel_cong f Hrc))))
  /\ (forall (L : Level) (S T : FunctionalSystem L) (f : ERRMorphism S T)
            (Hrc : roles_collapsing f) (HT : fs_constitution T = EquivalenceConstitution),
        injective_map (err_map (first_iso_mediator f Hrc HT)) <-> injective_map (err_map f)).
Proof.
  split; [ exact @kernel_equiv | ].
  split; [ exact @kernel_congruence_iff_roles_collapsing | ].
  split.
  - intros L S T f Hrc HT.
    split; [ exact (first_iso_factor f Hrc HT) | exact (first_iso_epi f Hrc) ].
  - exact @mediator_inj_iff_f_inj.
Qed.

Print Assumptions err_first_iso.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  10 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Obstacle (c) turned into a theorem: kernel_equiv (ker always equivalence);*)
(*  kernel_congruence_iff_roles_collapsing (ker is a congruence iff f is       *)
(*  Roles-collapsing — (c) located exactly).  FIRST ISO FRAGMENT for Roles-    *)
(*  collapsing f: first_iso_quotient (the ④ kernel-quotient), first_iso_       *)
(*  mediator, first_iso_factor (f = mediator ∘ epi) + first_iso_epi — 0-axiom, *)
(*  no quotient-type, no proof irrelevance.  RESIDUE = (a): mediator_inj_iff_f_*)
(*  inj (mediator injective iff f injective on the CARRIER — the coarsen-Roles *)
(*  quotient kept the carrier, so iso-onto-image still needs carrier-merge).   *)
(*  WITNESS fconst (constant on discrete SDisc): fconst_collapsing +           *)
(*  fconst_not_injective => fconst_factors_but_not_iso.  Capstone err_first_iso.*)
(*  HONEST: the FRAGMENT that holds 0-axiom; full S/ker≅im needs (a); we PROVE *)
(*  the residue is exactly carrier-injectivity.  Target must be an equiv-system.*)
(* ========================================================================= *)
