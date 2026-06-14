(** * ERRIso.v — deepening ④: ISOMORPHISM of systems + the QUOTIENT SPECTRUM.  The honest, 0-axiom
      replacement for the classical first isomorphism theorem.

    An ISO is a morphism with a two-sided inverse morphism.  It is an equivalence on objects
    (refl/sym/trans) and is BOTH mono (injective) and epi (surjective).  The quotient (④) gives a
    SPECTRUM: quotient by the FINEST congruence (the Roles themselves) is an ISO — nothing forgotten;
    coarser congruences give epis that FORGET (ERRQuotient.quotient_collapses).

      ★ iso m / SystemIso S1 S2 — a morphism with a two-sided inverse / objects so related.
      ★ iso_refl / iso_sym / iso_trans — SystemIso is an equivalence on objects.
      ★ iso_injective (mono) / iso_surjective (epi) — an iso is both.
      ★ quotient_by_roles_iso — the quotient by the Roles-congruence is ISO to S (the trivial,
        nothing-forgotten quotient); coarser congruences forget (④).

    Why NOT the classical first iso theorem (S/ker f ≅ im f): it needs (a) carrier quotient TYPES (a
    quotient axiom), (b) proof irrelevance to handle the image as a sub-type, and (c) the kernel pair
    of f to be a CONGRUENCE — but in this Roles-PRESERVING category the kernel (f x = f y) need not
    contain the Roles, so it is not a congruence in general.  All three break 0-axiom or fail here.  We
    give instead what DOES hold: iso = equivalence + mono + epi, and the quotient spectrum.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      an ISO is an invertible morphism; SystemIso is an equivalence on objects and every iso is BOTH
      mono and epi; the QUOTIENT SPECTRUM runs from the finest congruence (the Roles — an ISO, nothing
      forgotten) to coarser ones (forgetful epis).
    Roles (L4): iso / SystemIso; iso_injective / iso_surjective (mono / epi); quotient_by_roles_iso
      (the trivial quotient).
    Elements (L1+P4): the systems; the morphisms; the congruences.
    P4 diagnostic (could it be otherwise?):
      an iso is a contingent invertible relabeling; the quotient spectrum is a real RANGE — finest
      (Roles, iso, nothing forgotten) to coarsest (full, maximal collapse): how much is forgotten is a
      free choice.
    Honesty wall:
      NOT the classical first iso theorem (carrier quotient types + proof irrelevance + kernel-as-
      congruence all fail 0-axiom / this category); we give iso-as-equivalence + mono+epi + the
      quotient spectrum (quotient by the Roles = iso).  Ties ④ (ERRQuotient) and the mono/epi (sub/
      quotient) language.  Reuses ERRComposition + ERRQuotient.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, err_id, err_comp, err_map, err_morph_eq *)
From ToS Require Import foundation.ERRQuotient.       (* fs_quotient, congruence, fs_quot, surjective *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  ISOMORPHISM                                                            *)
(* ===================================================================== *)

(** An ISO: a morphism with a two-sided inverse morphism. *)
Definition iso {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2) : Prop :=
  exists m' : ERRMorphism S2 S1,
    err_morph_eq (err_comp m m') (err_id S1) /\ err_morph_eq (err_comp m' m) (err_id S2).

(** Two systems are ISOMORPHIC if some morphism between them is an iso. *)
Definition SystemIso {L} (S1 S2 : FunctionalSystem L) : Prop := exists m : ERRMorphism S1 S2, iso m.

(** ★ Reflexive: identity is an iso. *)
Lemma iso_refl : forall {L} (S : FunctionalSystem L), SystemIso S S.
Proof. intros L S. exists (err_id S), (err_id S). split; intro x; reflexivity. Qed.

(** ★★ Symmetric: the inverse is an iso the other way. *)
Lemma iso_sym : forall {L} (S1 S2 : FunctionalSystem L), SystemIso S1 S2 -> SystemIso S2 S1.
Proof.
  intros L S1 S2 [m [mi [Hmm Hmi]]]. exists mi, m. split; [ exact Hmi | exact Hmm ].
Qed.

(** ★★ Transitive: isos compose. *)
Lemma iso_trans : forall {L} (S1 S2 S3 : FunctionalSystem L),
  SystemIso S1 S2 -> SystemIso S2 S3 -> SystemIso S1 S3.
Proof.
  intros L S1 S2 S3 [m [mi [Hmm Hmi]]] [n [ni [Hnn Hni]]].
  exists (err_comp m n), (err_comp ni mi). split.
  - intro x. cbn. transitivity (err_map mi (err_map m x)).
    + f_equal. exact (Hnn (err_map m x)).
    + exact (Hmm x).
  - intro x. cbn. transitivity (err_map n (err_map ni x)).
    + f_equal. exact (Hmi (err_map ni x)).
    + exact (Hni x).
Qed.

(* ===================================================================== *)
(*  AN ISO IS BOTH MONO AND EPI                                            *)
(* ===================================================================== *)

(** Injectivity of the underlying map (a mono witness). *)
Definition injective_map {A B : Type} (f : A -> B) : Prop := forall x y, f x = f y -> x = y.

(** ★★ An iso is MONO (injective). *)
Lemma iso_injective : forall {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2),
  iso m -> injective_map (err_map m).
Proof.
  intros L S1 S2 m [mi [Hmm _]] x y H.
  transitivity (err_map mi (err_map m x)).
  - symmetry. exact (Hmm x).
  - rewrite H. exact (Hmm y).
Qed.

(** ★★ An iso is EPI (surjective). *)
Lemma iso_surjective : forall {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2),
  iso m -> surjective (err_map m).
Proof. intros L S1 S2 m [mi [_ Hmi]] y. exists (err_map mi y). exact (Hmi y). Qed.

(* ===================================================================== *)
(*  THE QUOTIENT SPECTRUM — quotient by the Roles is an ISO                *)
(* ===================================================================== *)

(** When S's Roles are an equivalence (S has an equivalence constitution), the Roles are a congruence
    (trivially containing themselves). *)
Lemma roles_congruence : forall {L} (S : FunctionalSystem L),
  fs_constitution S = EquivalenceConstitution -> congruence S (get_Roles S).
Proof.
  intros L S H. split.
  - rewrite <- H. exact (fs_functional S).
  - intros x y Hxy. exact Hxy.
Qed.

(** The inverse of the quotient-by-Roles map: the identity, reflecting Roles back. *)
Definition fs_quot_inv {L} (S : FunctionalSystem L) (H : fs_constitution S = EquivalenceConstitution)
  : ERRMorphism (fs_quotient S (get_Roles S) (roles_congruence S H)) S.
Proof.
  refine (@mkERRMorphism L (fs_quotient S (get_Roles S) (roles_congruence S H)) S (fun x => x) _).
  intros x y Hxy. exact Hxy.
Defined.

(** ★★★ The quotient by the FINEST congruence (the Roles) is ISO to S — the trivial, nothing-forgotten
    quotient.  (Coarser congruences forget distinctions — ERRQuotient.quotient_collapses.) *)
Lemma quotient_by_roles_iso : forall {L} (S : FunctionalSystem L)
  (H : fs_constitution S = EquivalenceConstitution),
  SystemIso S (fs_quotient S (get_Roles S) (roles_congruence S H)).
Proof.
  intros L S H.
  exists (fs_quot S (get_Roles S) (roles_congruence S H)), (fs_quot_inv S H).
  split; intro x; reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ ISOMORPHISM & the QUOTIENT SPECTRUM:
      (equivalence) SystemIso is reflexive, symmetric, transitive;
      (mono+epi)    every iso is both injective and surjective;
      (spectrum)    the quotient by the finest congruence (the Roles) is an iso — nothing forgotten.
    Iso is an equivalence on objects and is both mono and epi; the quotient runs a spectrum from iso
    (finest) to maximal collapse (coarsest). *)
Theorem err_iso :
  (forall (L : Level) (S : FunctionalSystem L), SystemIso S S)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L), SystemIso S1 S2 -> SystemIso S2 S1)
  /\ (forall (L : Level) (S1 S2 S3 : FunctionalSystem L),
        SystemIso S1 S2 -> SystemIso S2 S3 -> SystemIso S1 S3)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (m : ERRMorphism S1 S2),
        iso m -> injective_map (err_map m))
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) (m : ERRMorphism S1 S2),
        iso m -> surjective (err_map m))
  /\ (forall (L : Level) (S : FunctionalSystem L) (H : fs_constitution S = EquivalenceConstitution),
        SystemIso S (fs_quotient S (get_Roles S) (roles_congruence S H))).
Proof.
  split; [ exact @iso_refl | ].
  split; [ exact @iso_sym | ].
  split; [ exact @iso_trans | ].
  split; [ exact @iso_injective | ].
  split; [ exact @iso_surjective | exact @quotient_by_roles_iso ].
Qed.

Print Assumptions err_iso.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Deepens ④: ISOMORPHISM + the QUOTIENT SPECTRUM (honest 0-axiom stand-in    *)
(*  for the first iso theorem).  iso / SystemIso; iso_refl/_sym/_trans         *)
(*  (equivalence on objects); iso_injective (mono) / iso_surjective (epi);     *)
(*  roles_congruence + fs_quot_inv + quotient_by_roles_iso (quotient by the    *)
(*  finest congruence = the Roles is an ISO — nothing forgotten; coarser       *)
(*  congruences forget, cf. ERRQuotient.quotient_collapses).  Capstone err_iso.*)
(*  HONEST: NOT S/ker f =~ im f — that needs carrier quotient types (a         *)
(*  quotient axiom) + proof irrelevance + kernel-as-congruence, all of which   *)
(*  fail 0-axiom / this Roles-preserving category.                            *)
(* ========================================================================= *)
