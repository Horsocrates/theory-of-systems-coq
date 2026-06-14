(** * ERRFiniteQuotient.v — dissolving obstacles (a) and (b) on the FINITE / DECIDABLE side of H1: the
      FULL first isomorphism theorem S/ker f ≅ im f, 0-axiom, for any morphism equipped with a
      canonical-representative function (which finiteness + decidability provides).

    ERRFirstIso located obstacle (c) (kernel = congruence iff Roles-collapsing) and showed the residue
    is exactly (a) carrier-merge + (b) proof irrelevance.  Here we DISSOLVE (a) and (b) — on the side
    of H1 where they can be dissolved (finite / decidable), without any axiom:

      ★ A CanonRepr for f: a decidable equality on the carrier + a canonical representative function
        `repr` with repr-SOUND (f (repr x) = f x — repr stays in the kernel-class) and repr-COMPLETE
        (f x = f y -> repr x = repr y — kernel-equal elements share one representative).  This is
        exactly what a finite carrier with decidable kernel provides (the canonical-form / `find`
        construction); the representative is an ACTUAL element chosen by a rule (the argmax-by-index
        pattern), NOT a class-as-object (so no quotient-type — (a) dissolved).
      ★ The MERGED carrier Qfin = {x | repr x = x} (the representatives) is a genuine sub-type — the
        carrier-quotient, built with NO quotient axiom.  Its identity is settled by UIP_dec (decidable
        equality => proof irrelevance for the membership proof — (b) dissolved, 0-axiom, NOT the PI
        axiom).
      ★ The FULL first iso theorem: f factors as the surjection qfin (carrier-merge) followed by the
        mediator medfin, and medfin is a BIJECTION onto the image — injective (medfin_injective) and
        onto (medfin_onto_image).  So S/ker f ≅ im f at the carrier level, 0-axiom.
      ★ Witness fconst (constant on the discrete bool-system): a concrete CanonRepr; the 2-element
        carrier MERGES to a single representative (fconst_carrier_merged) — (a) dissolved concretely.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      a canonical representative MERGES the carrier (representative = an actual Element chosen by a rule,
      not a class-as-object); decidable equality gives UIP (identity at the WHAT-tier, no proof
      irrelevance axiom); then the FULL S/ker f ≅ im f holds (the mediator is a carrier-level bijection
      onto the image).
    Roles (L4): CanonRepr (the representative structure); qfin (the merge / quotient map); medfin (the
      mediator, an iso onto the image); the bijection lemmas.
    Elements (L1+P4): the finite/decidable carrier; the representatives (actual Elements); the merged
      sub-type Qfin.
    P4 diagnostic (could it be otherwise?):
      the representative is P4-legitimate (an actual element, selected by a rule) — NOT a collection-as-
      object (¬P4); the merge is constructive (finite, decidable); identity is by value (extensional)
      via UIP_dec, not by class.  So on the finite side both (a) and (b) are unforced and vanish.
    Honesty wall:
      this dissolves (a)+(b) at the carrier / map level — the iso S/ker f ≅ im f as a BIJECTION of
      carriers — for ANY f equipped with a CanonRepr; CanonRepr is realizable 0-axiom for finite
      decidable carriers (the standard canonical-form / find-over-enumeration construction), shown here
      concretely on bool / fconst (the general construction is routine constructive, not an axiom).  It
      does NOT touch the role-limit side of H1 (ярус III): there the carrier is infinite / the kernel
      undecidable, CanonRepr is not constructible, and the wall stays — exactly as it must.  Making
      im f a constituted sub-SYSTEM (with Roles / Rules) is the separate restriction-stable question.
      Uses UIP_dec (Stdlib Eqdep_dec — 0-axiom for decidable types).  Reuses ERRFirstIso (fconst /
      SDisc).  0 axioms.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, err_map *)
From ToS Require Import foundation.ERRQuotient.       (* SDisc *)
From ToS Require Import foundation.ERRFirstIso.       (* fconst *)
From Stdlib Require Import Eqdep_dec Bool.

(* ===================================================================== *)
(*  CANONICAL REPRESENTATIVES — what finiteness + decidability provide     *)
(* ===================================================================== *)

(** A canonical-representative structure for f: decidable carrier equality + a representative function
    that is SOUND (stays in the kernel-class) and COMPLETE (kernel-equal share a representative). *)
Record CanonRepr {L} (S T : FunctionalSystem L) (f : ERRMorphism S T) : Type := {
  cr_dec      : forall x y : get_Elements S, {x = y} + {x <> y};
  cr_repr     : get_Elements S -> get_Elements S;
  cr_sound    : forall x, err_map f (cr_repr x) = err_map f x;
  cr_complete : forall x y, err_map f x = err_map f y -> cr_repr x = cr_repr y;
}.
Arguments cr_dec {L S T f}.
Arguments cr_repr {L S T f}.
Arguments cr_sound {L S T f}.
Arguments cr_complete {L S T f}.

(** The representative is idempotent (it is sound, so kernel-equal to its own representative). *)
Definition cr_idem {L} {S T : FunctionalSystem L} {f : ERRMorphism S T} (CR : CanonRepr S T f)
  (x : get_Elements S) : cr_repr CR (cr_repr CR x) = cr_repr CR x :=
  cr_complete CR (cr_repr CR x) x (cr_sound CR x).

(* ===================================================================== *)
(*  THE MERGED CARRIER (the carrier-quotient, no quotient-type)            *)
(* ===================================================================== *)

(** The quotient carrier: the representatives.  A genuine sub-type — the carrier has been MERGED. *)
Definition Qfin {L} {S T : FunctionalSystem L} {f : ERRMorphism S T} (CR : CanonRepr S T f) : Type :=
  { x : get_Elements S | cr_repr CR x = x }.

(** Sub-type identity is settled by UIP_dec (decidable equality, 0-axiom — NOT proof irrelevance). *)
Lemma Qfin_eq : forall {L} {S T : FunctionalSystem L} {f : ERRMorphism S T} (CR : CanonRepr S T f)
  (q1 q2 : Qfin CR), proj1_sig q1 = proj1_sig q2 -> q1 = q2.
Proof.
  intros L S T f CR [v1 p1] [v2 p2] H. simpl in H. subst v2.
  f_equal. apply (UIP_dec (cr_dec CR)).
Qed.

(** The quotient map: send each element to its representative (the carrier-merge). *)
Definition qfin {L} {S T : FunctionalSystem L} {f : ERRMorphism S T} (CR : CanonRepr S T f)
  (x : get_Elements S) : Qfin CR := exist _ (cr_repr CR x) (cr_idem CR x).

(** The mediator: a representative goes to its f-value (well-defined since reps are canonical). *)
Definition medfin {L} {S T : FunctionalSystem L} {f : ERRMorphism S T} (CR : CanonRepr S T f)
  (q : Qfin CR) : get_Elements T := err_map f (proj1_sig q).

(* ===================================================================== *)
(*  THE FULL FIRST ISO THEOREM ON THE FINITE / DECIDABLE SIDE              *)
(* ===================================================================== *)

(** ★★ Factorization: f = mediator ∘ quotient (the surjection then the injection). *)
Lemma medfin_factor : forall {L} {S T : FunctionalSystem L} {f : ERRMorphism S T}
  (CR : CanonRepr S T f) (x : get_Elements S),
  err_map f x = medfin CR (qfin CR x).
Proof. intros L S T f CR x. unfold medfin, qfin. simpl. symmetry. apply (cr_sound CR). Qed.

(** ★★ The quotient map is SURJECTIVE onto the merged carrier (carrier-merge). *)
Lemma qfin_surjective : forall {L} {S T : FunctionalSystem L} {f : ERRMorphism S T}
  (CR : CanonRepr S T f) (q : Qfin CR), exists x, qfin CR x = q.
Proof.
  intros L S T f CR q. exists (proj1_sig q). apply Qfin_eq. unfold qfin. simpl.
  exact (proj2_sig q).
Qed.

(** ★★★ The mediator is INJECTIVE — the carrier-merge bought the injectivity (this is exactly the step
    that ERRFirstIso's coarsen-Roles quotient could NOT supply).  So "≅ im f" now holds. *)
Lemma medfin_injective : forall {L} {S T : FunctionalSystem L} {f : ERRMorphism S T}
  (CR : CanonRepr S T f) (q1 q2 : Qfin CR), medfin CR q1 = medfin CR q2 -> q1 = q2.
Proof.
  intros L S T f CR q1 q2 H. unfold medfin in H.
  apply Qfin_eq.
  pose proof (cr_complete CR (proj1_sig q1) (proj1_sig q2) H) as Hc.
  rewrite (proj2_sig q1) in Hc. rewrite (proj2_sig q2) in Hc. exact Hc.
Qed.

(** ★★ The mediator is ONTO the image of f. *)
Lemma medfin_onto_image : forall {L} {S T : FunctionalSystem L} {f : ERRMorphism S T}
  (CR : CanonRepr S T f) (x : get_Elements S), exists q : Qfin CR, medfin CR q = err_map f x.
Proof.
  intros L S T f CR x. exists (qfin CR x). unfold medfin, qfin. simpl. apply (cr_sound CR).
Qed.

(* ===================================================================== *)
(*  WITNESS — a concrete finite CanonRepr; the carrier genuinely merges    *)
(* ===================================================================== *)

(** A canonical-representative structure for fconst (constant true on the discrete bool-system):
    decidable (bool_dec), representative = true (the single kernel-class). *)
Definition fconst_repr : CanonRepr SDisc SDisc fconst :=
  @Build_CanonRepr L2 SDisc SDisc fconst bool_dec (fun _ => true)
    (fun x => eq_refl) (fun x y _ => eq_refl).

(** ★★ The carrier genuinely MERGES: bool has two distinct elements, but the quotient carrier is a
    subsingleton (one representative).  Obstacle (a) dissolved concretely, 0-axiom. *)
Lemma fconst_carrier_merged :
  (true <> false) /\ (forall q1 q2 : Qfin fconst_repr, q1 = q2).
Proof.
  split.
  - discriminate.
  - intros q1 q2. apply Qfin_eq.
    transitivity true; [ symmetry; exact (proj2_sig q1) | exact (proj2_sig q2) ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE FULL FIRST ISO THEOREM, finite / decidable side (obstacles (a) and (b) dissolved):
      (factor)     f = mediator ∘ quotient;
      (epi)        the quotient map is surjective onto the merged carrier;
      (mono)       the mediator is injective (the carrier-merge supplied the injectivity);
      (onto image) the mediator is onto the image of f.
    Hence the mediator is a bijection Qfin ≅ im f — the classical S/ker f ≅ im f holds 0-axiom for any
    f with a canonical-representative structure (which finiteness + decidability provide).  Beyond the
    role-limit side of H1, there are NO obstacles (a)/(b)/(c). *)
Theorem err_finite_first_iso : forall {L} {S T : FunctionalSystem L} {f : ERRMorphism S T}
  (CR : CanonRepr S T f),
  (forall x, err_map f x = medfin CR (qfin CR x))
  /\ (forall q : Qfin CR, exists x, qfin CR x = q)
  /\ (forall q1 q2 : Qfin CR, medfin CR q1 = medfin CR q2 -> q1 = q2)
  /\ (forall x, exists q : Qfin CR, medfin CR q = err_map f x).
Proof.
  intros L S T f CR.
  split; [ exact (medfin_factor CR) | ].
  split; [ exact (qfin_surjective CR) | ].
  split; [ exact (medfin_injective CR) | exact (medfin_onto_image CR) ].
Qed.

Print Assumptions err_finite_first_iso.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  7 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Dissolves obstacles (a) carrier-merge and (b) proof irrelevance on the    *)
(*  FINITE / DECIDABLE side of H1.  CanonRepr (decidable eq + canonical        *)
(*  representative, sound + complete) = what finiteness provides.  Qfin = the  *)
(*  merged carrier {x | repr x = x} (no quotient-type — (a) gone); Qfin_eq via *)
(*  UIP_dec (decidable eq => no proof-irrelevance axiom — (b) gone).  Full     *)
(*  first iso theorem: medfin_factor + qfin_surjective (epi) + medfin_         *)
(*  injective (the carrier-merge supplies injectivity — the step the coarsen-  *)
(*  Roles quotient lacked) + medfin_onto_image; so medfin : Qfin ≅ im f.       *)
(*  Witness fconst_repr + fconst_carrier_merged (bool's 2 elements merge to    *)
(*  one representative).  Capstone err_finite_first_iso.  HONEST: carrier/map  *)
(*  level, for any f with a CanonRepr (realizable 0-axiom for finite decidable,*)
(*  shown on bool); does NOT touch the role-limit side (there CanonRepr is not *)
(*  constructible — the H1 wall stays); im f as a constituted sub-system is a   *)
(*  separate question.  Uses UIP_dec (Eqdep_dec).                             *)
(* ========================================================================= *)
