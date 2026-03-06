(* ========================================================================= *)
(*                CONVERSION: WHEN TYPES ARE EQUAL (P3)                    *)
(*                                                                          *)
(*  P3 says: systems with same constitution are identical.                 *)
(*  This file formalizes conversion rules -- when you can replace          *)
(*  one type with another:                                                  *)
(*    - P3 constitution-based conversion (intensional identity)            *)
(*    - Computational conversion (beta/eta for Pi and Sigma)               *)
(*    - L5 resolution determinism                                           *)
(*                                                                          *)
(*  Depends on: Core_ERR, IntensionalIdentity, DependentSystems, L5Res    *)
(*  STATUS: 16 Qed, 0 Admitted                                            *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import IntensionalIdentity.
From ToS Require Import SystemMorphism.
From ToS Require Import DependentSystems.
From ToS Require Import L5Resolution.

Import ListNotations.

(* ========================================================================= *)
(*          PART I: P3 CONSTITUTION-BASED CONVERSION                        *)
(* ========================================================================= *)

(** P3 conversion = Leibniz equality on CriterionOver.
    Strictly stronger than extensional equivalence: requires same
    predicate AND same level witness, not just same elements. *)

Section P3Conversion.

Variable L : Level.
Variable D : Type.

Definition P3_convertible (c1 c2 : CriterionOver L D) : Prop := c1 = c2.

(** Lemma 1: reflexivity *)
Lemma P3_convertible_refl : forall c : CriterionOver L D,
  P3_convertible c c.
Proof. intro c. unfold P3_convertible. reflexivity. Qed.

(** Lemma 2: symmetry *)
Lemma P3_convertible_sym : forall c1 c2 : CriterionOver L D,
  P3_convertible c1 c2 -> P3_convertible c2 c1.
Proof.
  intros c1 c2 H. unfold P3_convertible in *. symmetry. exact H.
Qed.

(** Lemma 3: transitivity *)
Lemma P3_convertible_trans : forall c1 c2 c3 : CriterionOver L D,
  P3_convertible c1 c2 -> P3_convertible c2 c3 -> P3_convertible c1 c3.
Proof.
  intros c1 c2 c3 H12 H23.
  unfold P3_convertible in *. transitivity c2; assumption.
Qed.

End P3Conversion.

(** Lemma 4: P3 is NOT extensional equality.
    Reuses co_all_L1/co_all_L2 counterexample from IntensionalIdentity.v:
    same predicate (True for all nat) but different level witnesses. *)
Theorem P3_not_extensional :
  ~ (forall (c1 c2 : CriterionOver L3 nat),
       ext_equiv L3 nat c1 c2 -> P3_convertible L3 nat c1 c2).
Proof.
  intro H. apply P3_neq_counterexample. apply H.
  exact ext_equiv_counterexample.
Qed.

(** Lemma 5: P3-convertible criteria have identical element membership *)
Lemma convertible_same_elements :
  forall L D (c1 c2 : CriterionOver L D),
    P3_convertible L D c1 c2 ->
    forall e : D, co_predicate L D c1 e <-> co_predicate L D c2 e.
Proof.
  intros L0 D0 c1 c2 Hconv e.
  unfold P3_convertible in Hconv. subst c2. reflexivity.
Qed.

(** Lemma 6: chain of conversions collapses to one conversion *)
Lemma conversion_chain :
  forall L D (c1 c2 c3 c4 : CriterionOver L D),
    P3_convertible L D c1 c2 ->
    P3_convertible L D c2 c3 ->
    P3_convertible L D c3 c4 ->
    P3_convertible L D c1 c4.
Proof.
  intros L0 D0 c1 c2 c3 c4 H12 H23 H34.
  apply (P3_convertible_trans L0 D0 c1 c2 c4).
  - exact H12.
  - apply (P3_convertible_trans L0 D0 c2 c3 c4); assumption.
Qed.

(* ========================================================================= *)
(*      PART II: COMPUTATIONAL CONVERSION (Beta/Eta for Pi and Sigma)       *)
(* ========================================================================= *)

(** Beta: constructing then eliminating yields the original.
    Eta: eliminating then reconstructing yields the original.
    In MLTT: beta-Pi = (fun x => t) a = t[a/x],
             eta-Pi  = (fun x => f x) = f,
             beta-Sigma-fst/snd, eta-Sigma = surjective pairing. *)

Section ComputationalConversion.

Variable L : Level.
Variable A : System L.
Variable B : ElemOf L A -> System L.

(** Lemma 7: Beta for Pi -- application computes *)
Lemma beta_pi :
  forall (f_body : forall a : ElemOf L A, ElemOf L (B a))
         (a : ElemOf L A),
    pi_app L A B (mkPiSystem L A B f_body) a = f_body a.
Proof. intros f_body a. reflexivity. Qed.

(** Lemma 8: Eta for Pi -- any PiSystem equals its pointwise reconstruction.
    Uses pi_extensionality (functional_extensionality_dep). *)
Lemma eta_pi :
  forall (f : PiSystem L A B),
    f = mkPiSystem L A B (fun a => pi_app L A B f a).
Proof.
  intros f. apply (pi_extensionality L A B). intro a. reflexivity.
Qed.

(** Lemma 9: Beta for Sigma fst *)
Lemma beta_sigma_fst :
  forall (a : ElemOf L A) (b : ElemOf L (B a)),
    sigma_fst L A B (mkSigmaElem L A B a b) = a.
Proof. intros a b. reflexivity. Qed.

(** Lemma 10: Beta for Sigma snd *)
Lemma beta_sigma_snd :
  forall (a : ElemOf L A) (b : ElemOf L (B a)),
    sigma_snd L A B (mkSigmaElem L A B a b) = b.
Proof. intros a b. reflexivity. Qed.

(** Lemma 11: Sigma eta (surjective pairing) -- every Sigma element
    equals the pair of its projections. Reuses sigma_eta. *)
Lemma sigma_surjective_pairing :
  forall (p : SigmaElem L A B),
    p = mkSigmaElem L A B (sigma_fst L A B p) (sigma_snd L A B p).
Proof. intros p. exact (sigma_eta L A B p). Qed.

End ComputationalConversion.

(* ========================================================================= *)
(*           PART III: L5 RESOLUTION DETERMINISM                            *)
(* ========================================================================= *)

(** Lemma 12: L5 resolution is deterministic -- same candidate set
    (as set-equal lists) gives the same result. *)
Theorem l5_resolve_deterministic :
  forall (l1 l2 : list nat) (a b : nat),
    l5_resolve_gen l1 = Some a ->
    l5_resolve_gen l2 = Some b ->
    (forall x, In x l1 <-> In x l2) ->
    a = b.
Proof. exact l5_resolve_gen_deterministic. Qed.

(* ========================================================================= *)
(*      PART IV: SYSTEM-LEVEL P3 CONVERSION                                *)
(* ========================================================================= *)

(** Lemma 13: System equality implies criterion equality *)
Lemma system_eq_criterion :
  forall L (S1 S2 : System L),
    S1 = S2 -> sys_criterion L S1 = sys_criterion L S2.
Proof. intros L0 S1 S2 Heq. subst S2. reflexivity. Qed.

(** Lemma 14: P3-convertible criteria enable element transfer *)
Lemma P3_convertible_element_transfer :
  forall L D (c1 c2 : CriterionOver L D) (e : D),
    P3_convertible L D c1 c2 ->
    co_predicate L D c1 e ->
    co_predicate L D c2 e.
Proof.
  intros L0 D0 c1 c2 e Hconv Hsat.
  unfold P3_convertible in Hconv. subst c2. exact Hsat.
Qed.

(** Lemma 15: P3 conversion preserves level witness *)
Lemma P3_convertible_same_level :
  forall L D (c1 c2 : CriterionOver L D),
    P3_convertible L D c1 c2 ->
    co_level_witness L D c1 = co_level_witness L D c2.
Proof.
  intros L0 D0 c1 c2 Hconv.
  unfold P3_convertible in Hconv. subst c2. reflexivity.
Qed.

(** Lemma 16: Beta-eta coherence for Pi -- constructing from a function
    then eta-expanding is identity. *)
Lemma beta_eta_pi_coherence :
  forall L (A : System L) (B : ElemOf L A -> System L)
         (f_body : forall a : ElemOf L A, ElemOf L (B a)),
    mkPiSystem L A B f_body =
    mkPiSystem L A B (fun a => pi_app L A B (mkPiSystem L A B f_body) a).
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  PROVEN (16 Qed, 0 Admitted):

  Part I  -- P3 Conversion:
    1. P3_convertible_refl            6. conversion_chain
    2. P3_convertible_sym
    3. P3_convertible_trans
    4. P3_not_extensional
    5. convertible_same_elements

  Part II -- Computational (beta/eta):
    7.  beta_pi                      11. sigma_surjective_pairing
    8.  eta_pi
    9.  beta_sigma_fst
    10. beta_sigma_snd

  Part III -- L5: 12. l5_resolve_deterministic

  Part IV -- System-Level:
    13. system_eq_criterion          16. beta_eta_pi_coherence
    14. P3_convertible_element_transfer
    15. P3_convertible_same_level

  AXIOMS: classical logic (inherited), functional_extensionality_dep (eta_pi)
*)

Print Assumptions P3_not_extensional.
Print Assumptions l5_resolve_deterministic.
Print Assumptions beta_eta_pi_coherence.
