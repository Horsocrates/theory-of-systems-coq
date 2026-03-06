(* ========================================================================= *)
(*               INTENSIONAL IDENTITY: P3 FORMALIZED                       *)
(*                                                                          *)
(*  Part of: Theory of Systems — Coq Formalization                         *)
(*                                                                          *)
(*  P3: System identity = criterion identity (intensional),                *)
(*  NOT element-set identity (extensional).                                *)
(*                                                                          *)
(*  In ZFC, {x | x > 5} = {x | x ≥ 6} because same elements.            *)
(*  In ToS, these are DIFFERENT systems — different criteria.              *)
(*                                                                          *)
(*  STATUS: 11 Qed, 0 Admitted, 0 axioms                                  *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.

(* ========================================================================= *)
(*                   PART I: CRITERION OVER FIXED DOMAIN                   *)
(* ========================================================================= *)

(**
  CRITERIONOVER: DOMAIN-FIXED CRITERION
  =======================================

  Core_ERR.v's Criterion L has crit_domain : Type as a field.
  When comparing two criteria with different domains, transport is needed.

  CriterionOver L D fixes the domain D, making equivalence clean:
  no dependent type transport, just predicate comparison.

  Every Criterion L where crit_domain = D corresponds to a CriterionOver.
*)

Section P3_Theory.

Variable L : Level.
Variable D : Type.

Record CriterionOver := mkCriterionOver {
  co_predicate : D -> Prop;
  co_level_witness : Level;
  co_level_valid : co_level_witness << L;
}.

(* ========================================================================= *)
(*                   PART II: EXTENSIONAL EQUIVALENCE                      *)
(* ========================================================================= *)

(**
  EXTENSIONAL EQUIVALENCE
  ========================

  Two criteria over the same domain D are extensionally equivalent
  when they accept the same elements. This is what ZFC uses for
  set equality — same members means same set.
*)

(** Extensional equivalence: same predicate behavior *)
Definition ext_equiv (c1 c2 : CriterionOver) : Prop :=
  forall e : D, co_predicate c1 e <-> co_predicate c2 e.

(** Reflexivity *)
Lemma ext_equiv_refl : forall c, ext_equiv c c.
Proof.
  intro c. unfold ext_equiv. intro e. reflexivity.
Qed.

(** Symmetry *)
Lemma ext_equiv_sym :
  forall c1 c2, ext_equiv c1 c2 -> ext_equiv c2 c1.
Proof.
  intros c1 c2 H e. symmetry. apply H.
Qed.

(** Transitivity *)
Lemma ext_equiv_trans :
  forall c1 c2 c3,
    ext_equiv c1 c2 -> ext_equiv c2 c3 -> ext_equiv c1 c3.
Proof.
  intros c1 c2 c3 H12 H23 e.
  transitivity (co_predicate c2 e).
  - apply H12.
  - apply H23.
Qed.

(** Element transfer: ext_equiv preserves element membership *)
Lemma ext_equiv_element_transfer :
  forall c1 c2 e,
    ext_equiv c1 c2 -> co_predicate c1 e -> co_predicate c2 e.
Proof.
  intros c1 c2 e Heq Hin. apply Heq. exact Hin.
Qed.

(* ========================================================================= *)
(*                   PART III: P3 IDENTITY                                 *)
(* ========================================================================= *)

(**
  P3 IDENTITY (INTENSIONAL)
  ==========================

  P3 identity is Leibniz equality of criteria.
  Two criteria are P3-identical iff they are structurally the same:
  same predicate function, same level witness, same proof.

  Leibniz equality is strictly STRONGER than extensional equivalence.
*)

(** Leibniz equality implies extensional equivalence *)
Lemma P3_eq_implies_ext :
  forall (c1 c2 : CriterionOver),
    c1 = c2 -> ext_equiv c1 c2.
Proof.
  intros c1 c2 Heq. subst. apply ext_equiv_refl.
Qed.

(** Same criterion → same level witness *)
Lemma same_criterion_same_level :
  forall (c1 c2 : CriterionOver),
    c1 = c2 -> co_level_witness c1 = co_level_witness c2.
Proof.
  intros c1 c2 Heq. subst. reflexivity.
Qed.

(** Contrapositive: different level → different criterion *)
Lemma different_level_different_criterion :
  forall (c1 c2 : CriterionOver),
    co_level_witness c1 <> co_level_witness c2 -> c1 <> c2.
Proof.
  intros c1 c2 Hne Heq. apply Hne.
  exact (same_criterion_same_level c1 c2 Heq).
Qed.

End P3_Theory.

(* ========================================================================= *)
(*                   PART IV: THE SEPARATION THEOREM                       *)
(* ========================================================================= *)

(**
  EXTENSIONAL ≠ INTENSIONAL  (The Key Theorem)
  ==============================================

  We construct two CriterionOver L3 nat:
    - co_all_L1: predicate = True, level witness = L1
    - co_all_L2: predicate = True, level witness = L2

  These are EXTENSIONALLY equivalent:
    Same predicate behavior (both accept all natural numbers).

  But they are NOT P3-equal (not Leibniz equal):
    Different level witnesses (L1 ≠ L2).

  Philosophically: Two systems selecting the same elements
  for DIFFERENT reasons (grounded at different levels)
  are different systems. The "why" matters, not just the "what".
*)

(** Counterexample criterion 1: all nats, level witness L1 *)
Definition co_all_L1 : CriterionOver L3 nat := {|
  co_predicate := fun _ => True;
  co_level_witness := L1;
  co_level_valid := L1_lt_L3;
|}.

(** Counterexample criterion 2: all nats, level witness L2 *)
Definition co_all_L2 : CriterionOver L3 nat := {|
  co_predicate := fun _ => True;
  co_level_witness := L2;
  co_level_valid := L2_lt_L3;
|}.

(** These are extensionally equivalent *)
Lemma ext_equiv_counterexample :
  ext_equiv L3 nat co_all_L1 co_all_L2.
Proof.
  unfold ext_equiv. intro e. simpl. tauto.
Qed.

(** But they are NOT Leibniz equal *)
Lemma P3_neq_counterexample :
  co_all_L1 <> co_all_L2.
Proof.
  apply (different_level_different_criterion L3 nat).
  simpl. discriminate.
Qed.

(** THE SEPARATION THEOREM:
    Extensional equivalence does NOT imply P3 identity *)
Theorem extensional_not_implies_intensional :
  ~ (forall (c1 c2 : CriterionOver L3 nat),
       ext_equiv L3 nat c1 c2 -> c1 = c2).
Proof.
  intro H.
  apply P3_neq_counterexample.
  apply H.
  exact ext_equiv_counterexample.
Qed.

(* ========================================================================= *)
(*                   PART V: SYSTEM-LEVEL CONSEQUENCES                     *)
(* ========================================================================= *)

(**
  SYSTEM-LEVEL P3
  =================

  The separation theorem lifts from CriterionOver to System.
  We show that even for systems with identical structure
  (same pos_bound, same uniqueness), P3 distinguishes them
  when criteria differ at the level-witness.
*)

(** Construct two systems with extensionally equivalent but
    P3-distinct criteria *)
Definition sys_all_nat_L1 : System L3 := {|
  sys_criterion := {| crit_domain := nat;
                       crit_predicate := fun _ => True;
                       crit_level_witness := L1;
                       crit_level_valid := L1_lt_L3 |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

Definition sys_all_nat_L2 : System L3 := {|
  sys_criterion := {| crit_domain := nat;
                       crit_predicate := fun _ => True;
                       crit_level_witness := L2;
                       crit_level_valid := L2_lt_L3 |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

(** These systems are NOT equal despite having the same elements *)
Theorem system_P3_separation :
  sys_all_nat_L1 <> sys_all_nat_L2.
Proof.
  intro H.
  assert (Hc := f_equal (sys_criterion L3) H).
  assert (Hw := f_equal (crit_level_witness L3) Hc).
  simpl in Hw. discriminate.
Qed.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  PROVEN (11 Qed):

  Part II  — Extensional equivalence:
    ext_equiv_refl, ext_equiv_sym, ext_equiv_trans, ext_equiv_element_transfer

  Part III — P3 identity:
    P3_eq_implies_ext, same_criterion_same_level,
    different_level_different_criterion

  Part IV  — The Separation Theorem:
    ext_equiv_counterexample, P3_neq_counterexample,
    extensional_not_implies_intensional

  Part V   — System-level:
    system_P3_separation

  KEY INSIGHT:
  co_all_L1 and co_all_L2 accept EXACTLY the same natural numbers (all of them).
  Yet they are structurally different: one is grounded at L1, the other at L2.
  P3 correctly distinguishes them — identity is intensional, not extensional.
  This is the formal content of P3: "systems that look alike are not alike
  unless they are identical in definition."

  AXIOMS: 0 (all proofs constructive, no classical logic needed)
*)

Print Assumptions extensional_not_implies_intensional.
Print Assumptions ext_equiv_trans.
Print Assumptions system_P3_separation.
