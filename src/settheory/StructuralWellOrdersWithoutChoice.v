(** * StructuralWellOrdersWithoutChoice.v — well-orders we have, without AC
    Elements: carriers nat, Level; orders lt, level_lt
    Roles:    well_orders = (well-founded + total) as a structural role
    Rules:    nat and the Level hierarchy carry structural well-orders;
              the GLOBAL well-ordering principle (every type) is the AC-equivalent
              and is NOT asserted
    STATUS:   6 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    G5. "Well-ordering without choice": the carriers we actually use (nat, the
    Level hierarchy) are well-ordered STRUCTURALLY — well-founded (no infinite
    descent) and total — with ZERO axioms. By contrast, the well-ordering
    THEOREM ("every set can be well-ordered", forall X, well_orderable X) is
    equivalent to the Axiom of Choice (Zermelo) and is deliberately NOT proven:
    it is exactly the transgressive completed-object claim P4 refuses
    (foundation/P4ProhibitsAC.v).
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.TransfiniteInductionLevel.
From Stdlib Require Import Wf_nat PeanoNat Lia.

(* ===================== Level depth: positivity and injectivity ========== *)

Lemma level_depth_pos : forall l, (1 <= level_depth l)%nat.
Proof. induction l as [|l' IH]; simpl; lia. Qed.

Lemma level_depth_inj : forall l1 l2, level_depth l1 = level_depth l2 -> l1 = l2.
Proof.
  induction l1 as [|l1' IHl1]; intros [|l2'] H.
  - reflexivity.
  - exfalso. simpl in H. pose proof (level_depth_pos l2'). lia.
  - exfalso. simpl in H. pose proof (level_depth_pos l1'). lia.
  - simpl in H. f_equal. apply IHl1. lia.
Qed.

(* Converse of Core_ERR's level_lt_depth: depth comparison drives the order *)
Lemma depth_lt_imp_level_lt :
  forall l2 l1, (level_depth l1 < level_depth l2)%nat -> l1 << l2.
Proof.
  induction l2 as [|l2' IH]; intros l1 H.
  - exfalso. simpl in H. pose proof (level_depth_pos l1). lia.
  - simpl. simpl in H.
    assert (Hle : (level_depth l1 <= level_depth l2')%nat) by lia.
    apply Nat.le_lteq in Hle. destruct Hle as [Hlt | Heq].
    + right. apply IH. exact Hlt.
    + left. apply level_depth_inj. exact Heq.
Qed.

(* ===================== Level order is total ============================= *)

Lemma level_lt_total : forall l1 l2, l1 << l2 \/ l1 = l2 \/ l2 << l1.
Proof.
  intros l1 l2.
  destruct (Nat.lt_trichotomy (level_depth l1) (level_depth l2))
    as [Hlt | [Heq | Hgt]].
  - left. apply depth_lt_imp_level_lt. exact Hlt.
  - right; left. apply level_depth_inj. exact Heq.
  - right; right. apply depth_lt_imp_level_lt. exact Hgt.
Qed.

(* ===================== Structural well-orders (0 axioms) ================= *)

Definition well_orders {X : Type} (R : X -> X -> Prop) : Prop :=
  well_founded R /\ (forall x y, R x y \/ x = y \/ R y x).

Definition well_orderable (X : Type) : Prop := exists R : X -> X -> Prop, @well_orders X R.

Lemma nat_well_orderable : well_orderable nat.
Proof.
  exists lt. split.
  - exact Wf_nat.lt_wf.
  - intros x y. exact (Nat.lt_trichotomy x y).
Qed.

Lemma level_well_orderable : well_orderable Level.
Proof.
  exists level_lt. split.
  - exact level_lt_wf.
  - exact level_lt_total.
Qed.

(* ===================== HONEST BOUNDARY =====================
   The well-ordering THEOREM — forall X : Type, well_orderable X — is
   equivalent to the Axiom of Choice (Zermelo) and is NOT proven here. The
   carriers we use (nat, Level, and the constructive ordinal notations Ord of
   foundation/Ordinal.v) are well-ordered structurally; a GLOBAL well-ordering
   of arbitrary types is the transgressive completed-object claim P4 refuses.
   For Ord with its OLim limits we do NOT claim a decidable linear trichotomy
   either — only the structural recursion/induction of TransfiniteInduction.v. *)
