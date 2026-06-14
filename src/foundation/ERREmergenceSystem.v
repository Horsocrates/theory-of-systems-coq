(** * ERREmergenceSystem.v — deepening the emergence taxonomy: emergence at the SYSTEM level, the
      ORDER of the strata around the part->whole baseline, and the TWO AXES (relative vs absolute).

    ERREmergenceTaxonomy classified a composite's Roles R vs the product of the parts' Roles, at the
    relation level.  This file lifts that to the SYSTEM level (FunctionalSystem) and adds structure:

      ★ system-level emergence — a composite SYSTEM is emergent over its parts iff its Roles are not
        the product of the parts' Roles.  parity_system (ERREntanglement) is emergent over its bool
        parts: parity_system_emergent_over_product (its Roles /= the product, because it is
        non-separable while the product is separable).

      ★ emergence is UNDERDETERMINED by the carrier — same carrier bool*bool, two composites: the
        product (separable / reducible) and parity_system (non-separable / emergent).  Whether the
        whole is emergent is a free Roles-tier fact (the Кирпич-1 asymmetry at the emergence level).

      ★ the ORDER of the strata around the baseline — in the rsub order, super_additive sits ABOVE the
        baseline (prod_rel R1 R2 ⊆ R), sub_additive BELOW (R ⊆ prod_rel R1 R2), reducible AT it (both).

      ★ the TWO AXES — relative-to-given-parts (super/sub, vs a chosen prod_rel) vs absolute
        (non-separable, not ANY product).  parity is super-additive over (eq,eq) AND non-separable —
        the two axes are distinct.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      emergence lifted to the SYSTEM level and ORDERED around the part->whole baseline.  A composite
      SYSTEM is emergent over its parts iff its Roles /= the product of the parts' Roles; this is
      UNDERDETERMINED by the parts (Кирпич-1 at the emergence level — same carrier, two composites,
      different emergence).  The strata are ORDERED by rsub around the baseline (super above / reducible
      at / sub below).  TWO AXES: relative (super/sub) vs absolute (non-separable); parity is both.
    Roles (L4): get_Roles of the composite vs prod_rel of the parts; BEq (a bool-equivalence part);
      fs_product (the reducible composite); parity_system (the emergent one); rsub (the order).
    Elements (L1+P4): bool, bool*bool; the systems.
    P4 diagnostic (could it be otherwise?):
      a composite's emergence is NOT fixed by its parts — the same carrier admits a reducible (product)
      and an emergent (parity) whole; the whole's Roles is the free, deciding tier (Кирпич-1).
    Honesty wall:
      system-level via concrete systems (BEq / parity_system) to avoid heterogeneous-carrier transport;
      the order is the rsub-position around the baseline (a partial order, not a full lattice — "the
      lattice of emergence" only as the order around the reference point); the two axes are made
      explicit.  Builds on ERREmergenceTaxonomy + ERREntanglement.  0 axioms.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.        (* prod_rel, fs_product *)
From ToS Require Import foundation.ERRCombinationCalculus. (* rsub *)
From ToS Require Import foundation.ERREntanglement.        (* separable, prod_rel_separable, parity_roles, par, parity_system, parity_system_entangled *)
From ToS Require Import foundation.ERREmergenceTaxonomy.   (* reducible/super_additive/sub_additive/non_separable *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  A bool-equivalence part system, and the reducible (product) composite *)
(* ===================================================================== *)

(** A part system: carrier bool, Roles = equality, Rules = equivalence. *)
Definition BEq : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := bool;
            fs_relations := @eq bool; fs_functional := _;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => L1_lt_L2 |}.
  unfold EquivalenceConstitution. split; [ | split ].
  - intro x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z Hxy Hyz. transitivity y; assumption.
Defined.

Definition Hbe : fs_constitution BEq = EquivalenceConstitution := eq_refl.

(* ===================================================================== *)
(*  SYSTEM-LEVEL EMERGENCE                                                 *)
(* ===================================================================== *)

(** ★★ parity_system is EMERGENT over its bool parts: its Roles are NOT the product of the parts'
    Roles — because parity_system is non-separable while the product is separable. *)
Lemma parity_system_emergent_over_product :
  get_Roles parity_system <> get_Roles (fs_product BEq BEq Hbe Hbe).
Proof.
  intro Heq. apply parity_system_entangled. rewrite Heq. apply prod_rel_separable.
Qed.

(** ★★ Emergence is UNDERDETERMINED by the carrier: two composites over the SAME carrier bool*bool —
    the product (separable / reducible) and parity_system (non-separable / emergent).  Whether the
    whole is emergent is decided by its Roles, not by the carrier/parts (Кирпич-1). *)
Lemma emergence_underdetermined :
  separable (get_Roles (fs_product BEq BEq Hbe Hbe)) /\ ~ separable (get_Roles parity_system).
Proof.
  split; [ apply prod_rel_separable | exact parity_system_entangled ].
Qed.

(* ===================================================================== *)
(*  THE ORDER OF THE STRATA AROUND THE BASELINE                            *)
(* ===================================================================== *)

(** ★ super-additive sits ABOVE the baseline: prod_rel R1 R2 ⊆ R. *)
Lemma super_above_baseline : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop),
  super_additive R1 R2 R -> rsub (prod_rel R1 R2) R.
Proof. intros D1 D2 R1 R2 R [H _]. exact H. Qed.

(** ★ sub-additive sits BELOW the baseline: R ⊆ prod_rel R1 R2. *)
Lemma sub_below_baseline : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop),
  sub_additive R1 R2 R -> rsub R (prod_rel R1 R2).
Proof. intros D1 D2 R1 R2 R [H _]. exact H. Qed.

(** ★ reducible sits AT the baseline: R and prod_rel R1 R2 include each other. *)
Lemma reducible_at_baseline : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop),
  reducible R1 R2 R -> rsub R (prod_rel R1 R2) /\ rsub (prod_rel R1 R2) R.
Proof.
  intros D1 D2 R1 R2 R Hred. split.
  - intros p q H. exact (proj1 (Hred p q) H).
  - intros p q H. exact (proj2 (Hred p q) H).
Qed.

(* ===================================================================== *)
(*  THE TWO AXES — relative (super/sub) vs absolute (non-separable)        *)
(* ===================================================================== *)

(** ★★ parity is SUPER-ADDITIVE over (eq, eq): it relates strictly more than equality on both
    components (it relates (false,false) and (true,true), of equal parity, which equality does not). *)
Lemma parity_super_over_eq : super_additive (@eq bool) (@eq bool) parity_roles.
Proof.
  split.
  - intros p q [Ha Hb]. unfold parity_roles, par. rewrite Ha, Hb. reflexivity.
  - intro Hsub.
    assert (Hp : parity_roles (false, false) (true, true)) by reflexivity.
    specialize (Hsub (false, false) (true, true) Hp). destruct Hsub as [He _]. discriminate He.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ EMERGENCE DEEPENED:
      (system-level)     parity_system is emergent over its bool parts (Roles /= the product);
      (underdetermined)  same carrier, two composites — one separable, one not (Кирпич-1);
      (order)            super sits above the baseline, sub below, reducible at it;
      (two axes)         parity is super-additive over (eq,eq) AND non-separable absolutely.
    Emergence is a Roles-tier fact, ordered around the part->whole baseline, with a relative and an
    absolute axis. *)
Theorem err_emergence_deepened :
  (get_Roles parity_system <> get_Roles (fs_product BEq BEq Hbe Hbe))
  /\ (separable (get_Roles (fs_product BEq BEq Hbe Hbe)) /\ ~ separable (get_Roles parity_system))
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
            (R : (D1 * D2) -> (D1 * D2) -> Prop), super_additive R1 R2 R -> rsub (prod_rel R1 R2) R)
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
            (R : (D1 * D2) -> (D1 * D2) -> Prop), sub_additive R1 R2 R -> rsub R (prod_rel R1 R2))
  /\ (super_additive (@eq bool) (@eq bool) parity_roles /\ non_separable parity_roles).
Proof.
  split; [ exact parity_system_emergent_over_product | ].
  split; [ exact emergence_underdetermined | ].
  split; [ exact @super_above_baseline | ].
  split; [ exact @sub_below_baseline | ].
  split; [ exact parity_super_over_eq | exact parity_not_separable ].
Qed.

Print Assumptions err_emergence_deepened.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  7 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Deepens ERREmergenceTaxonomy.  SYSTEM-LEVEL: parity_system_emergent_over_  *)
(*  product (parity_system's Roles /= the product of its bool parts, since it  *)
(*  is non-separable while the product is separable); emergence_underdetermined*)
(*  (same carrier bool*bool, the product is separable, parity_system is not —  *)
(*  emergence is a Roles-tier fact, Кирпич-1).  ORDER around the baseline:      *)
(*  super_above_baseline / sub_below_baseline / reducible_at_baseline (the      *)
(*  rsub-position of each stratum).  TWO AXES: parity_super_over_eq (parity is  *)
(*  super-additive over (eq,eq)) AND non_separable parity_roles — relative vs   *)
(*  absolute emergence are distinct.  Capstone err_emergence_deepened.  HONEST: *)
(*  concrete systems (BEq/parity_system) to avoid heterogeneous transport; the  *)
(*  order is a partial order around the reference, not a full lattice.         *)
(* ========================================================================= *)
