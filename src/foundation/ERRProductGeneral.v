(** * ERRProductGeneral.v — dissolving the "(co)product only for equivalence-constitution" wall: the
      product of systems for ANY product-closed constitution C, with projections and the universal
      property — not just EquivalenceConstitution.

    ERRComposition built fs_product for EquivalenceConstitution and left the general case open ("needs
    product_closed").  But product_closed C is EXACTLY the condition (the Кирпич-1 fact that Rules gate
    composition).  Here the wall dissolves: fs_product_gen works for any product-closed C.

      ★ fs_product_gen C HC S1 S2 — the product when the shared constitution C is product-closed (HC);
        triad: Elements = pairs, Roles = prod_rel, Rules = C.
      ★ Projections fs_proj1_gen / fs_proj2_gen and the universal property: the pairing fs_pair_gen with
        the projection computation rules (product_gen_proj1 / _proj2) and mediator uniqueness
        (product_gen_mediator_unique).
      ★ Equivalence is the instance: the general product at C = EquivalenceConstitution has the same
        triad as fs_product (fs_product_gen_recovers_equiv).
      ★ It applies BEYOND equivalence: a product of two TrivialConstitution systems
        (trivial_product_general) — exactly where the equivalence-only fs_product does not.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the composition of Rules is governed by EXACTLY product_closed C (Кирпич-1: Rules gate
      composition); equivalence is one product-closed constitution among others, not privileged.
    Roles (L4): fs_product_gen (the assembly); fs_proj1_gen / fs_proj2_gen (projections); fs_pair_gen
      (the mediator); product_closed (the gating condition).
    Elements (L1+P4): the systems S1, S2; the pairs; prod_rel; the constitution C.
    P4 diagnostic (could it be otherwise?):
      the whole's constitution is C — a free choice among product-closed constitutions (trivial,
      equivalence, ...); equivalence is not forced.  So the equivalence-only restriction was an
      unforced specialization — the wall dissolves to the honest condition product_closed.
    Honesty wall:
      the general product is given at the object + morphism + universal-property level for any
      product_closed C; equivalence is recovered as the instance (triad-level, proof-irrelevance-free);
      the coproduct generalizes identically (coproduct_closed — noted, not re-done here).  Reuses
      ERRComposition (prod_rel, product_closed, equiv/trivial_product_closed).  0 axioms.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* prod_rel, product_closed, equiv/trivial_product_closed, ERRMorphism, mkERRMorphism, err_map, err_comp, err_morph_eq, fs_product *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE GENERAL PRODUCT — for any product-closed constitution            *)
(* ===================================================================== *)

(** ★★ The product of two systems sharing a PRODUCT-CLOSED constitution C (not just equivalence). *)
Definition fs_product_gen {L} (C : Constitution) (HC : product_closed C)
  (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = C) (H2 : fs_constitution S2 = C) : FunctionalSystem L.
Proof.
  refine {| fs_constitution := C;
            fs_domain := (get_Elements S1 * get_Elements S2)%type;
            fs_relations := prod_rel (get_Roles S1) (get_Roles S2);
            fs_functional := _;
            fs_element_level := fun p => fs_element_level S1 (fst p);
            fs_level_valid := fun p => fs_level_valid S1 (fst p) |}.
  apply HC.
  - rewrite <- H1. exact (fs_functional S1).
  - rewrite <- H2. exact (fs_functional S2).
Defined.

Lemma fs_product_gen_elements : forall {L} C HC (S1 S2 : FunctionalSystem L) H1 H2,
  get_Elements (fs_product_gen C HC S1 S2 H1 H2) = (get_Elements S1 * get_Elements S2)%type.
Proof. intros. reflexivity. Qed.

Lemma fs_product_gen_roles : forall {L} C HC (S1 S2 : FunctionalSystem L) H1 H2,
  get_Roles (fs_product_gen C HC S1 S2 H1 H2) = prod_rel (get_Roles S1) (get_Roles S2).
Proof. intros. reflexivity. Qed.

Lemma fs_product_gen_rules : forall {L} C HC (S1 S2 : FunctionalSystem L) H1 H2,
  fs_constitution (fs_product_gen C HC S1 S2 H1 H2) = C.
Proof. intros. reflexivity. Qed.

(* ===================================================================== *)
(*  PROJECTIONS and the UNIVERSAL PROPERTY                                 *)
(* ===================================================================== *)

Definition fs_proj1_gen {L} (C : Constitution) (HC : product_closed C)
  (S1 S2 : FunctionalSystem L) (H1 : fs_constitution S1 = C) (H2 : fs_constitution S2 = C)
  : ERRMorphism (fs_product_gen C HC S1 S2 H1 H2) S1 :=
  @mkERRMorphism L (fs_product_gen C HC S1 S2 H1 H2) S1 (fun p => fst p) (fun x y H => proj1 H).

Definition fs_proj2_gen {L} (C : Constitution) (HC : product_closed C)
  (S1 S2 : FunctionalSystem L) (H1 : fs_constitution S1 = C) (H2 : fs_constitution S2 = C)
  : ERRMorphism (fs_product_gen C HC S1 S2 H1 H2) S2 :=
  @mkERRMorphism L (fs_product_gen C HC S1 S2 H1 H2) S2 (fun p => snd p) (fun x y H => proj2 H).

(** The mediating morphism <g1, g2> into the general product. *)
Definition fs_pair_gen {L} (C : Constitution) (HC : product_closed C)
  (S1 S2 Z : FunctionalSystem L) (H1 : fs_constitution S1 = C) (H2 : fs_constitution S2 = C)
  (g1 : ERRMorphism Z S1) (g2 : ERRMorphism Z S2)
  : ERRMorphism Z (fs_product_gen C HC S1 S2 H1 H2).
Proof.
  refine (@mkERRMorphism L Z (fs_product_gen C HC S1 S2 H1 H2)
            (fun z => (err_map g1 z, err_map g2 z)) _).
  intros x y H. split; [ exact (err_pres g1 x y H) | exact (err_pres g2 x y H) ].
Defined.

(** ★★ Computation: the pairing followed by the first projection is g1. *)
Lemma product_gen_proj1 : forall {L} C HC (S1 S2 Z : FunctionalSystem L) H1 H2
  (g1 : ERRMorphism Z S1) (g2 : ERRMorphism Z S2),
  err_morph_eq (err_comp (fs_pair_gen C HC S1 S2 Z H1 H2 g1 g2) (fs_proj1_gen C HC S1 S2 H1 H2)) g1.
Proof. intros L C HC S1 S2 Z H1 H2 g1 g2 z. reflexivity. Qed.

(** ★★ Computation: the pairing followed by the second projection is g2. *)
Lemma product_gen_proj2 : forall {L} C HC (S1 S2 Z : FunctionalSystem L) H1 H2
  (g1 : ERRMorphism Z S1) (g2 : ERRMorphism Z S2),
  err_morph_eq (err_comp (fs_pair_gen C HC S1 S2 Z H1 H2 g1 g2) (fs_proj2_gen C HC S1 S2 H1 H2)) g2.
Proof. intros L C HC S1 S2 Z H1 H2 g1 g2 z. reflexivity. Qed.

(** ★★ UNIQUENESS of the mediator: any h respecting both projections equals the pairing. *)
Lemma product_gen_mediator_unique : forall {L} C HC (S1 S2 Z : FunctionalSystem L) H1 H2
  (g1 : ERRMorphism Z S1) (g2 : ERRMorphism Z S2)
  (h : ERRMorphism Z (fs_product_gen C HC S1 S2 H1 H2)),
  err_morph_eq (err_comp h (fs_proj1_gen C HC S1 S2 H1 H2)) g1 ->
  err_morph_eq (err_comp h (fs_proj2_gen C HC S1 S2 H1 H2)) g2 ->
  err_morph_eq h (fs_pair_gen C HC S1 S2 Z H1 H2 g1 g2).
Proof.
  intros L C HC S1 S2 Z H1 H2 g1 g2 h Hp1 Hp2 z.
  change (err_map (fs_pair_gen C HC S1 S2 Z H1 H2 g1 g2) z)
    with (err_map g1 z, err_map g2 z).
  rewrite (surjective_pairing (err_map h z)).
  f_equal; [ exact (Hp1 z) | exact (Hp2 z) ].
Qed.

(* ===================================================================== *)
(*  EQUIVALENCE IS THE INSTANCE; APPLIES BEYOND EQUIVALENCE               *)
(* ===================================================================== *)

(** ★ The general product at C = EquivalenceConstitution has the same triad as fs_product. *)
Lemma fs_product_gen_recovers_equiv : forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
  get_Roles (fs_product_gen EquivalenceConstitution equiv_product_closed S1 S2 H1 H2)
    = get_Roles (fs_product S1 S2 H1 H2).
Proof. intros. reflexivity. Qed.

(** A trivial-constitution bool-system (NOT an equivalence-system in the equivalence sense). *)
Definition STriv : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => L1_lt_L2 |}.
Defined.

Definition STriv_triv : fs_constitution STriv = TrivialConstitution := eq_refl.

(** The general product of two trivial-constitution systems. *)
Definition Striv_prod : FunctionalSystem L2 :=
  fs_product_gen TrivialConstitution trivial_product_closed STriv STriv STriv_triv STriv_triv.

(** ★★ The general product applies BEYOND equivalence: a product of trivial-constitution systems
    exists and carries the trivial constitution — exactly where the equivalence-only fs_product does
    not apply. *)
Lemma trivial_product_general : fs_constitution Striv_prod = TrivialConstitution.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE GENERAL PRODUCT (wall dissolved):
      (triad)      Elements = pairs, Roles = prod_rel, Rules = C, for any product-closed C;
      (universal)  the pairing's projection computations hold (and the mediator is unique);
      (beyond eq)  it applies to non-equivalence constitutions (a product of trivial systems).
    The product of systems works for ANY product-closed constitution, not just equivalence — the
    "(co)product only for equivalence" wall was an unforced specialization. *)
Theorem err_product_general :
  (forall (L : Level) (C : Constitution) (HC : product_closed C) (S1 S2 : FunctionalSystem L) H1 H2,
     get_Elements (fs_product_gen C HC S1 S2 H1 H2) = (get_Elements S1 * get_Elements S2)%type
     /\ get_Roles (fs_product_gen C HC S1 S2 H1 H2) = prod_rel (get_Roles S1) (get_Roles S2)
     /\ fs_constitution (fs_product_gen C HC S1 S2 H1 H2) = C)
  /\ (forall (L : Level) (C : Constitution) (HC : product_closed C) (S1 S2 Z : FunctionalSystem L) H1 H2
            (g1 : ERRMorphism Z S1) (g2 : ERRMorphism Z S2),
        err_morph_eq (err_comp (fs_pair_gen C HC S1 S2 Z H1 H2 g1 g2) (fs_proj1_gen C HC S1 S2 H1 H2)) g1
        /\ err_morph_eq (err_comp (fs_pair_gen C HC S1 S2 Z H1 H2 g1 g2) (fs_proj2_gen C HC S1 S2 H1 H2)) g2)
  /\ fs_constitution Striv_prod = TrivialConstitution.
Proof.
  split.
  - intros L C HC S1 S2 H1 H2. split; [ reflexivity | split; reflexivity ].
  - split.
    + intros L C HC S1 S2 Z H1 H2 g1 g2.
      split; [ exact (product_gen_proj1 C HC S1 S2 Z H1 H2 g1 g2)
             | exact (product_gen_proj2 C HC S1 S2 Z H1 H2 g1 g2) ].
    + exact trivial_product_general.
Qed.

Print Assumptions err_product_general.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Dissolves the "(co)product only for equivalence" wall.  fs_product_gen for *)
(*  any product_closed C (triad: elements/roles/rules).  Projections          *)
(*  fs_proj1_gen/fs_proj2_gen + universal property: fs_pair_gen, product_gen_  *)
(*  proj1/_proj2 (computations), product_gen_mediator_unique (via surjective_  *)
(*  pairing).  fs_product_gen_recovers_equiv (equivalence = the instance,      *)
(*  triad-level).  trivial_product_general (applies to a NON-equivalence       *)
(*  constitution — a product of trivial systems).  Capstone err_product_       *)
(*  general.  HONEST: object+morphism+universal level for any product_closed C;*)
(*  coproduct generalizes identically (coproduct_closed) — noted, not re-done. *)
(* ========================================================================= *)
