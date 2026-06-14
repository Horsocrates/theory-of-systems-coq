(** * ERRCombinationCalculus.v — the COMBINATION CALCULUS of the three tiers: when systems combine to
      form a new system, each tier combines by a DIFFERENT operation, and the operations are ordered
      by INCREASING CONSTRAINT — Elements (free product), Roles (meet-baseline, emergence-capable, plus
      sequential composition), Rules (gated meet in the Constitution lattice).

    This deepens the rank asymmetry (ERRRankAsymmetry.v: "Rules gate") into a full calculus: the
    asymmetry is not just that Rules gate composability — it is that the THREE TIERS each combine by an
    operation of a DIFFERENT character, and the character gets MORE CONSTRAINED as you go up:
      Elements:  product (x)        — UNCONDITIONAL (every pair of elements exists);
      Roles:     prod_rel (meet)    — a BASELINE the composite can STRICTLY EXCEED (emergence);
                 rcomp (sequential) — Roles also have an algebra (associative, unital);
      Rules:     cmeet (lattice)    — GATED by product_closed: some Rules do NOT combine (connex).

    Anatomy of each constituent (the orders/algebras), then the combination law per tier.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) on combining systems, each tier combines by a DIFFERENT operation, with constraint INCREASING
          up the tiers;
      (2) Elements combine by the product, UNCONDITIONALLY (every pair exists);
      (3) Roles combine by the prod_rel meet-baseline, which the composite can STRICTLY EXCEED
          (emergence); Roles also compose SEQUENTIALLY (rcomp: associative, unital);
      (4) Rules combine by the lattice meet cmeet, GATED by product_closed (connex does NOT combine).
    Roles (L4): cstronger/cmeet (the Rules lattice); rsub/rcomp (the Roles order + algebra); the
      product type (Elements).
    Elements (L1+P4): Constitutions; relations; carriers; the concrete witnesses bool / eq / the full
      relation / equivalence / connex.
    P4 diagnostic (could it be otherwise?):
      the answer DIFFERS per tier and GROWS: Elements no (the product is forced — every pair exists),
      Roles yes-above-the-baseline (emergence is the freedom over prod_rel), Rules constrained (the
      gate forbids connex).  That gradient IS the rank asymmetry realized as a combination calculus.
    Honesty wall:
      this is the abstract tier (orders, meets, the gate), deepening ERRRankAsymmetry from "Rules gate"
      to "each tier combines by an operation of increasing constraint".  NOT a full lattice-theoretic
      classification (no completeness of the Constitution lattice, no general emergence taxonomy);
      witnesses are concrete.  cmeet is the lattice meet, NOT a claim that every composite's Rule IS
      the meet (that needs both parts to satisfy both constitutions — flagged).  0 axioms.

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.    (* Constitution, TrivialConstitution, EquivalenceConstitution *)
From ToS Require Import foundation.ERRComposition.    (* prod_rel, product_closed, ConnexConstitution + the gate lemmas *)

(* ===================================================================== *)
(*  ELEMENTS — the free tier: combine by the product, unconditionally     *)
(* ===================================================================== *)

(** ★ Elements combine FREELY: for any two carriers, every pair of elements exists as a combined
    element (the product type is total — no constraint).  Contrast Rules (gated, below). *)
Lemma elements_combine_free : forall (A B : Type) (a : A) (b : B),
  exists p : A * B, fst p = a /\ snd p = b.
Proof. intros A B a b. exists (a, b). split; reflexivity. Qed.

(* ===================================================================== *)
(*  ROLES — the middle tier: an order, a meet-baseline + emergence,        *)
(*          and a sequential composition algebra                          *)
(* ===================================================================== *)

(** The Roles order: relation inclusion. *)
Definition rsub {D : Type} (R1 R2 : D -> D -> Prop) : Prop :=
  forall x y, R1 x y -> R2 x y.

(** ★ The Roles order is a preorder (reflexive + transitive) — the anatomy of the Roles tier. *)
Lemma rsub_refl : forall {D} (R : D -> D -> Prop), rsub R R.
Proof. intros D R x y H. exact H. Qed.

Lemma rsub_trans : forall {D} (R S T : D -> D -> Prop), rsub R S -> rsub S T -> rsub R T.
Proof. intros D R S T H1 H2 x y H. apply H2. apply H1. exact H. Qed.

(** Sequential role composition (the algebra of Roles: a role followed by a role). *)
Definition rcomp {D : Type} (R S : D -> D -> Prop) : D -> D -> Prop :=
  fun x z => exists y, R x y /\ S y z.

(** The identity role. *)
Definition rid {D : Type} : D -> D -> Prop := @eq D.

(** ★★ Sequential role composition is ASSOCIATIVE. *)
Lemma rcomp_assoc : forall (D : Type) (R S T : D -> D -> Prop) (x z : D),
  rcomp (rcomp R S) T x z <-> rcomp R (rcomp S T) x z.
Proof.
  intros D R S T x z. unfold rcomp. split.
  - intros [y [[w [HRxw HSwy]] HTyz]]. exists w. split; [ exact HRxw | ]. exists y. split; [ exact HSwy | exact HTyz ].
  - intros [w [HRxw [y [HSwy HTyz]]]]. exists y. split; [ | exact HTyz ]. exists w. split; [ exact HRxw | exact HSwy ].
Qed.

(** ★ The identity role is a LEFT unit for sequential composition. *)
Lemma rcomp_id_l : forall (D : Type) (R : D -> D -> Prop) (x y : D), rcomp rid R x y <-> R x y.
Proof.
  intros D R x y. unfold rcomp, rid. split.
  - intros [z [Hxz HRzy]]. subst z. exact HRzy.
  - intro H. exists x. split; [ reflexivity | exact H ].
Qed.

(** ★ The identity role is a RIGHT unit for sequential composition. *)
Lemma rcomp_id_r : forall (D : Type) (R : D -> D -> Prop) (x y : D), rcomp R rid x y <-> R x y.
Proof.
  intros D R x y. unfold rcomp, rid. split.
  - intros [z [HRxz Hzy]]. subst z. exact HRxz.
  - intro H. exists y. split; [ exact H | reflexivity ].
Qed.

(** ★★ EMERGENCE: the composite's Roles can STRICTLY EXCEED the product baseline — the whole relates
    pairs that the parts' product does not.  (prod_rel eq eq is the baseline; the full relation is a
    legitimate composite Roles that strictly contains it — e.g. it relates (true,false) and
    (false,true), which the baseline does not.)  Roles-combination is NOT determined by the parts. *)
Lemma roles_super_additive :
  exists (m1 m2 : bool -> bool -> Prop) (R : (bool * bool) -> (bool * bool) -> Prop),
    rsub (prod_rel m1 m2) R /\ ~ rsub R (prod_rel m1 m2).
Proof.
  exists (@eq bool), (@eq bool), (fun _ _ => True). split.
  - intros x y H. exact I.
  - intro Hsub. specialize (Hsub (true, false) (false, true) I).
    destruct Hsub as [He _]. discriminate He.
Qed.

(* ===================================================================== *)
(*  RULES — the top tier: the Constitution LATTICE, with a combination GATE *)
(* ===================================================================== *)

(** The Rules order: a Constitution refines another if everything it accepts, the other accepts. *)
Definition cstronger (C1 C2 : Constitution) : Prop :=
  forall (D : Type) (R : D -> D -> Prop), C1 D R -> C2 D R.

(** The meet of two Constitutions: accept iff BOTH accept. *)
Definition cmeet (C1 C2 : Constitution) : Constitution :=
  fun D R => C1 D R /\ C2 D R.

(** ★ The meet is a lower bound: it refines each factor. *)
Lemma cmeet_refines_l : forall C1 C2, cstronger (cmeet C1 C2) C1.
Proof. intros C1 C2 D R [H _]. exact H. Qed.

Lemma cmeet_refines_r : forall C1 C2, cstronger (cmeet C1 C2) C2.
Proof. intros C1 C2 D R [_ H]. exact H. Qed.

(** ★★ The meet is the GREATEST lower bound: any common refinement refines the meet. *)
Lemma cmeet_glb : forall (C C1 C2 : Constitution),
  cstronger C C1 -> cstronger C C2 -> cstronger C (cmeet C1 C2).
Proof. intros C C1 C2 H1 H2 D R HC. split; [ apply H1 | apply H2 ]; exact HC. Qed.

(** ★ TrivialConstitution is the TOP of the lattice (everything refines it). *)
Lemma trivial_top : forall C, cstronger C TrivialConstitution.
Proof. intros C D R _. exact I. Qed.

(** ★★ The COMBINABLE Rules (the product-closed ones) are themselves closed under meet — they form a
    SUB-LATTICE.  So the gate is structured: combinability is preserved by meet. *)
Lemma cmeet_product_closed : forall C1 C2,
  product_closed C1 -> product_closed C2 -> product_closed (cmeet C1 C2).
Proof.
  intros C1 C2 P1 P2 D1 R1 D2 R2 H1 H2.
  destruct H1 as [H1a H1b]. destruct H2 as [H2a H2b].
  split; [ apply P1 | apply P2 ]; assumption.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the combination calculus (increasing constraint up the tiers) *)
(* ===================================================================== *)

(** ★★★ THE COMBINATION CALCULUS: when systems combine to form a new system, each tier combines by a
    different operation, of INCREASING CONSTRAINT:
      (Elements, FREE)   every pair of elements exists — the product is unconditional;
      (Roles, EMERGENT)  the product is a meet-baseline the composite can STRICTLY EXCEED;
      (Roles, ALGEBRA)   Roles also compose sequentially, with the identity a unit;
      (Rules, LATTICE)   Constitutions form a lattice (meet = greatest lower bound) ...
      (Rules, SUBLATTICE) ... the combinable (product-closed) Rules are closed under meet ...
      (Rules, GATED)     ... but combination is GATED: equivalence combines, connex does NOT.
    Elements free < Roles meet-with-emergence < Rules gated meet — the rank asymmetry as a calculus. *)
Theorem err_combination_calculus :
  (forall (A B : Type) (a : A) (b : B), exists p : A * B, fst p = a /\ snd p = b)
  /\ (exists (m1 m2 : bool -> bool -> Prop) (R : (bool * bool) -> (bool * bool) -> Prop),
        rsub (prod_rel m1 m2) R /\ ~ rsub R (prod_rel m1 m2))
  /\ (forall (D : Type) (R : D -> D -> Prop) (x y : D), rcomp rid R x y <-> R x y)
  /\ (forall (C C1 C2 : Constitution), cstronger C C1 -> cstronger C C2 -> cstronger C (cmeet C1 C2))
  /\ (forall C1 C2, product_closed C1 -> product_closed C2 -> product_closed (cmeet C1 C2))
  /\ (product_closed EquivalenceConstitution /\ ~ product_closed ConnexConstitution).
Proof.
  split; [ exact elements_combine_free | ].
  split; [ exact roles_super_additive | ].
  split; [ exact rcomp_id_l | ].
  split; [ exact cmeet_glb | ].
  split; [ exact cmeet_product_closed | ].
  split; [ exact equiv_product_closed | exact connex_not_product_closed ].
Qed.

Print Assumptions err_combination_calculus.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  13 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The COMBINATION CALCULUS: each tier combines by a different operation of   *)
(*  increasing constraint.  ELEMENTS — elements_combine_free (product, every   *)
(*  pair exists, unconditional).  ROLES — rsub (order: rsub_refl/trans),       *)
(*  rcomp (sequential algebra: rcomp_assoc/id_l/id_r), roles_super_additive    *)
(*  (EMERGENCE: composite Roles strictly exceed the prod_rel baseline).  RULES *)
(*  — cstronger/cmeet (Constitution lattice: cmeet_refines_l/r, cmeet_glb,     *)
(*  trivial_top), cmeet_product_closed (combinable Rules = a sub-lattice), and *)
(*  the GATE (equiv_product_closed YES, connex_not_product_closed NO).         *)
(*  Capstone err_combination_calculus.  Deepens ERRRankAsymmetry "Rules gate"  *)
(*  into a full calculus: Elements free < Roles meet+emergence < Rules gated.  *)
(*  HONEST: abstract tier; concrete witnesses; no lattice-completeness / no    *)
(*  general emergence taxonomy; cmeet is the meet, not the claim that every     *)
(*  composite Rule IS the meet.                                               *)
(* ========================================================================= *)
