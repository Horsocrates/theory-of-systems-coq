(** * ERREmergenceTaxonomy.v — the GENERAL EMERGENCE TAXONOMY: a composite's Roles classified by how
      they relate to the product of the parts' Roles (the part->whole baseline of ERRProperty #128).
      Four strata, each inhabited; the three emergent ones lie OUTSIDE the part->whole image.

    ERRProperty (#128) defined emergence as "a whole-property outside the image of the part->whole map"
    and gave ONE instance (non-separability / parity).  This file unfolds the full taxonomy.  Given
    parts with Roles R1, R2, the whole's Roles R compares to the baseline prod_rel R1 R2:

      ★ reducible      — R = prod_rel R1 R2: the whole IS the product of its parts (independent parts,
                         in the part->whole image; reducible => separable).
      ★ super_additive — R strictly CONTAINS prod_rel R1 R2: the whole relates MORE than its parts'
                         product (emergent coupling ADDS relations).  This is the KnowledgeCollective
                         emergence: the collective relates A->C from A->B + B->C, no member does.
      ★ sub_additive   — R strictly CONTAINED in prod_rel R1 R2: the whole relates LESS (emergent
                         CONSTRAINT removes marginally-allowed pairs = correlation/coupling).
      ★ non_separable  — R is not ANY product (the sharpest emergence — entanglement, ERREntanglement).

    Each stratum has a witness; the emergent three are provably OUTSIDE reducible.  (Exhaustiveness —
    that every R is exactly one — is NOT claimed: it would need decidability / classic.)

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      emergence is classified by how the whole's Roles relate to the product of the parts' Roles (the
      part->whole baseline): EQUAL (reducible), strictly MORE (super-additive), strictly LESS
      (sub-additive), or NOT-ANY-PRODUCT (non-separable).  Four strata; the three emergent ones lie
      outside the part->whole image.
    Roles (L4): reducible / super_additive / sub_additive / non_separable (the predicates); rsub (the
      order, ERRCombinationCalculus); prod_rel (the baseline, ERRComposition); the witnesses
      (eq / full / diagonal / parity).
    Elements (L1+P4): the bool carriers; the relations.
    P4 diagnostic (could it be otherwise?):
      the whole's Roles need NOT equal the product of the parts' Roles — they can exceed (super), fall
      short (sub), or fail to be a product at all (non-separable).  The four are genuinely distinct
      (each inhabited) and the emergent three are FORCED outside reducible (strict inclusion).
      Exhaustiveness is NOT claimed (would need decidability/classic) — honest.
    Honesty wall:
      a classification of R vs prod_rel(parts), generalizing ERRProperty's single instance into four
      inhabited, pairwise-distinct strata; exhaustiveness not claimed.  super-additive = the
      KnowledgeCollective emergence, sub-additive = correlation/constraint, non-separable = entanglement
      (cited).  Built on ERRComposition / ERRCombinationCalculus / ERREntanglement.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import foundation.ERRComposition.        (* prod_rel *)
From ToS Require Import foundation.ERRCombinationCalculus. (* rsub *)
From ToS Require Import foundation.ERREntanglement.        (* separable, parity_roles, parity_not_separable *)

(* ===================================================================== *)
(*  THE FOUR STRATA — R vs the product of the parts' Roles                 *)
(* ===================================================================== *)

(** REDUCIBLE: the whole IS the product of its parts (independent parts; in the part->whole image). *)
Definition reducible {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  forall p q, R p q <-> prod_rel R1 R2 p q.

(** SUPER-ADDITIVE: the whole relates MORE than the parts' product (emergent coupling adds relations). *)
Definition super_additive {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  rsub (prod_rel R1 R2) R /\ ~ rsub R (prod_rel R1 R2).

(** SUB-ADDITIVE: the whole relates LESS (emergent constraint removes marginally-allowed pairs). *)
Definition sub_additive {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  rsub R (prod_rel R1 R2) /\ ~ rsub (prod_rel R1 R2) R.

(** NON-SEPARABLE: the whole is not ANY product (the sharpest emergence). *)
Definition non_separable {D1 D2 : Type} (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  ~ separable R.

(* ===================================================================== *)
(*  EACH STRATUM IS INHABITED                                              *)
(* ===================================================================== *)

(** ★ REDUCIBLE inhabited: parts eq, whole = their product. *)
Lemma reducible_inhabited :
  reducible (@eq bool) (@eq bool) (prod_rel (@eq bool) (@eq bool)).
Proof. intros p q. split; intro H; exact H. Qed.

(** ★★ SUPER-ADDITIVE inhabited: parts eq, whole = the FULL relation (relates more — e.g. it relates
    (true,false) and (false,true), which the product of the marginals does not). *)
Lemma super_additive_inhabited :
  super_additive (@eq bool) (@eq bool) (fun _ _ => True).
Proof.
  split.
  - intros p q H. exact I.
  - intro Hsub. specialize (Hsub (true, false) (false, true) I).
    destruct Hsub as [He _]. discriminate He.
Qed.

(** ★★ SUB-ADDITIVE inhabited: parts FULL (anything allowed), whole = the diagonal (only identical
    states relate) — the whole relates strictly LESS than the product (a correlation/constraint). *)
Lemma sub_additive_inhabited :
  sub_additive (fun _ _ : bool => True) (fun _ _ : bool => True) (fun p q : bool * bool => p = q).
Proof.
  split.
  - intros p q H. split; exact I.
  - intro Hsub. specialize (Hsub (true, false) (false, true) (conj I I)). discriminate Hsub.
Qed.

(** ★★ NON-SEPARABLE inhabited: the parity (Bell/GHZ) correlation (ERREntanglement). *)
Lemma non_separable_inhabited : non_separable parity_roles.
Proof. exact parity_not_separable. Qed.

(* ===================================================================== *)
(*  THE EMERGENT STRATA LIE OUTSIDE THE PART -> WHOLE IMAGE                *)
(* ===================================================================== *)

(** ★ REDUCIBLE is in the image: a reducible whole is separable (a product). *)
Lemma reducible_is_separable : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop),
  reducible R1 R2 R -> separable R.
Proof. intros D1 D2 R1 R2 R Hred. exists R1, R2. exact Hred. Qed.

(** ★★ SUPER-ADDITIVE is emergent: it is NOT reducible (the whole relates strictly more). *)
Lemma super_not_reducible : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop),
  super_additive R1 R2 R -> ~ reducible R1 R2 R.
Proof.
  intros D1 D2 R1 R2 R [_ Hnle] Hred. apply Hnle.
  intros p q HR. exact (proj1 (Hred p q) HR).
Qed.

(** ★★ SUB-ADDITIVE is emergent: it is NOT reducible (the whole relates strictly less). *)
Lemma sub_not_reducible : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  (R : (D1 * D2) -> (D1 * D2) -> Prop),
  sub_additive R1 R2 R -> ~ reducible R1 R2 R.
Proof.
  intros D1 D2 R1 R2 R [_ Hnle] Hred. apply Hnle.
  intros p q HP. exact (proj2 (Hred p q) HP).
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE EMERGENCE TAXONOMY: four inhabited strata by R vs the product of the parts' Roles —
      reducible (whole = product, in the image, separable);
      super-additive (whole relates MORE — KnowledgeCollective emergence) — NOT reducible;
      sub-additive (whole relates LESS — correlation/constraint) — NOT reducible;
      non-separable (whole is not any product — entanglement).
    Emergence = the whole's Roles deviating from the part->whole baseline; three genuine directions. *)
Theorem err_emergence_taxonomy :
  reducible (@eq bool) (@eq bool) (prod_rel (@eq bool) (@eq bool))
  /\ super_additive (@eq bool) (@eq bool) (fun _ _ => True)
  /\ sub_additive (fun _ _ : bool => True) (fun _ _ : bool => True) (fun p q : bool * bool => p = q)
  /\ non_separable parity_roles
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
            (R : (D1 * D2) -> (D1 * D2) -> Prop), reducible R1 R2 R -> separable R)
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
            (R : (D1 * D2) -> (D1 * D2) -> Prop), super_additive R1 R2 R -> ~ reducible R1 R2 R)
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
            (R : (D1 * D2) -> (D1 * D2) -> Prop), sub_additive R1 R2 R -> ~ reducible R1 R2 R).
Proof.
  split; [ exact reducible_inhabited | ].
  split; [ exact super_additive_inhabited | ].
  split; [ exact sub_additive_inhabited | ].
  split; [ exact non_separable_inhabited | ].
  split; [ exact @reducible_is_separable | ].
  split; [ exact @super_not_reducible | exact @sub_not_reducible ].
Qed.

Print Assumptions err_emergence_taxonomy.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The GENERAL EMERGENCE TAXONOMY (extends ERRProperty #128): a composite's   *)
(*  Roles R classified vs the product of the parts' Roles prod_rel R1 R2.      *)
(*  reducible (R = product, in the part->whole image; reducible_is_separable), *)
(*  super_additive (R strictly contains the product — whole relates MORE —      *)
(*  KnowledgeCollective emergence), sub_additive (R strictly inside — whole     *)
(*  relates LESS — correlation/constraint), non_separable (R is not any         *)
(*  product — entanglement).  Each inhabited (reducible/super/sub/non_separable *)
(*  _inhabited, witnesses eq/full/diagonal/parity); the emergent three are      *)
(*  OUTSIDE reducible (super_not_reducible, sub_not_reducible).  Capstone       *)
(*  err_emergence_taxonomy.  HONEST: classification, four inhabited distinct    *)
(*  strata; exhaustiveness NOT claimed (needs decidability/classic).  Builds    *)
(*  on ERRComposition / ERRCombinationCalculus / ERREntanglement.             *)
(* ========================================================================= *)
