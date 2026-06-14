(** * ERR2Category.v — the SECOND dimension of the E/R/R system category: Roles as 2-cells.

    The 1-categorical core gave objects (FunctionalSystems), 1-morphisms (ERRMorphisms =
    Element-maps preserving Roles), and equality of morphisms.  But the ROLES tier had no
    categorical voice yet.  This file gives it one: the Roles of the TARGET system ARE the
    2-cells (morphisms between parallel 1-morphisms).

      A 2-cell  α : f ⟹ g   (f g : S1 → S2)  is   `forall x, get_Roles S2 (f x) (g x)`
      — "f and g land in Roles-connected places everywhere" = f and g are THE SAME map from
      the system's own (Roles) standpoint (the categorical face of P3 / intensional identity).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      "two parallel maps are the same FROM THE SYSTEM'S OWN STANDPOINT  iff  they are Roles-
      connected pointwise."  Vertical composition / identity of 2-cells require the target's
      Roles to be an EQUIVALENCE — which is exactly what an equivalence-Constitution supplies
      (equiv_system_roles_equiv).  So the RULES tier fixes the coherence of the 2-dimension:
      rank asymmetry Rules>Roles>Elements becomes the DIMENSION of the category.
    Roles (L4): the 2-cells themselves (Roles2) — Roles become first-class as morphisms-of-
      morphisms; composition is a congruence for them (whiskering = err_pres re-read as
      2-functoriality of the 1-morphisms).
    Elements (L1+P4): carriers, maps, witnesses; a 2-cell is checked POINTWISE on actual
      elements — finite/actual, no completed infinity.
    P4 diagnostic (could it be otherwise?):
      No.  Morphisms preserve Roles (err_pres), so the only structure-respecting "transformation
      between maps" the triad offers is Roles-connectedness.  Elements give only equality (too
      fine — discrete, trivial 2-structure); Rules give only the global frame (too coarse).
      Roles is the unique MIDDLE tier yielding a nontrivial-yet-coherent 2-structure.  Forced.
    Honesty wall:
      Roles are Prop-valued ⟹ the 2-category is LOCALLY THIN (hom-setoids).  The strict
      2-category laws (associativity / interchange as EQUALITIES of 2-cell proofs) hold only up
      to proof-irrelevance of the Roles relation — NOT claimed here (would need an axiom).
      Instead we prove the CONGRUENCE / setoid-enrichment form (Roles2 is an equivalence on each
      hom-set; composition is a congruence for it) — fully, 0 axioms.  Whiskering needs NO
      hypothesis (pure err_pres); identity / vertical / horizontal composition need the target
      Roles to be an equivalence (= the Rules gate, same as everywhere in the thread).
      Reuses ERRComposition + the witness systems SB (full Roles) / SDisc (discrete Roles).

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.     (* ERRMorphism, err_map, err_pres, err_comp, err_id, err_morph_eq *)
From ToS Require Import foundation.ERRDynamics.          (* SB : full-Roles bool system *)
From ToS Require Import foundation.ERRDynamicsArrow.     (* flip : negb on SB *)
From ToS Require Import foundation.ERRQuotient.          (* SDisc : discrete (eq) bool system *)

(* Record projections lose their implicit {L} across import — re-add. *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  Roles of a system as an equivalence (the Rules gate for the 2-tier)    *)
(* ===================================================================== *)

(** A system's Roles form an equivalence relation on its Elements. *)
Definition roles_equiv {L} (S : FunctionalSystem L) : Prop :=
  (forall x, get_Roles S x x) /\
  (forall x y, get_Roles S x y -> get_Roles S y x) /\
  (forall x y z, get_Roles S x y -> get_Roles S y z -> get_Roles S x z).

(** ★ The RULES supply the gate: an equivalence-Constitution makes the Roles an equivalence,
    hence the 2-cells composable.  (This is where "Rules > Roles" becomes 2-coherence.) *)
Lemma equiv_system_roles_equiv {L} (S : FunctionalSystem L) :
  fs_constitution S = EquivalenceConstitution -> roles_equiv S.
Proof.
  intro He. unfold roles_equiv, get_Roles.
  pose proof (fs_functional S) as Hf.
  rewrite He in Hf. unfold EquivalenceConstitution in Hf. exact Hf.
Qed.

(* ===================================================================== *)
(*  The 2-cell: a Roles-homotopy between parallel 1-morphisms              *)
(* ===================================================================== *)

(** A 2-cell  f ⟹ g : the two Element-maps are Roles-connected at every element.
    Reading: f and g are indistinguishable AT THE ROLES TIER — the system cannot tell them
    apart by its own relations (the categorical form of intensional / P3 identity). *)
Definition Roles2 {L} {S1 S2 : FunctionalSystem L} (f g : ERRMorphism S1 S2) : Prop :=
  forall x, get_Roles S2 (err_map f x) (err_map g x).

(** Identity 2-cell  (reflexivity of the Roles-homotopy). *)
Lemma Roles2_refl {L} {S1 S2 : FunctionalSystem L} (He : roles_equiv S2)
  (f : ERRMorphism S1 S2) : Roles2 f f.
Proof. intro x. exact (proj1 He (err_map f x)). Qed.

(** 2-cells are invertible (the hom-setoid is a groupoid):  symmetry. *)
Lemma Roles2_sym {L} {S1 S2 : FunctionalSystem L} (He : roles_equiv S2)
  {f g : ERRMorphism S1 S2} : Roles2 f g -> Roles2 g f.
Proof. intros Hfg x. exact (proj1 (proj2 He) (err_map f x) (err_map g x) (Hfg x)). Qed.

(** VERTICAL composition of 2-cells  (α : f⟹g, β : g⟹h  ⟹  f⟹h). *)
Lemma Roles2_trans {L} {S1 S2 : FunctionalSystem L} (He : roles_equiv S2)
  {f g h : ERRMorphism S1 S2} : Roles2 f g -> Roles2 g h -> Roles2 f h.
Proof.
  intros Hfg Hgh x.
  exact (proj2 (proj2 He) (err_map f x) (err_map g x) (err_map h x) (Hfg x) (Hgh x)).
Qed.

(** ★ The Element tier refines INTO the Roles tier: pointwise EQUALITY of maps (the finest,
    Element-level sameness) is a special case of Roles2 (the coarser, Roles-level sameness).
    So the 2-category carries two graded notions of "same map", Elements ⊂ Roles. *)
Lemma morph_eq_refines_Roles2 {L} {S1 S2 : FunctionalSystem L} (He : roles_equiv S2)
  {f g : ERRMorphism S1 S2} : err_morph_eq f g -> Roles2 f g.
Proof. intros Heq x. rewrite (Heq x). exact (proj1 He (err_map g x)). Qed.

(* ===================================================================== *)
(*  Whiskering — 1-morphisms act 2-functorially on 2-cells (no gate)       *)
(* ===================================================================== *)

(** POST-whiskering: composing a 2-cell with a 1-morphism on the OUTSIDE.
    This is exactly err_pres re-read: a 1-morphism PRESERVES 2-cells (2-functoriality).
    No equivalence hypothesis needed — pure Roles-preservation. *)
Lemma Roles2_whisker_post {L} {S1 S2 S3 : FunctionalSystem L}
  (h : ERRMorphism S2 S3) {f g : ERRMorphism S1 S2} :
  Roles2 f g -> Roles2 (err_comp f h) (err_comp g h).
Proof. intros Hfg x. exact (err_pres h (err_map f x) (err_map g x) (Hfg x)). Qed.

(** PRE-whiskering: composing on the INSIDE = reindexing the 2-cell.  No hypothesis. *)
Lemma Roles2_whisker_pre {L} {S1 S2 S3 : FunctionalSystem L}
  (k : ERRMorphism S1 S2) {f g : ERRMorphism S2 S3} :
  Roles2 f g -> Roles2 (err_comp k f) (err_comp k g).
Proof. intros Hfg x. exact (Hfg (err_map k x)). Qed.

(** ★★ HORIZONTAL composition = composition is a CONGRUENCE for Roles2 (the enrichment is
    respected): if f ⟹ g and f' ⟹ g' then (f∘f') ⟹ (g∘g').  Built from the two whiskerings
    and vertical composition (needs the equivalence gate on the final target S3). *)
Lemma Roles2_hcomp {L} {S1 S2 S3 : FunctionalSystem L} (He : roles_equiv S3)
  {f g : ERRMorphism S1 S2} {f' g' : ERRMorphism S2 S3} :
  Roles2 f g -> Roles2 f' g' -> Roles2 (err_comp f f') (err_comp g g').
Proof.
  intros Hfg Hf'g'.
  exact (Roles2_trans He (Roles2_whisker_post f' Hfg) (Roles2_whisker_pre g Hf'g')).
Qed.

(* ===================================================================== *)
(*  The 2-structure is RULES-GRADED: trivial on discrete, real on full     *)
(* ===================================================================== *)

(** On a DISCRETE system (Roles = equality) the 2-structure COLLAPSES to plain equality —
    no genuine second dimension.  (Elements-tier Rules ⟹ thin-to-the-point 2-cells.) *)
Lemma Roles2_on_discrete_iff_eq (S1 : FunctionalSystem L2) (f g : ERRMorphism S1 SDisc) :
  Roles2 f g <-> err_morph_eq f g.
Proof. split; intro H; exact H. Qed.

(** On a FULL-Roles system the 2-structure is STRICTLY COARSER than equality: there are
    genuinely distinct maps (id vs flip) joined by a 2-cell — a real second dimension.
    (Roles-tier content in the Rules ⟹ nontrivial 2-cells.) *)
Lemma Roles2_full_strictly_coarser :
  Roles2 (err_id SB) flip /\ ~ err_morph_eq (err_id SB) flip.
Proof.
  split.
  - intro x. exact I.
  - intro H. pose proof (H true) as Ht. cbn in Ht. discriminate Ht.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE SECOND DIMENSION OF THE E/R/R CATEGORY.
      The Roles tier IS the 2-cell structure:
      (1) on every hom-set, Roles2 is an EQUIVALENCE (id / sym / vertical composition) —
          a setoid-enrichment, gated by the target's Rules being an equivalence;
      (2) composition is a CONGRUENCE for it (horizontal composition / whiskering) — the
          1-morphisms are 2-functorial;
      (3) the 2-structure is RULES-GRADED: it collapses to equality on discrete systems and
          is strictly coarser (a real second dimension) on full ones.
    Rank asymmetry Rules>Roles>Elements, now read as category DIMENSION:
      Elements = carriers, 1-morphisms = Element-maps, Roles = 2-cells, Rules = the 2-coherence
      gate.  Honestly THIN (Prop-valued 2-cells): no higher coherence data; the strict
      equational 2-laws would need proof-irrelevance — here the congruence form is proved. *)
Theorem err_2category :
  (forall (L : Level) (S1 S2 : FunctionalSystem L), roles_equiv S2 ->
     (forall f : ERRMorphism S1 S2, Roles2 f f)
     /\ (forall f g : ERRMorphism S1 S2, Roles2 f g -> Roles2 g f)
     /\ (forall f g h : ERRMorphism S1 S2, Roles2 f g -> Roles2 g h -> Roles2 f h))
  /\ (forall (L : Level) (S1 S2 S3 : FunctionalSystem L), roles_equiv S3 ->
        forall (f g : ERRMorphism S1 S2) (f' g' : ERRMorphism S2 S3),
          Roles2 f g -> Roles2 f' g' -> Roles2 (err_comp f f') (err_comp g g'))
  /\ (forall (S1 : FunctionalSystem L2) (f g : ERRMorphism S1 SDisc),
        Roles2 f g <-> err_morph_eq f g)
  /\ (Roles2 (err_id SB) flip /\ ~ err_morph_eq (err_id SB) flip).
Proof.
  split; [ | split; [ | split ] ].
  - intros L S1 S2 He. split; [ | split ].
    + intro f. exact (Roles2_refl He f).
    + intros f g H. exact (Roles2_sym He H).
    + intros f g h H1 H2. exact (Roles2_trans He H1 H2).
  - intros L S1 S2 S3 He f g f' g' Hfg Hf'g'. exact (Roles2_hcomp He Hfg Hf'g').
  - exact Roles2_on_discrete_iff_eq.
  - exact Roles2_full_strictly_coarser.
Qed.

Print Assumptions err_2category.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The Roles tier as the 2-cell structure of the system category.  roles_   *)
(*  equiv + equiv_system_roles_equiv (Rules gate the 2-coherence).  Roles2    *)
(*  (the 2-cell = pointwise Roles-connection of two parallel maps).  Roles2_  *)
(*  refl/sym/trans (id + setoid-enrichment of each hom-set).  morph_eq_       *)
(*  refines_Roles2 (Elements ⊂ Roles sameness).  Roles2_whisker_post/_pre    *)
(*  (1-morphisms 2-functorial, no gate) + Roles2_hcomp (composition is a      *)
(*  congruence).  Roles2_on_discrete_iff_eq (trivial on discrete) + Roles2_   *)
(*  full_strictly_coarser (real on full) = the Rules-graded 2-structure.      *)
(*  Capstone err_2category.  HONEST: locally THIN (Prop 2-cells) — congruence *)
(*  form proved, strict equational 2-laws would need proof-irrelevance.       *)
(* ========================================================================= *)
