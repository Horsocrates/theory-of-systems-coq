(** * ERRComposition.v — Кирпич 2 развития ядра Теории Систем: the E/R/R COMPOSITION of systems —
      morphisms (Elements+Roles preserved, Rules as the frame) + product (the whole's triad from the
      parts' triads), with Rules GATING composability.

    Кирпич 1 (ERRRankAsymmetry.v) proved the rank asymmetry Rules > Roles > Elements on the canonical
    E/R/R object FunctionalSystem.  This brick builds the COMPOSITION the user asked for ("E/R/R
    composition of any system"), and the asymmetry from Кирпич 1 BITES exactly where expected.

    Two halves:

    (A) E/R/R-MORPHISM — a structure-preserving map between FunctionalSystems at the same level.
        A morphism acts on the LOWER two tiers: a map on Elements that PRESERVES Roles
        (ERRMorphism: err_map on get_Elements, err_pres on get_Roles).  Rules are NOT transported —
        a Constitution is a property of the whole, not carried pointwise; Rules are the ambient frame
        (the "type" of the category).  This is the Кирпич-1 asymmetry at the morphism level.  The
        morphisms form a CATEGORY: identity (err_id), composition (err_comp), and the laws
        (err_id_left/right, err_comp_assoc) — all by reflexivity, since function composition is
        definitionally unital and associative.

    (B) PRODUCT — the whole built from two parts.  Elements compose as the product type; Roles as the
        product relation prod_rel; and the triad of the whole is the composition of the triads of the
        parts (fs_product_elements/roles/rules).  But the RULES compose ONLY when the constitution is
        product-closed:
          - equiv_product_closed : EquivalenceConstitution composes (product of equivalences);
          - trivial_product_closed : TrivialConstitution composes;
          - connex_not_product_closed : ConnexConstitution does NOT (a concrete counterexample) —
            so Rules genuinely GATE composability (not every Rule survives a product).  This is the
            Кирпич-1 asymmetry: Rules are the hard tier.
        The product carries genuine PROJECTIONS fst/snd as E/R/R-morphisms (fs_proj1, fs_proj2).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) an E/R/R-morphism is a map on Elements that PRESERVES Roles; Rules are the frame, not
          transported — morphisms form a category;
      (2) a product composes Elements (pairs) and Roles (prod_rel) generically;
      (3) the product's Rules compose ONLY if the constitution is product-closed — Rules gate
          composability (equivalence yes, connex no);
      (4) the projections fst/snd are genuine E/R/R-morphisms.
    Roles (L4): err_map = the Elements map; err_pres = Roles preservation; fs_product = the assembly;
      product_closed = the condition on Rules; fs_proj1/fs_proj2 = projection morphisms.
    Elements (L1+P4): the systems S1, S2; the pairs; prod_rel; the constitutions
      Equivalence/Trivial/Connex.
    P4 diagnostic (could it be otherwise?):
      Composition is NOT free.  Elements and Roles compose generically; Rules compose only when
      product-closed (the connex witness shows some Rules fail).  This is exactly the Кирпич-1
      asymmetry — Rules are the hard tier; a morphism acts on the lower two, Rules are the frame.
    Honesty wall:
      a morphism does NOT transport Rules (a Constitution is a property of the whole, not pointwise) —
      this is honest and IS the E/R/R structure.  The product is given for systems of the SAME
      constitution (the same "kind") and demonstrated for equivalence; the general arbitrary-
      constitution case is open (needs product_closed).  The product's UNIVERSAL PROPERTY
      (uniqueness of the mediating morphism) is NOT proved — projections are given (genuine product
      structure), not completeness (that is a later brick).  Built on FunctionalSystem (canonical
      E/R/R object).  0 axioms (classic sits in Core_ERR's context, untouched — Print Assumptions).

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.

(* Restore the section-local implicit {L} on the record projections (see ERRRankAsymmetry.v). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  PART A — E/R/R-MORPHISM and the category of FunctionalSystems          *)
(* ===================================================================== *)

(** An E/R/R-morphism: a map on Elements that PRESERVES Roles.  Rules are the ambient frame, not
    transported — the morphism lives on the lower two tiers (the Кирпич-1 asymmetry). *)
Record ERRMorphism {L : Level} (S1 S2 : FunctionalSystem L) : Type := mkERRMorphism {
  err_map  : get_Elements S1 -> get_Elements S2;
  err_pres : forall x y, get_Roles S1 x y -> get_Roles S2 (err_map x) (err_map y);
}.
Arguments err_map {L S1 S2}.
Arguments err_pres {L S1 S2}.

(** Identity morphism. *)
Definition err_id {L} (S : FunctionalSystem L) : ERRMorphism S S :=
  {| err_map := fun x => x; err_pres := fun x y H => H |}.

(** Composition of morphisms (preservation composes). *)
Definition err_comp {L} {S1 S2 S3 : FunctionalSystem L}
  (m12 : ERRMorphism S1 S2) (m23 : ERRMorphism S2 S3) : ERRMorphism S1 S3 :=
  {| err_map := fun x => err_map m23 (err_map m12 x);
     err_pres := fun x y H => err_pres m23 (err_map m12 x) (err_map m12 y) (err_pres m12 x y H) |}.

(** Extensional equality of morphisms (on the Elements map; err_pres is a proof). *)
Definition err_morph_eq {L} {S1 S2 : FunctionalSystem L} (m1 m2 : ERRMorphism S1 S2) : Prop :=
  forall x, err_map m1 x = err_map m2 x.

(** ★ Category law: identity is a left unit. *)
Lemma err_id_left : forall {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2),
  err_morph_eq (err_comp (err_id S1) m) m.
Proof. intros L S1 S2 m x. reflexivity. Qed.

(** ★ Category law: identity is a right unit. *)
Lemma err_id_right : forall {L} {S1 S2 : FunctionalSystem L} (m : ERRMorphism S1 S2),
  err_morph_eq (err_comp m (err_id S2)) m.
Proof. intros L S1 S2 m x. reflexivity. Qed.

(** ★ Category law: composition is associative. *)
Lemma err_comp_assoc :
  forall {L} {S1 S2 S3 S4 : FunctionalSystem L}
         (m1 : ERRMorphism S1 S2) (m2 : ERRMorphism S2 S3) (m3 : ERRMorphism S3 S4),
    err_morph_eq (err_comp (err_comp m1 m2) m3) (err_comp m1 (err_comp m2 m3)).
Proof. intros L S1 S2 S3 S4 m1 m2 m3 x. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B — PRODUCT: the whole's triad from the parts' triads            *)
(* ===================================================================== *)

(** The product Roles: a pair relates iff both components relate. *)
Definition prod_rel {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  : (D1 * D2) -> (D1 * D2) -> Prop :=
  fun p q => R1 (fst p) (fst q) /\ R2 (snd p) (snd q).

(** A constitution is PRODUCT-CLOSED if it survives the product relation — the condition for Rules
    to compose. *)
Definition product_closed (C : Constitution) : Prop :=
  forall (D1 : Type) (R1 : D1 -> D1 -> Prop) (D2 : Type) (R2 : D2 -> D2 -> Prop),
    C D1 R1 -> C D2 R2 -> C (D1 * D2)%type (prod_rel R1 R2).

(** ★ EquivalenceConstitution is product-closed: the product of two equivalences is an equivalence. *)
Lemma equiv_product_closed : product_closed EquivalenceConstitution.
Proof.
  intros D1 R1 D2 R2 [Hr1 [Hs1 Ht1]] [Hr2 [Hs2 Ht2]].
  split; [ | split ].
  - intro p. split; [ apply Hr1 | apply Hr2 ].
  - intros p q [Ha Hb]. split; [ apply Hs1; exact Ha | apply Hs2; exact Hb ].
  - intros p q r [Hpqa Hpqb] [Hqra Hqrb]. split.
    + apply Ht1 with (fst q); assumption.
    + apply Ht2 with (snd q); assumption.
Qed.

(** ★ TrivialConstitution is product-closed (it accepts everything). *)
Lemma trivial_product_closed : product_closed TrivialConstitution.
Proof. intros D1 R1 D2 R2 _ _. exact I. Qed.

(** A connex (total) constitution: every two elements are comparable. *)
Definition ConnexConstitution : Constitution :=
  fun D R => forall x y, R x y \/ R y x.

(** A concrete total relation on bool. *)
Definition tot (x y : bool) : Prop := x = y \/ x = false.

Lemma tot_connex : ConnexConstitution bool tot.
Proof.
  intros x y. unfold tot. destruct x.
  - destruct y.
    + left; left; reflexivity.
    + right; right; reflexivity.
  - left; right; reflexivity.
Qed.

(** ★★ ConnexConstitution is NOT product-closed: totality fails under the product — (true,false) and
    (false,true) become incomparable.  So Rules genuinely GATE composability (the Кирпич-1
    asymmetry: not every Rule survives a product). *)
Lemma connex_not_product_closed : ~ product_closed ConnexConstitution.
Proof.
  intro Hpc.
  pose proof (Hpc bool tot bool tot tot_connex tot_connex) as Hc.
  specialize (Hc (true, false) (false, true)).
  destruct Hc as [[Ha Hb] | [Ha Hb]].
  - destruct Ha as [E | E]; discriminate.
  - destruct Hb as [E | E]; discriminate.
Qed.

(** ★★ THE PRODUCT of two equivalence-systems: Elements = pairs, Roles = prod_rel, Rules =
    EquivalenceConstitution (preserved via equiv_product_closed). *)
Definition fs_product {L} (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution) : FunctionalSystem L.
Proof.
  refine {| fs_constitution := EquivalenceConstitution;
            fs_domain := (get_Elements S1 * get_Elements S2)%type;
            fs_relations := prod_rel (get_Roles S1) (get_Roles S2);
            fs_functional := _;
            fs_element_level := fun p => fs_element_level S1 (fst p);
            fs_level_valid := fun p => fs_level_valid S1 (fst p) |}.
  apply equiv_product_closed.
  - rewrite <- H1. exact (fs_functional S1).
  - rewrite <- H2. exact (fs_functional S2).
Defined.

(** ★ ELEMENTS compose: the whole's Elements = the product of the parts' Elements. *)
Lemma fs_product_elements :
  forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
    get_Elements (fs_product S1 S2 H1 H2) = (get_Elements S1 * get_Elements S2)%type.
Proof. intros. reflexivity. Qed.

(** ★ ROLES compose: the whole's Roles = the product relation of the parts' Roles. *)
Lemma fs_product_roles :
  forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
    get_Roles (fs_product S1 S2 H1 H2) = prod_rel (get_Roles S1) (get_Roles S2).
Proof. intros. reflexivity. Qed.

(** ★ RULES compose (here): the whole's Rules = EquivalenceConstitution. *)
Lemma fs_product_rules :
  forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
    fs_constitution (fs_product S1 S2 H1 H2) = EquivalenceConstitution.
Proof. intros. reflexivity. Qed.

(** ★ The first projection is a genuine E/R/R-morphism (fst preserves prod_rel into R1). *)
Definition fs_proj1 {L} (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution)
  : ERRMorphism (fs_product S1 S2 H1 H2) S1.
Proof.
  refine (@mkERRMorphism L (fs_product S1 S2 H1 H2) S1 (fun p => fst p) _).
  intros x y H. exact (proj1 H).
Defined.

(** ★ The second projection is a genuine E/R/R-morphism. *)
Definition fs_proj2 {L} (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution)
  : ERRMorphism (fs_product S1 S2 H1 H2) S2.
Proof.
  refine (@mkERRMorphism L (fs_product S1 S2 H1 H2) S2 (fun p => snd p) _).
  intros x y H. exact (proj2 H).
Defined.

(* ===================================================================== *)
(*  CAPSTONE — E/R/R composition                                          *)
(* ===================================================================== *)

(** ★★★ E/R/R COMPOSITION of systems:
      (category)  morphisms = Elements-maps preserving Roles, with identity a unit and composition
                  associative (Rules are the frame, not transported);
      (product)   the whole's triad is the composition of the parts' triads (Elements = pairs,
                  Roles = prod_rel, Rules = the shared constitution);
      (Rules gate) the Rules compose iff product-closed — equivalence YES, connex NO.
    Composition acts freely on Elements and Roles; Rules gate it — the Кирпич-1 asymmetry, now at
    the composition level. *)
Theorem err_composition_capstone :
  (forall (L : Level) (S1 S2 : FunctionalSystem L) (m : ERRMorphism S1 S2),
     err_morph_eq (err_comp (err_id S1) m) m)
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L)
            (H1 : fs_constitution S1 = EquivalenceConstitution)
            (H2 : fs_constitution S2 = EquivalenceConstitution),
        get_Elements (fs_product S1 S2 H1 H2) = (get_Elements S1 * get_Elements S2)%type
        /\ get_Roles (fs_product S1 S2 H1 H2) = prod_rel (get_Roles S1) (get_Roles S2)
        /\ fs_constitution (fs_product S1 S2 H1 H2) = EquivalenceConstitution)
  /\ product_closed EquivalenceConstitution
  /\ ~ product_closed ConnexConstitution.
Proof.
  split; [ intros L S1 S2 m x; reflexivity | ].
  split; [ intros L S1 S2 H1 H2; split; [ reflexivity | split; reflexivity ] | ].
  split; [ exact equiv_product_closed | exact connex_not_product_closed ].
Qed.

Print Assumptions err_composition_capstone.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Кирпич 2: the E/R/R COMPOSITION of FunctionalSystems.  (A) ERRMorphism =  *)
(*  Elements-map preserving Roles (Rules = the frame); category laws          *)
(*  err_id_left/right/comp_assoc (reflexivity).  (B) product: Elements = pairs,*)
(*  Roles = prod_rel, Rules = shared constitution (fs_product_elements/roles/  *)
(*  rules); Rules GATE composability — product_closed: equiv YES               *)
(*  (equiv_product_closed), trivial YES, connex NO (connex_not_product_closed);*)
(*  genuine projections fs_proj1/fs_proj2 as morphisms.  Capstone               *)
(*  err_composition_capstone.  HONEST: morphisms do not transport Rules        *)
(*  (Constitution is whole-level); product shown for shared-constitution       *)
(*  (equivalence), general case needs product_closed; universal property       *)
(*  (uniqueness of mediator) NOT proved — next brick.  Ties Кирпич 1: Rules    *)
(*  are the hard tier; composition free on E & R, gated on Rules.             *)
(* ========================================================================= *)
