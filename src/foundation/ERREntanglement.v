(** * ERREntanglement.v — physics probe of the category of systems: ENTANGLEMENT = a composite system
      that is NOT a categorical product of its parts.

    Кирпич 2 (ERRComposition.v) built the PRODUCT of systems: Elements = pairs, Roles = prod_rel
    (componentwise), Rules = the shared constitution, with genuine projections.  That product is the
    SEPARABLE composite — the whole's correlations are exactly the product of the parts'.  This file
    asks the physics-facing question the category opens: is EVERY composite a product?  No — and the
    obstruction is a Roles-tier fact, exactly the Кирпич-1 asymmetry seen from the composite side.

      ★ separable R       — a Roles relation on D1*D2 factors as prod_rel R1 R2 (the categorical
                            product / the separable case).
      ★ swap_closed R     — the structural fingerprint of a product: components recombine freely
                            (a,b)~(c,d) & (a',b')~(c',d') => (a,b')~(c,d').
      ★ separable_swap_closed — every separable (product) composite is swap-closed.
      ★ parity_roles      — the XOR-parity correlation on bool*bool: the algebraic CORE of the
                            Bell/GHZ family (the joint parity is the invariant).  It is an equivalence
                            (parity_equiv), hence a bona fide FunctionalSystem (parity_system) — and
                            it VIOLATES swap-closure (parity_not_swap_closed), so it is NOT separable
                            (parity_not_separable): the entangled composite is not a categorical
                            product of its parts.
      ★ prod_rel_separable — conversely, every prod_rel IS separable: separable <=> is-a-product, so
                            the dichotomy is clean (separable = product, entangled = non-product).

    This is the genuine, machine-checked content of "entanglement = categorical non-separability"
    (the categorical-QM framing: separable states = product states), instantiated 0-axiom on bool.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) a composite over D1*D2 is SEPARABLE iff its Roles factor as prod_rel R1 R2 (the categorical
          product of Кирпич 2);
      (2) separable Roles are SWAP-CLOSED — components recombine freely (the product fingerprint);
      (3) the parity correlation (Bell/GHZ core) VIOLATES swap-closure, so it is NOT separable — the
          entangled composite is not a categorical product of its parts.
    Roles (L4): separable = the factorization predicate; swap_closed = the product fingerprint;
      par/parity_roles = the correlation; parity_system = the entangled system as an actual
      FunctionalSystem; prod_rel/projections (Кирпич 2) = the separable (product) case.
    Elements (L1+P4): the carriers bool, bool*bool; the relations eq (separable witness) vs
      parity_roles (entangled); EquivalenceConstitution (parity_roles IS an equivalence — a genuine
      system, not a product).
    P4 diagnostic (could it be otherwise, under the SAME rules?):
      a composite's Roles are NOT forced to be prod_rel.  Under the same Elements (bool*bool) and the
      same Rules tier (an equivalence Constitution), the Roles can be EITHER a product (separable) OR
      not (parity_roles) — and parity is concretely a non-product.  So "is it a product?" is a genuine
      question UNDERDETERMINED by Elements and Rules, decided at the Roles tier: entanglement is a
      Roles-tier fact — exactly the Кирпич-1 asymmetry from the composite side (the whole's Roles can
      EXCEED the product of the parts' Roles).
    Honesty wall:
      this is QUALITATIVE / STRUCTURAL non-separability (Roles = a Prop-relation), NOT a quantitative
      entanglement measure (no amplitudes, no concurrence/entropy, no Tsirelson number).  parity_roles
      is the algebraic CORE of the Bell/GHZ parity correlations (a constraint with no componentwise /
      factorized explanation); the file proves the structural fact (no product factorization), not
      CHSH numerics.  "entanglement = non-product" is the categorical-QM framing instantiated 0-axiom
      on bool; it UNIFIES the project's existing GHZ/Bell as instances of "the composite is not a
      categorical product", it does not derive new physics.  A quantitative layer would need an
      enriched (e.g. Q-amplitude) Roles tier — not attempted.  0 axioms (classic sits unused in
      Core_ERR's context — Print Assumptions).

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.  (* prod_rel, fs_product (the separable case) *)
From Stdlib Require Import Bool.

(* Restore the section-local implicit {L} on the record projections (see ERRRankAsymmetry.v). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  SEPARABLE = a composite that factors as a product                     *)
(* ===================================================================== *)

(** A Roles relation on a product carrier is SEPARABLE if it factors as prod_rel of marginals — i.e.
    it is (the Roles of) a categorical PRODUCT of two systems. *)
Definition separable {D1 D2 : Type} (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  exists (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop),
    forall p q, R p q <-> prod_rel R1 R2 p q.

(** The structural fingerprint of a product: components recombine freely. *)
Definition swap_closed {D1 D2 : Type} (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  forall (a c a' c' : D1) (b d b' d' : D2),
    R (a, b) (c, d) -> R (a', b') (c', d') -> R (a, b') (c, d').

(** ★★ Every separable (product) composite is SWAP-CLOSED: in a product, what holds of the first
    components and what holds of the second components can be combined independently. *)
Lemma separable_swap_closed : forall {D1 D2 : Type} (R : (D1 * D2) -> (D1 * D2) -> Prop),
  separable R -> swap_closed R.
Proof.
  intros D1 D2 R [R1 [R2 Hiff]] a c a' c' b d b' d' H1 H2.
  destruct (Hiff (a, b) (c, d)) as [F1 _].
  destruct (Hiff (a', b') (c', d')) as [F2 _].
  destruct (Hiff (a, b') (c, d')) as [_ B3].
  specialize (F1 H1). specialize (F2 H2).
  destruct F1 as [Hac _]. destruct F2 as [_ Hb'd'].
  apply B3. split; [ exact Hac | exact Hb'd' ].
Qed.

(** ★ Conversely, every prod_rel IS separable — so separable <=> is-a-categorical-product. *)
Lemma prod_rel_separable : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop),
  separable (prod_rel R1 R2).
Proof.
  intros D1 D2 R1 R2. exists R1, R2. intros p q. split; intro H; exact H.
Qed.

(* ===================================================================== *)
(*  THE ENTANGLED WITNESS — the parity (Bell/GHZ) correlation             *)
(* ===================================================================== *)

(** The joint parity of a two-component state. *)
Definition par (p : bool * bool) : bool := xorb (fst p) (snd p).

(** The PARITY correlation: two composite states relate iff they share the joint parity.  This is the
    algebraic core of the Bell/GHZ family — the invariant a non-separable state preserves. *)
Definition parity_roles (p q : bool * bool) : Prop := par p = par q.

(** ★ parity_roles is an equivalence (it is equality pulled back through par) — so it is a genuine
    Roles relation under EquivalenceConstitution. *)
Lemma parity_equiv : EquivalenceConstitution (bool * bool)%type parity_roles.
Proof.
  unfold EquivalenceConstitution, parity_roles. split; [ | split ].
  - intro p. reflexivity.
  - intros p q H. symmetry. exact H.
  - intros p q r Hpq Hqr. transitivity (par q); assumption.
Qed.

(** ★★ The parity correlation VIOLATES swap-closure: (false,false)~(true,true) (both parity 0) and
    (false,true)~(false,true) (both parity 1), yet (false,true)~(true,true) FAILS (parity 1 vs 0). *)
Lemma parity_not_swap_closed : ~ swap_closed parity_roles.
Proof.
  unfold swap_closed. intro H.
  assert (P1 : parity_roles (false, false) (true, true)) by reflexivity.
  assert (P2 : parity_roles (false, true) (false, true)) by reflexivity.
  pose proof (H false true false false false true true true P1 P2) as Bad.
  unfold parity_roles, par in Bad. cbn in Bad. discriminate Bad.
Qed.

(** ★★★ The parity composite is NOT SEPARABLE: it is not the categorical product of any two systems
    on bool — entanglement is a structural non-product. *)
Lemma parity_not_separable : ~ separable parity_roles.
Proof.
  intro Hsep. apply parity_not_swap_closed. apply separable_swap_closed. exact Hsep.
Qed.

(** ★ Concretely, the parity composite relates two states that the canonical product-system
    (equality on both components) does NOT relate — a witnessed separability failure. *)
Lemma parity_differs_from_product :
  exists p q : bool * bool, parity_roles p q /\ ~ prod_rel (@eq bool) (@eq bool) p q.
Proof.
  exists (false, false), (true, true). split.
  - reflexivity.
  - intros [Ha _]. discriminate Ha.
Qed.

(* ===================================================================== *)
(*  THE ENTANGLED SYSTEM as an actual FunctionalSystem                     *)
(* ===================================================================== *)

(** ★ The parity correlation as a genuine FunctionalSystem: Elements = bool*bool, Roles =
    parity_roles, Rules = EquivalenceConstitution (a perfectly valid system — that is NOT a product). *)
Definition parity_system : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution;
            fs_domain := (bool * bool)%type;
            fs_relations := parity_roles;
            fs_functional := parity_equiv;
            fs_element_level := fun _ => L1;
            fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** ★ Its Roles are the parity correlation. *)
Lemma parity_system_roles : get_Roles parity_system = parity_roles.
Proof. reflexivity. Qed.

(** ★★ Its Roles are entangled — not a categorical product. *)
Lemma parity_system_entangled : ~ separable (get_Roles parity_system).
Proof. exact parity_not_separable. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ ENTANGLEMENT = a composite system that is NOT a categorical product:
      (product fingerprint)  every separable composite is swap-closed;
      (separable = product)  every prod_rel is separable;
      (entanglement)         the parity (Bell/GHZ core) correlation is NOT separable;
      (genuine system)       yet it satisfies its Rules (an equivalence) — a bona fide FunctionalSystem;
      (it is the system's)   its Roles ARE the parity correlation.
    So the whole's Roles can EXCEED the product of the parts' Roles — the Кирпич-1 asymmetry from the
    composite side, machine-checked 0-axiom.  Categorical-QM framing instantiated: separable = product,
    entangled = non-product. *)
Theorem err_entanglement :
  (forall (D1 D2 : Type) (R : (D1 * D2) -> (D1 * D2) -> Prop), separable R -> swap_closed R)
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop), separable (prod_rel R1 R2))
  /\ ~ separable parity_roles
  /\ get_Rules parity_system
  /\ get_Roles parity_system = parity_roles.
Proof.
  split; [ exact (@separable_swap_closed) | ].
  split; [ exact (@prod_rel_separable) | ].
  split; [ exact parity_not_separable | ].
  split; [ exact parity_equiv | exact parity_system_roles ].
Qed.

Print Assumptions parity_not_separable.
Print Assumptions err_entanglement.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Physics probe of the category of systems: ENTANGLEMENT = a composite      *)
(*  that is NOT a categorical product.  separable (factors as prod_rel) /      *)
(*  swap_closed (product fingerprint); separable_swap_closed (product =>       *)
(*  swap-closed); prod_rel_separable (product => separable, so separable <=>   *)
(*  is-a-product).  The parity (Bell/GHZ core) correlation parity_roles is an  *)
(*  equivalence (parity_equiv) — a genuine FunctionalSystem (parity_system) —  *)
(*  yet VIOLATES swap-closure (parity_not_swap_closed), hence is NOT separable *)
(*  (parity_not_separable): the entangled composite is not a categorical       *)
(*  product (parity_differs_from_product witnesses it concretely).  Capstone   *)
(*  err_entanglement.  HONEST: structural (Prop-relation) non-separability,    *)
(*  NOT a quantitative measure (no amplitudes/Tsirelson); unifies existing     *)
(*  GHZ/Bell as "composite not a product", derives no new physics; quantitative*)
(*  layer needs an enriched Roles tier (not attempted).  Roles-tier fact =     *)
(*  Кирпич-1 asymmetry from the composite side.                               *)
(* ========================================================================= *)
