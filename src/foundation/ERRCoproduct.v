(** * ERRCoproduct.v — thread ③: the COPRODUCT (sum) of systems — the categorical DUAL of the product
      (ERRComposition.fs_product).  Where the product COMBINES parts (an element is a pair, Roles
      relate jointly), the coproduct DECOMPOSES into alternatives (an element is EITHER part, parts
      never relate across).

    Dual, field-for-field, to fs_product:

      ★ sum_rel R1 R2 — a disjoint-union relation: two elements relate iff both are in the SAME summand
        and relate there; cross-summand pairs never relate.
      ★ fs_coproduct S1 S2 — Elements = the disjoint union, Roles = sum_rel, Rules = the shared
        (equivalence) constitution (preserved via equiv_coproduct_closed, dual to equiv_product_closed).
      ★ INJECTIONS fs_inl / fs_inr (dual to the projections fs_proj1 / fs_proj2).
      ★ UNIVERSAL PROPERTY (dual to ERRProductUniversal): a unique copairing fs_copair [g1, g2] with
        copair ∘ inl = g1, copair ∘ inr = g2 (coproduct_inl_compute / _inr_compute,
        coproduct_mediator_unique).
      ★ DECOMPOSITION: every element is in exactly one summand (coproduct_cases, disjoint), and the two
        parts never relate (coproduct_no_cross_roles) — the sum is maximally decomposable, the opposite
        extreme to entanglement (a product that does not factor, ERREntanglement).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the COPRODUCT composes Elements (disjoint union) and Roles (sum_rel) generically; Rules compose
      when COPRODUCT-CLOSED (equivalence yes); the injections + a UNIQUE copairing give the dual
      universal property; the parts stay SEPARATE (no cross-Roles) — the sum DECOMPOSES.
    Roles (L4): sum_rel; fs_coproduct; fs_inl / fs_inr (injections); fs_copair (the mediator);
      coproduct_no_cross_roles (separation of parts).
    Elements (L1+P4): the two systems S1, S2; the disjoint union; the constitutions.
    P4 diagnostic (could it be otherwise?):
      an element of the sum is EITHER from S1 OR from S2 (coproduct_cases), never both (disjoint), and
      the parts never relate across — the sum is a genuine alternative/decomposition, the DUAL of the
      product's combination.  Both exist; which one assembles the whole is the constructor's choice.
    Honesty wall:
      coproduct given for the shared (equivalence) constitution, exactly as fs_product was; the
      universal property is at the Elements-map level (dual to ERRProductUniversal); injections given;
      the sum is the categorical coproduct in the SAME category (ERRMorphism) as the product.  Reuses
      ERRComposition.  0 axioms.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, mkERRMorphism, err_map, err_morph_eq *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE SUM RELATION and its constitution-closure                         *)
(* ===================================================================== *)

(** The coproduct Roles: relate iff both in the same summand and relate there. *)
Definition sum_rel {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop)
  : (D1 + D2) -> (D1 + D2) -> Prop :=
  fun p q => match p, q with
             | inl a, inl a' => R1 a a'
             | inr b, inr b' => R2 b b'
             | _, _ => False
             end.

(** A constitution is COPRODUCT-CLOSED if it survives the sum relation (dual to product_closed). *)
Definition coproduct_closed (C : Constitution) : Prop :=
  forall (D1 : Type) (R1 : D1 -> D1 -> Prop) (D2 : Type) (R2 : D2 -> D2 -> Prop),
    C D1 R1 -> C D2 R2 -> C (D1 + D2)%type (sum_rel R1 R2).

(** ★ EquivalenceConstitution is coproduct-closed: the disjoint sum of two equivalences is an
    equivalence (dual to equiv_product_closed). *)
Lemma equiv_coproduct_closed : coproduct_closed EquivalenceConstitution.
Proof.
  intros D1 R1 D2 R2 [Hr1 [Hs1 Ht1]] [Hr2 [Hs2 Ht2]].
  split; [ | split ].
  - intro p. destruct p as [a | b]; [ apply Hr1 | apply Hr2 ].
  - intros p q H. destruct p as [a|b]; destruct q as [a'|b']; simpl in *; try contradiction.
    + apply Hs1; exact H.
    + apply Hs2; exact H.
  - intros p q r Hpq Hqr.
    destruct p as [a|b]; destruct q as [a'|b']; destruct r as [a''|b'']; simpl in *; try contradiction.
    + apply Ht1 with a'; assumption.
    + apply Ht2 with b'; assumption.
Qed.

(* ===================================================================== *)
(*  THE COPRODUCT SYSTEM                                                   *)
(* ===================================================================== *)

(** ★★ THE COPRODUCT of two equivalence-systems: Elements = disjoint union, Roles = sum_rel, Rules =
    EquivalenceConstitution (preserved via equiv_coproduct_closed). *)
Definition fs_coproduct {L} (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution) : FunctionalSystem L.
Proof.
  refine {| fs_constitution := EquivalenceConstitution;
            fs_domain := (get_Elements S1 + get_Elements S2)%type;
            fs_relations := sum_rel (get_Roles S1) (get_Roles S2);
            fs_functional := _;
            fs_element_level := fun x => match x with
                                         | inl a => fs_element_level S1 a
                                         | inr b => fs_element_level S2 b end;
            fs_level_valid := _ |}.
  - apply equiv_coproduct_closed.
    + rewrite <- H1. exact (fs_functional S1).
    + rewrite <- H2. exact (fs_functional S2).
  - intros [a | b]; [ exact (fs_level_valid S1 a) | exact (fs_level_valid S2 b) ].
Defined.

(** ★ ELEMENTS = the disjoint union of the parts' Elements. *)
Lemma fs_coproduct_elements : forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
  get_Elements (fs_coproduct S1 S2 H1 H2) = (get_Elements S1 + get_Elements S2)%type.
Proof. intros. reflexivity. Qed.

(** ★ ROLES = the sum relation of the parts' Roles. *)
Lemma fs_coproduct_roles : forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
  get_Roles (fs_coproduct S1 S2 H1 H2) = sum_rel (get_Roles S1) (get_Roles S2).
Proof. intros. reflexivity. Qed.

(** ★ RULES = EquivalenceConstitution. *)
Lemma fs_coproduct_rules : forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
  fs_constitution (fs_coproduct S1 S2 H1 H2) = EquivalenceConstitution.
Proof. intros. reflexivity. Qed.

(* ===================================================================== *)
(*  INJECTIONS (dual to the projections fs_proj1 / fs_proj2)              *)
(* ===================================================================== *)

(** The left injection is a genuine E/R/R-morphism. *)
Definition fs_inl {L} (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution)
  : ERRMorphism S1 (fs_coproduct S1 S2 H1 H2).
Proof. refine (@mkERRMorphism L S1 (fs_coproduct S1 S2 H1 H2) (fun a => inl a) _).
  intros x y H. exact H.
Defined.

(** The right injection is a genuine E/R/R-morphism. *)
Definition fs_inr {L} (S1 S2 : FunctionalSystem L)
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution)
  : ERRMorphism S2 (fs_coproduct S1 S2 H1 H2).
Proof. refine (@mkERRMorphism L S2 (fs_coproduct S1 S2 H1 H2) (fun b => inr b) _).
  intros x y H. exact H.
Defined.

(* ===================================================================== *)
(*  THE COPAIRING [g1, g2] and the dual universal property               *)
(* ===================================================================== *)

(** The copairing: given g1 : S1 -> T and g2 : S2 -> T, the mediator S1+S2 -> T. *)
Definition fs_copair {L} {S1 S2 T : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution)
  (g1 : ERRMorphism S1 T) (g2 : ERRMorphism S2 T)
  : ERRMorphism (fs_coproduct S1 S2 H1 H2) T.
Proof.
  refine (@mkERRMorphism L (fs_coproduct S1 S2 H1 H2) T
            (fun x => match x with inl a => err_map g1 a | inr b => err_map g2 b end) _).
  intros x y H. destruct x as [a|b]; destruct y as [a'|b']; simpl in *; try contradiction.
  - apply (err_pres g1); exact H.
  - apply (err_pres g2); exact H.
Defined.

(** ★ Computation rule (left): copair ∘ inl = g1. *)
Lemma coproduct_inl_compute : forall {L} {S1 S2 T : FunctionalSystem L} H1 H2
  (g1 : ERRMorphism S1 T) (g2 : ERRMorphism S2 T) (a : get_Elements S1),
  err_map (fs_copair H1 H2 g1 g2) (inl a) = err_map g1 a.
Proof. intros. reflexivity. Qed.

(** ★ Computation rule (right): copair ∘ inr = g2. *)
Lemma coproduct_inr_compute : forall {L} {S1 S2 T : FunctionalSystem L} H1 H2
  (g1 : ERRMorphism S1 T) (g2 : ERRMorphism S2 T) (b : get_Elements S2),
  err_map (fs_copair H1 H2 g1 g2) (inr b) = err_map g2 b.
Proof. intros. reflexivity. Qed.

(** ★★ UNIQUENESS of the mediator: any h agreeing with g1 on inl and g2 on inr equals the copairing. *)
Lemma coproduct_mediator_unique : forall {L} {S1 S2 T : FunctionalSystem L} H1 H2
  (g1 : ERRMorphism S1 T) (g2 : ERRMorphism S2 T)
  (h : ERRMorphism (fs_coproduct S1 S2 H1 H2) T),
  (forall a, err_map h (inl a) = err_map g1 a) ->
  (forall b, err_map h (inr b) = err_map g2 b) ->
  err_morph_eq h (fs_copair H1 H2 g1 g2).
Proof.
  intros L S1 S2 T H1 H2 g1 g2 h Hinl Hinr x. destruct x as [a | b].
  - rewrite Hinl. reflexivity.
  - rewrite Hinr. reflexivity.
Qed.

(* ===================================================================== *)
(*  DECOMPOSITION — the parts are separate                                 *)
(* ===================================================================== *)

(** ★ Every element of the sum is in exactly one summand. *)
Lemma coproduct_cases : forall {L} {S1 S2 : FunctionalSystem L} H1 H2
  (x : get_Elements (fs_coproduct S1 S2 H1 H2)),
  (exists a, x = inl a) \/ (exists b, x = inr b).
Proof. intros L S1 S2 H1 H2 x. destruct x as [a|b]; [ left; exists a | right; exists b ]; reflexivity. Qed.

(** ★ The summands are disjoint. *)
Lemma coproduct_inl_neq_inr : forall {L} {S1 S2 : FunctionalSystem L} H1 H2
  (a : get_Elements S1) (b : get_Elements S2),
  (inl a : get_Elements (fs_coproduct S1 S2 H1 H2)) <> inr b.
Proof. intros. discriminate. Qed.

(** ★★ The two parts NEVER relate across — the sum is maximally decomposable (opposite of
    entanglement). *)
Lemma coproduct_no_cross_roles : forall {L} {S1 S2 : FunctionalSystem L} H1 H2
  (a : get_Elements S1) (b : get_Elements S2),
  ~ get_Roles (fs_coproduct S1 S2 H1 H2) (inl a) (inr b).
Proof. intros L S1 S2 H1 H2 a b. exact (fun h => h). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE COPRODUCT (dual of the product):
      (triad)        Elements = disjoint union, Roles = sum_rel, Rules = shared constitution;
      (Rules)        the constitution is coproduct-closed (equivalence);
      (universal)    injections + a UNIQUE copairing (copair ∘ inl = g1, copair ∘ inr = g2);
      (decomposition) the two parts never relate across — maximally decomposable.
    The sum DECOMPOSES into separate alternatives, exactly dual to the product's combination. *)
Theorem err_coproduct :
  (forall (L : Level) (S1 S2 : FunctionalSystem L) H1 H2,
     get_Elements (fs_coproduct S1 S2 H1 H2) = (get_Elements S1 + get_Elements S2)%type
     /\ get_Roles (fs_coproduct S1 S2 H1 H2) = sum_rel (get_Roles S1) (get_Roles S2)
     /\ fs_constitution (fs_coproduct S1 S2 H1 H2) = EquivalenceConstitution)
  /\ coproduct_closed EquivalenceConstitution
  /\ (forall (L : Level) (S1 S2 T : FunctionalSystem L) H1 H2
            (g1 : ERRMorphism S1 T) (g2 : ERRMorphism S2 T),
        (forall a, err_map (fs_copair H1 H2 g1 g2) (inl a) = err_map g1 a)
        /\ (forall b, err_map (fs_copair H1 H2 g1 g2) (inr b) = err_map g2 b)
        /\ (forall (h : ERRMorphism (fs_coproduct S1 S2 H1 H2) T),
              (forall a, err_map h (inl a) = err_map g1 a) ->
              (forall b, err_map h (inr b) = err_map g2 b) ->
              err_morph_eq h (fs_copair H1 H2 g1 g2)))
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) H1 H2
            (a : get_Elements S1) (b : get_Elements S2),
        ~ get_Roles (fs_coproduct S1 S2 H1 H2) (inl a) (inr b)).
Proof.
  split; [ intros L S1 S2 H1 H2; split; [ reflexivity | split; reflexivity ] | ].
  split; [ exact equiv_coproduct_closed | ].
  split.
  - intros L S1 S2 T H1 H2 g1 g2.
    split; [ exact (coproduct_inl_compute H1 H2 g1 g2) | ].
    split; [ exact (coproduct_inr_compute H1 H2 g1 g2)
           | exact (coproduct_mediator_unique H1 H2 g1 g2) ].
  - intros L S1 S2 H1 H2 a b. exact (coproduct_no_cross_roles H1 H2 a b).
Qed.

Print Assumptions err_coproduct.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Thread ③: the COPRODUCT (sum) of systems = the categorical DUAL of         *)
(*  ERRComposition.fs_product.  sum_rel (disjoint-union relation),             *)
(*  coproduct_closed + equiv_coproduct_closed (dual to product_closed);        *)
(*  fs_coproduct (Elements = disjoint union, Roles = sum_rel, Rules = shared   *)
(*  equivalence): fs_coproduct_elements/roles/rules.  Injections fs_inl/fs_inr *)
(*  (dual to fs_proj1/fs_proj2).  Dual universal property: fs_copair +         *)
(*  coproduct_inl_compute/_inr_compute + coproduct_mediator_unique.            *)
(*  DECOMPOSITION: coproduct_cases (every elem in one summand),                *)
(*  coproduct_inl_neq_inr (disjoint), coproduct_no_cross_roles (parts never    *)
(*  relate — opposite of entanglement).  Capstone err_coproduct.  HONEST:      *)
(*  shared (equivalence) constitution as the product; universal property at    *)
(*  the map level (dual to ERRProductUniversal); same category (ERRMorphism).  *)
(* ========================================================================= *)
