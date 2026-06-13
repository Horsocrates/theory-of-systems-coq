(** * ERRProductUniversal.v — довесок к Кирпичу 2: the E/R/R product is a GENUINE categorical
      product — the universal property (mediator exists and is unique).

    ERRComposition.v built the product fs_product with projections fs_proj1/fs_proj2.  This file
    proves the UNIVERSAL PROPERTY, upgrading "a construction with projections" to "the product":
    for any cone (f1 : T -> S1, f2 : T -> S2) there is a mediating morphism <f1,f2> : T -> product
    with proj_i o <f1,f2> = f_i, and it is the UNIQUE such morphism (up to err_morph_eq).

      ★ fs_pair      : the mediator <f1,f2> (the componentwise pair of maps; Roles preserved by both);
      ★ product_proj1/proj2 : the projections recover the components;
      ★ product_mediator_unique : any g agreeing with f1, f2 through the projections equals <f1,f2>.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) for any f1 : T -> S1, f2 : T -> S2 there is a mediator <f1,f2> : T -> product;
      (2) the projections recover the components (proj_i o <f1,f2> = f_i);
      (3) the mediator is UNIQUE (any g with the same projections equals <f1,f2>).
    Roles (L4): fs_pair = the mediator; fs_proj1/fs_proj2 = the projections; err_comp = composition.
    Elements (L1+P4): the systems T, S1, S2; the componentwise pair of maps.
    P4 diagnostic (could it be otherwise?):
      The universal property is forced by the product structure (pairs + prod_rel): the mediator is
      the componentwise pair, and uniqueness is surjective_pairing on the carrier.  A genuine
      categorical product in the E/R/R-morphism category at level L.
    Honesty wall:
      the product is (as in Кирпич 2) for equivalence-systems; uniqueness is up to err_morph_eq
      (extensional equality of the Elements-maps), not record equality (which would need proof
      irrelevance).  0 axioms.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.

(* Restore implicit {L} on the projections (section-local in Core_ERR). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.

(* ===================================================================== *)
(*  THE MEDIATOR                                                           *)
(* ===================================================================== *)

(** ★ The mediator <f1,f2> : T -> S1 x S2 — the componentwise pair of maps; it preserves Roles
    because both f1 and f2 do (the product relation is the conjunction). *)
Definition fs_pair {L} {T S1 S2 : FunctionalSystem L}
  (H1 : fs_constitution S1 = EquivalenceConstitution)
  (H2 : fs_constitution S2 = EquivalenceConstitution)
  (f1 : ERRMorphism T S1) (f2 : ERRMorphism T S2)
  : ERRMorphism T (fs_product S1 S2 H1 H2).
Proof.
  refine (@mkERRMorphism L T (fs_product S1 S2 H1 H2)
            (fun t => (err_map f1 t, err_map f2 t)) _).
  intros x y H. split; [ exact (err_pres f1 x y H) | exact (err_pres f2 x y H) ].
Defined.

(* ===================================================================== *)
(*  THE UNIVERSAL PROPERTY                                                 *)
(* ===================================================================== *)

(** ★ The first projection recovers the first component. *)
Theorem product_proj1 :
  forall {L} {T S1 S2 : FunctionalSystem L} H1 H2
         (f1 : ERRMorphism T S1) (f2 : ERRMorphism T S2),
    err_morph_eq (err_comp (fs_pair H1 H2 f1 f2) (fs_proj1 S1 S2 H1 H2)) f1.
Proof. intros L T S1 S2 H1 H2 f1 f2 t. reflexivity. Qed.

(** ★ The second projection recovers the second component. *)
Theorem product_proj2 :
  forall {L} {T S1 S2 : FunctionalSystem L} H1 H2
         (f1 : ERRMorphism T S1) (f2 : ERRMorphism T S2),
    err_morph_eq (err_comp (fs_pair H1 H2 f1 f2) (fs_proj2 S1 S2 H1 H2)) f2.
Proof. intros L T S1 S2 H1 H2 f1 f2 t. reflexivity. Qed.

(** ★★ UNIQUENESS: any morphism g whose projections are f1 and f2 equals the mediator <f1,f2>. *)
Theorem product_mediator_unique :
  forall {L} {T S1 S2 : FunctionalSystem L} H1 H2
         (f1 : ERRMorphism T S1) (f2 : ERRMorphism T S2)
         (g : ERRMorphism T (fs_product S1 S2 H1 H2)),
    err_morph_eq (err_comp g (fs_proj1 S1 S2 H1 H2)) f1 ->
    err_morph_eq (err_comp g (fs_proj2 S1 S2 H1 H2)) f2 ->
    err_morph_eq g (fs_pair H1 H2 f1 f2).
Proof.
  intros L T S1 S2 H1 H2 f1 f2 g Hp1 Hp2 t.
  specialize (Hp1 t). specialize (Hp2 t). cbn in Hp1, Hp2.
  cbn. rewrite (surjective_pairing (err_map g t)). rewrite Hp1, Hp2. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The E/R/R product is a GENUINE categorical product: the mediator exists (fs_pair), the
    projections recover the components, and the mediator is unique. *)
Theorem err_product_universal :
  forall {L} {T S1 S2 : FunctionalSystem L} H1 H2
         (f1 : ERRMorphism T S1) (f2 : ERRMorphism T S2),
    err_morph_eq (err_comp (fs_pair H1 H2 f1 f2) (fs_proj1 S1 S2 H1 H2)) f1
    /\ err_morph_eq (err_comp (fs_pair H1 H2 f1 f2) (fs_proj2 S1 S2 H1 H2)) f2
    /\ (forall g : ERRMorphism T (fs_product S1 S2 H1 H2),
          err_morph_eq (err_comp g (fs_proj1 S1 S2 H1 H2)) f1 ->
          err_morph_eq (err_comp g (fs_proj2 S1 S2 H1 H2)) f2 ->
          err_morph_eq g (fs_pair H1 H2 f1 f2)).
Proof.
  intros L T S1 S2 H1 H2 f1 f2.
  split; [ exact (product_proj1 H1 H2 f1 f2) | ].
  split; [ exact (product_proj2 H1 H2 f1 f2)
         | exact (product_mediator_unique H1 H2 f1 f2) ].
Qed.

Print Assumptions err_product_universal.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  4 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The E/R/R product (ERRComposition.fs_product) is a GENUINE categorical    *)
(*  product: fs_pair = the mediator <f1,f2>; product_proj1/proj2 recover the   *)
(*  components; product_mediator_unique = uniqueness (up to err_morph_eq).     *)
(*  Capstone err_product_universal.  Completes Кирпич 2's product into a       *)
(*  product-with-universal-property.  HONEST: for equivalence-systems;         *)
(*  uniqueness up to extensional map-equality, not record equality.           *)
(* ========================================================================= *)
