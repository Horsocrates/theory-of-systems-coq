(** * SetoidClassifier.v — A subobject classifier in SetoidCat

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: propositions (points of Omega), true : 1 -> Omega, the
              characteristic arrow chi_P, the subobject {a | P a}
    Roles:    Omega -> "the object of truth values"; true -> selection of truth;
              chi_P -> the indicator of a predicate; {a | P a} -> the subobject
    Rules:    classification: a (respectful) predicate P corresponds to an arrow
              chi_P : A -> Omega, and {a | P a} is the pullback of true along chi_P
    Status:   Omega = (Prop, <->); respectful predicates classify subobjects

    P4 diagnostic.  Omega = (Prop, <->) is a role-level object of values (equality
    is logical equivalence, not Leibniz); classification is the RULE predicate <->
    indicator, not a completed "set of all subsets".

    Honest boundary.  This classifies RESPECTFUL PREDICATES (constructive
    subsetoids), not arbitrary monomorphisms (those need image factorization).
    It is the constructive setoid form of the subobject classifier.

    Builds on: stdlib/Category.v, category/SetoidCategory.v,
               category/SetoidProducts.v (unit_setoid).

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import category.SetoidCategory.
From ToS Require Import category.SetoidProducts.

(* ================================================================= *)
(*  Omega = (Prop, <->) and the truth arrow                          *)
(* ================================================================= *)

Definition omega_setoid : Setoid :=
  mkSetoid Prop (fun P Q => P <-> Q)
    (fun P => conj (fun x => x) (fun x => x))
    (fun P Q H => conj (proj2 H) (proj1 H))
    (fun P Q R H1 H2 =>
       conj (fun p => proj1 H2 (proj1 H1 p)) (fun r => proj2 H1 (proj2 H2 r))).

Definition setoid_true : SetoidMor unit_setoid omega_setoid :=
  mkSetoidMor unit_setoid omega_setoid (fun _ => True)
    (fun x y _ => conj (fun t => t) (fun t => t)).

(* ================================================================= *)
(*  Characteristic arrows and the predicate <-> arrow bijection      *)
(* ================================================================= *)

(** A respectful predicate yields a characteristic map A -> Omega *)
Definition char (A : Setoid) (P : st_carrier A -> Prop)
  (HP : forall a a', st_eq a a' -> (P a <-> P a')) : SetoidMor A omega_setoid :=
  mkSetoidMor A omega_setoid (fun a => P a) (fun a a' H => HP a a' H).

(** Every arrow A -> Omega is the characteristic map of its own predicate
    (the predicate <-> arrow correspondence is a bijection) *)
Lemma char_self : forall (A : Setoid) (chi : SetoidMor A omega_setoid),
  cat_mor_eq SetoidCat A omega_setoid
    (char A (fun a => sm_map chi a) (fun a a' H => sm_resp chi H)) chi.
Proof.
  intros A chi. intro a. apply st_refl.
Qed.

(* ================================================================= *)
(*  The subobject {a | P a} and its classification                   *)
(* ================================================================= *)

Definition sub_setoid (A : Setoid) (P : st_carrier A -> Prop) : Setoid :=
  mkSetoid { a : st_carrier A | P a }
    (fun p q => st_eq (proj1_sig p) (proj1_sig q))
    (fun p => st_refl (proj1_sig p))
    (fun p q H => st_sym H)
    (fun p q r H1 H2 => st_trans H1 H2).

Definition sub_incl (A : Setoid) (P : st_carrier A -> Prop) :
  SetoidMor (sub_setoid A P) A :=
  mkSetoidMor (sub_setoid A P) A (fun p => proj1_sig p) (fun p q H => H).

(** Commuting square: chi_P holds on the subobject (= true . !) *)
Lemma subobject_commute : forall (A : Setoid) (P : st_carrier A -> Prop)
  (HP : forall a a', st_eq a a' -> (P a <-> P a'))
  (s : st_carrier (sub_setoid A P)),
  sm_map (char A P HP) (sm_map (sub_incl A P) s) <-> True.
Proof.
  intros A P HP s. simpl. split.
  - intro; exact I.
  - intro. exact (proj2_sig s).
Qed.

(** The mediator: if z : Z -> A lands in the subobject (P (z x) for all x),
    it lifts uniquely to {a | P a} *)
Definition subobject_mediator (Z A : Setoid) (P : st_carrier A -> Prop)
  (z : SetoidMor Z A) (Hz : forall x, P (sm_map z x)) :
  SetoidMor Z (sub_setoid A P) :=
  mkSetoidMor Z (sub_setoid A P)
    (fun x => exist _ (sm_map z x) (Hz x))
    (fun x x' H => sm_resp z H).

(** The mediator lifts z:  incl . mediator = z *)
Lemma subobject_univ : forall (Z A : Setoid) (P : st_carrier A -> Prop)
  (z : SetoidMor Z A) (Hz : forall x, P (sm_map z x)),
  cat_mor_eq SetoidCat Z A
    (cat_comp SetoidCat Z (sub_setoid A P) A
       (sub_incl A P) (subobject_mediator Z A P z Hz))
    z.
Proof.
  intros Z A P z Hz. intro x. simpl. apply st_refl.
Qed.

(** Uniqueness of the mediator *)
Lemma subobject_unique : forall (Z A : Setoid) (P : st_carrier A -> Prop)
  (z : SetoidMor Z A) (Hz : forall x, P (sm_map z x))
  (m : SetoidMor Z (sub_setoid A P)),
  cat_mor_eq SetoidCat Z A
    (cat_comp SetoidCat Z (sub_setoid A P) A (sub_incl A P) m) z ->
  cat_mor_eq SetoidCat Z (sub_setoid A P) m (subobject_mediator Z A P z Hz).
Proof.
  intros Z A P z Hz m Hm. intro x. simpl. exact (Hm x).
Qed.

(* ================================================================= *)
(*  Summary: 4 Qed, 0 Admitted, 0 axioms                            *)
(*    char_self, subobject_commute, subobject_univ, subobject_unique  *)
(*    (+ setoid_true sanity); omega/char/sub_setoid/mediator are defs *)
(* ================================================================= *)
