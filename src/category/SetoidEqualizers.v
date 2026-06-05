(** * SetoidEqualizers.v — Equalizers in SetoidCat as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: points x of A with f(x) ~ g(x), the inclusion, the mediator
    Roles:    eq_setoid -> "the subobject where f and g agree"; eq_incl -> the
              inclusion; eq_mediator -> the unique arrow factoring through the
              agreement locus
    Rules:    the universal property (equalizes + unique lift) constitutes the
              equalizer (constitution)
    Status:   SetoidCat has equalizers (hence, with products, finite limits)

    P4 diagnostic.  An equalizer is a subsetoid — a finitely actual carving by the
    agreement predicate; the universal property is the RULE of unique lifting, not
    a completed object over all cones.

    Builds on: stdlib/Category.v, category/SetoidCategory.v.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import category.SetoidCategory.

(* ================================================================= *)
(*  The equalizer subsetoid {x : A | f x ~ g x}                     *)
(* ================================================================= *)

Definition eq_setoid (A B : Setoid) (f g : SetoidMor A B) : Setoid :=
  mkSetoid
    { x : st_carrier A | st_eq (sm_map f x) (sm_map g x) }
    (fun p q => st_eq (proj1_sig p) (proj1_sig q))
    (fun p => st_refl (proj1_sig p))
    (fun p q H => st_sym H)
    (fun p q r H1 H2 => st_trans H1 H2).

(** The inclusion of the equalizer into A *)
Definition eq_incl (A B : Setoid) (f g : SetoidMor A B) :
  SetoidMor (eq_setoid A B f g) A :=
  mkSetoidMor (eq_setoid A B f g) A (fun p => proj1_sig p) (fun p q H => H).

(** The mediator: a map m : C -> A coequalizing f,g lifts uniquely to the
    equalizer *)
Definition eq_mediator (C A B : Setoid) (f g : SetoidMor A B) (m : SetoidMor C A)
  (H : cat_mor_eq SetoidCat C B
         (cat_comp SetoidCat C A B f m) (cat_comp SetoidCat C A B g m)) :
  SetoidMor C (eq_setoid A B f g) :=
  mkSetoidMor C (eq_setoid A B f g)
    (fun c => exist _ (sm_map m c) (H c))
    (fun c c' Hcc' => sm_resp m Hcc').

(* ----- universal property ----- *)

(** f and g agree on the equalizer:  f . incl = g . incl *)
Lemma eq_equalizes : forall (A B : Setoid) (f g : SetoidMor A B),
  cat_mor_eq SetoidCat (eq_setoid A B f g) B
    (cat_comp SetoidCat (eq_setoid A B f g) A B f (eq_incl A B f g))
    (cat_comp SetoidCat (eq_setoid A B f g) A B g (eq_incl A B f g)).
Proof.
  intros A B f g. intro p. simpl. exact (proj2_sig p).
Qed.

(** The mediator lifts m:  incl . mediator = m *)
Lemma eq_univ : forall (C A B : Setoid) (f g : SetoidMor A B) (m : SetoidMor C A)
  (H : cat_mor_eq SetoidCat C B
         (cat_comp SetoidCat C A B f m) (cat_comp SetoidCat C A B g m)),
  cat_mor_eq SetoidCat C A
    (cat_comp SetoidCat C (eq_setoid A B f g) A
       (eq_incl A B f g) (eq_mediator C A B f g m H))
    m.
Proof.
  intros C A B f g m H. intro c. simpl. apply st_refl.
Qed.

(** Uniqueness: any lift of m through the inclusion equals the mediator *)
Lemma eq_unique : forall (C A B : Setoid) (f g : SetoidMor A B) (m : SetoidMor C A)
  (H : cat_mor_eq SetoidCat C B
         (cat_comp SetoidCat C A B f m) (cat_comp SetoidCat C A B g m))
  (n : SetoidMor C (eq_setoid A B f g)),
  cat_mor_eq SetoidCat C A
    (cat_comp SetoidCat C (eq_setoid A B f g) A (eq_incl A B f g) n) m ->
  cat_mor_eq SetoidCat C (eq_setoid A B f g) n (eq_mediator C A B f g m H).
Proof.
  intros C A B f g m H n Hn. intro c. simpl. exact (Hn c).
Qed.

(* ================================================================= *)
(*  Summary: 3 Qed, 0 Admitted, 0 axioms                            *)
(*    eq_equalizes, eq_univ, eq_unique                              *)
(*    (eq_setoid, eq_incl, eq_mediator are definitions)             *)
(* ================================================================= *)
