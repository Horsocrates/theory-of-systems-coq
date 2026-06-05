(** * SetoidCategory.v — The category of setoids as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: setoids (types with an equivalence), setoid maps (relation-respecting)
    Roles:    setoid_id -> Neutral, setoid_comp -> Combinator
    Rules:    category laws hold pointwise from the target setoid's relation
    Status:   SetoidCat; the right target for hom-functors (unblocks Yoneda)

    Builds on: stdlib/Category.v.

    Why this category.  A representable functor Hom(x,-) sends an object a to the
    *hom-set* cat_mor C x a, whose natural notion of equality is cat_mor_eq — a
    setoid relation, NOT Leibniz equality.  The strict category of types TypeCat
    (whose morphism-equality is pointwise =) therefore cannot receive Hom(x,-)
    functorially.  SetoidCat — objects are types-with-an-equivalence, morphisms
    are functions respecting the equivalence, morphism-equality is pointwise the
    target relation — is the correct codomain, and makes Hom(x,-) a functor
    (see RepresentableFunctor / YonedaLemma).

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.

(* ================================================================= *)
(*  Setoids and setoid maps                                          *)
(* ================================================================= *)

Record Setoid := mkSetoid {
  st_carrier : Type;
  st_eq : st_carrier -> st_carrier -> Prop;
  st_refl : forall x, st_eq x x;
  st_sym : forall x y, st_eq x y -> st_eq y x;
  st_trans : forall x y z, st_eq x y -> st_eq y z -> st_eq x z;
}.

Arguments st_eq {_} _ _.
Arguments st_refl {_} _.
Arguments st_sym {_} {_ _} _.
Arguments st_trans {_} {_ _ _} _ _.

Record SetoidMor (A B : Setoid) := mkSetoidMor {
  sm_map : st_carrier A -> st_carrier B;
  sm_resp : forall x y, st_eq x y -> st_eq (sm_map x) (sm_map y);
}.

Arguments sm_map {A B} _ _.
Arguments sm_resp {A B} _ {x y} _.

Definition setoid_id (A : Setoid) : SetoidMor A A :=
  mkSetoidMor A A (fun x => x) (fun x y H => H).

Definition setoid_comp (A B C : Setoid)
  (g : SetoidMor B C) (f : SetoidMor A B) : SetoidMor A C :=
  mkSetoidMor A C
    (fun x => sm_map g (sm_map f x))
    (fun x y H => sm_resp g (sm_resp f H)).

Definition SetoidMorEq (A B : Setoid) (f g : SetoidMor A B) : Prop :=
  forall x, st_eq (sm_map f x) (sm_map g x).

(* ================================================================= *)
(*  The category SetoidCat                                           *)
(* ================================================================= *)

Definition SetoidCat : Category.
Proof.
  apply (mkCategory Setoid SetoidMor SetoidMorEq setoid_id setoid_comp).
  - (* refl *)
    intros A B f. unfold SetoidMorEq. intro x. apply st_refl.
  - (* sym *)
    intros A B f g H. unfold SetoidMorEq in *. intro x. apply st_sym. apply H.
  - (* trans *)
    intros A B f g h Hfg Hgh. unfold SetoidMorEq in *. intro x.
    apply (st_trans (Hfg x) (Hgh x)).
  - (* comp_compat *)
    intros A B C F F' G G' HF HG. unfold SetoidMorEq in *. intro x. simpl.
    apply (st_trans (y := sm_map F (sm_map G' x))).
    + apply (sm_resp F). apply HG.
    + apply HF.
  - (* assoc *)
    intros A B C D F G H. unfold SetoidMorEq. intro x. simpl. apply st_refl.
  - (* id_l *)
    intros A B F. unfold SetoidMorEq. intro x. simpl. apply st_refl.
  - (* id_r *)
    intros A B F. unfold SetoidMorEq. intro x. simpl. apply st_refl.
Defined.

(* ================================================================= *)
(*  Basic facts                                                      *)
(* ================================================================= *)

(** Morphism equality in SetoidCat is pointwise the target relation *)
Lemma SetoidCat_mor_eq_iff : forall (A B : Setoid) (f g : SetoidMor A B),
  cat_mor_eq SetoidCat A B f g <-> (forall x, st_eq (sm_map f x) (sm_map g x)).
Proof.
  intros A B f g. split; intro H; exact H.
Qed.

(** Composition in SetoidCat is map composition *)
Lemma SetoidCat_comp_map : forall (A B C : Setoid)
  (g : SetoidMor B C) (f : SetoidMor A B) (x : st_carrier A),
  sm_map (cat_comp SetoidCat A B C g f) x = sm_map g (sm_map f x).
Proof.
  intros. simpl. reflexivity.
Qed.

(** The identity of SetoidCat is the identity map *)
Lemma SetoidCat_id_map : forall (A : Setoid) (x : st_carrier A),
  sm_map (cat_id SetoidCat A) x = x.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ----- a concrete example: every Type gives a discrete setoid ----- *)

Definition discrete_setoid (T : Type) : Setoid :=
  mkSetoid T (fun x y => x = y)
    (fun x => eq_refl)
    (fun x y H => eq_sym H)
    (fun x y z H1 H2 => eq_trans H1 H2).

(** Any function lifts to a setoid map between discrete setoids *)
Definition discrete_mor (S T : Type) (h : S -> T) :
  SetoidMor (discrete_setoid S) (discrete_setoid T) :=
  mkSetoidMor (discrete_setoid S) (discrete_setoid T) h
    (fun x y (H : x = y) => f_equal h H).

(* ================================================================= *)
(*  Summary: 3 Qed, 0 Admitted, 0 axioms                            *)
(*    SetoidCat_mor_eq_iff, SetoidCat_comp_map, SetoidCat_id_map      *)
(*    (SetoidCat, discrete_setoid, discrete_mor are Definitions)      *)
(* ================================================================= *)
