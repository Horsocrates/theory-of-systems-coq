(** * Functor.v — Functors and Natural Transformations as ToS Morphisms

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: functors (structure-preserving maps between categories)
    Roles:    fobj -> Object Map, fmor -> Morphism Map
    Rules:    preserves identity + preserves composition (functor laws)
    Status:   faithful | full | essentially_surjective

    Connection: Category.v (source and target categories)
    Connection: SystemMorphism.v (functors generalize system morphisms)

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
From ToS Require Import stdlib.Category.

(* ================================================================= *)
(*  PART I: FUNCTOR DEFINITION                                        *)
(* ================================================================= *)

(** A functor between two categories: maps objects and morphisms,
    preserving identity and composition. *)
Record Functor (C D : Category) := mkFunctor {
  fobj : cat_obj C -> cat_obj D;
  fmor : forall a b, cat_mor C a b -> cat_mor D (fobj a) (fobj b);
  fmor_compat : forall a b (f g : cat_mor C a b),
    cat_mor_eq C a b f g ->
    cat_mor_eq D (fobj a) (fobj b) (fmor a b f) (fmor a b g);
  fmor_id : forall a,
    cat_mor_eq D (fobj a) (fobj a) (fmor a a (cat_id C a)) (cat_id D (fobj a));
  fmor_comp : forall a b c (f : cat_mor C a b) (g : cat_mor C b c),
    cat_mor_eq D (fobj a) (fobj c)
      (fmor a c (cat_comp C a b c g f))
      (cat_comp D (fobj a) (fobj b) (fobj c) (fmor b c g) (fmor a b f));
}.

Arguments fobj {C D} _ _.
Arguments fmor {C D} _ {a b} _.
Arguments fmor_compat {C D} _ {a b} _ _ _.
Arguments fmor_id {C D} _ _.
Arguments fmor_comp {C D} _ {a b c} _ _.

(* ================================================================= *)
(*  PART II: IDENTITY AND COMPOSITION OF FUNCTORS (2 Qed)             *)
(* ================================================================= *)

(** Identity functor on a category *)
Definition id_functor (C : Category) : Functor C C.
Proof.
  apply (mkFunctor C C (fun a => a) (fun a b f => f)).
  - (* fmor_compat *) intros a b f g H. exact H.
  - (* fmor_id *) intros a. apply cat_mor_eq_refl.
  - (* fmor_comp *) intros a b c f g. apply cat_mor_eq_refl.
Defined.

Lemma id_functor_valid : forall (C : Category),
  forall a, fobj (id_functor C) a = a.
Proof.
  intros C a. reflexivity.
Qed.

(** Composition of functors: G . F *)
Definition compose_functor (C D E : Category)
  (G : Functor D E) (F : Functor C D) : Functor C E.
Proof.
  apply (mkFunctor C E
    (fun a => fobj G (fobj F a))
    (fun a b f => fmor G (fmor F f))).
  - (* fmor_compat *)
    intros a b f g H.
    apply (fmor_compat G).
    apply (fmor_compat F).
    exact H.
  - (* fmor_id *)
    intros a.
    apply (cat_mor_eq_trans E _ _ _ (fmor G (cat_id D (fobj F a)))).
    + apply (fmor_compat G). apply (fmor_id F).
    + apply (fmor_id G).
  - (* fmor_comp *)
    intros a b c f g.
    apply (cat_mor_eq_trans E _ _
      (fmor G (fmor F (cat_comp C a b c g f)))
      (fmor G (cat_comp D (fobj F a) (fobj F b) (fobj F c) (fmor F g) (fmor F f)))).
    + apply (fmor_compat G). apply (fmor_comp F).
    + apply (fmor_comp G).
Defined.

Lemma compose_functor_valid : forall (C D E : Category)
  (G : Functor D E) (F : Functor C D),
  forall a, fobj (compose_functor C D E G F) a = fobj G (fobj F a).
Proof.
  intros. reflexivity.
Qed.

(* ================================================================= *)
(*  PART III: FUNCTOR COMPOSITION LAWS (3 Qed)                        *)
(* ================================================================= *)

(** compose(F, id) has the same fobj as F *)
Lemma compose_id_right : forall (C D : Category) (F : Functor C D),
  forall a, fobj (compose_functor C C D F (id_functor C)) a = fobj F a.
Proof.
  intros C D F a. reflexivity.
Qed.

(** compose(id, F) has the same fobj as F *)
Lemma compose_id_left : forall (C D : Category) (F : Functor C D),
  forall a, fobj (compose_functor C D D (id_functor D) F) a = fobj F a.
Proof.
  intros C D F a. reflexivity.
Qed.

(** Composition of functors is associative on objects *)
Lemma compose_functor_assoc : forall (B C D E : Category)
  (F : Functor B C) (G : Functor C D) (H : Functor D E),
  forall a,
    fobj (compose_functor B C E (compose_functor C D E H G) F) a =
    fobj (compose_functor B D E H (compose_functor B C D G F)) a.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================= *)
(*  PART IV: NATURAL TRANSFORMATIONS (2 Qed)                          *)
(* ================================================================= *)

(** A natural transformation between functors F, G : C -> D *)
Record NatTrans (C D : Category) (F G : Functor C D) := mkNatTrans {
  nt_comp : forall a, cat_mor D (fobj F a) (fobj G a);
  nt_natural : forall a b (f : cat_mor C a b),
    cat_mor_eq D (fobj F a) (fobj G b)
      (cat_comp D _ _ _ (nt_comp b) (fmor F f))
      (cat_comp D _ _ _ (fmor G f) (nt_comp a));
}.

Arguments nt_comp {C D F G} _ _.
Arguments nt_natural {C D F G} _ {a b} _.

(** Identity natural transformation: nt_comp a = cat_id *)
Definition id_nat_trans (C D : Category) (F : Functor C D) :
  NatTrans C D F F.
Proof.
  apply (mkNatTrans C D F F (fun a => cat_id D (fobj F a))).
  intros a b f.
  (* Goal: id_b . Ff = Ff . id_a *)
  apply (cat_mor_eq_trans D (fobj F a) (fobj F b)
    (cat_comp D (fobj F a) (fobj F b) (fobj F b) (cat_id D (fobj F b)) (fmor F f))
    (fmor F f)
    (cat_comp D (fobj F a) (fobj F a) (fobj F b) (fmor F f) (cat_id D (fobj F a)))).
  - apply cat_id_l.
  - apply cat_mor_eq_sym. apply cat_id_r.
Defined.

Lemma id_nat_trans_component : forall (C D : Category) (F : Functor C D) (a : cat_obj C),
  cat_mor_eq D (fobj F a) (fobj F a)
    (nt_comp (id_nat_trans C D F) a)
    (cat_id D (fobj F a)).
Proof.
  intros. simpl. apply cat_mor_eq_refl.
Qed.

(** Vertical composition of natural transformations *)
Definition vert_comp_nat_trans (C D : Category) (F G H : Functor C D)
  (alpha : NatTrans C D F G) (beta : NatTrans C D G H) :
  NatTrans C D F H.
Proof.
  apply (mkNatTrans C D F H
    (fun a => cat_comp D (fobj F a) (fobj G a) (fobj H a) (nt_comp beta a) (nt_comp alpha a))).
  intros a b f.
  set (Fa := fobj F a). set (Fb := fobj F b).
  set (Ga := fobj G a). set (Gb := fobj G b).
  set (Ha := fobj H a). set (Hb := fobj H b).
  set (Ff := fmor F f). set (Gf := fmor G f). set (Hf := fmor H f).
  set (alpha_a := nt_comp alpha a). set (alpha_b := nt_comp alpha b).
  set (beta_a := nt_comp beta a). set (beta_b := nt_comp beta b).
  (* Goal: (beta_b . alpha_b) . Ff = Hf . (beta_a . alpha_a) *)
  (* Step 1: (beta_b . alpha_b) . Ff = beta_b . (alpha_b . Ff) by sym(assoc) *)
  apply (cat_mor_eq_trans D Fa Hb
    (cat_comp D Fa Fb Hb (cat_comp D Fb Gb Hb beta_b alpha_b) Ff)
    (cat_comp D Fa Gb Hb beta_b (cat_comp D Fa Fb Gb alpha_b Ff))
    (cat_comp D Fa Ha Hb Hf (cat_comp D Fa Ga Ha beta_a alpha_a))).
  - apply cat_mor_eq_sym. apply cat_assoc.
  - (* Step 2: beta_b . (alpha_b . Ff) = beta_b . (Gf . alpha_a) by naturality of alpha *)
    apply (cat_mor_eq_trans D Fa Hb
      (cat_comp D Fa Gb Hb beta_b (cat_comp D Fa Fb Gb alpha_b Ff))
      (cat_comp D Fa Gb Hb beta_b (cat_comp D Fa Ga Gb Gf alpha_a))
      (cat_comp D Fa Ha Hb Hf (cat_comp D Fa Ga Ha beta_a alpha_a))).
    + apply cat_comp_compat.
      * apply cat_mor_eq_refl.
      * apply (nt_natural alpha f).
    + (* Step 3: beta_b . (Gf . alpha_a) = (beta_b . Gf) . alpha_a by assoc *)
      apply (cat_mor_eq_trans D Fa Hb
        (cat_comp D Fa Gb Hb beta_b (cat_comp D Fa Ga Gb Gf alpha_a))
        (cat_comp D Fa Ga Hb (cat_comp D Ga Gb Hb beta_b Gf) alpha_a)
        (cat_comp D Fa Ha Hb Hf (cat_comp D Fa Ga Ha beta_a alpha_a))).
      * apply cat_assoc.
      * (* Step 4: (beta_b . Gf) . alpha_a = (Hf . beta_a) . alpha_a by naturality of beta *)
        apply (cat_mor_eq_trans D Fa Hb
          (cat_comp D Fa Ga Hb (cat_comp D Ga Gb Hb beta_b Gf) alpha_a)
          (cat_comp D Fa Ga Hb (cat_comp D Ga Ha Hb Hf beta_a) alpha_a)
          (cat_comp D Fa Ha Hb Hf (cat_comp D Fa Ga Ha beta_a alpha_a))).
        -- apply cat_comp_compat.
           ++ apply (nt_natural beta f).
           ++ apply cat_mor_eq_refl.
        -- (* Step 5: (Hf . beta_a) . alpha_a = Hf . (beta_a . alpha_a) by sym(assoc) *)
           apply cat_mor_eq_sym. apply cat_assoc.
Defined.

Lemma vert_comp_nat_trans_component :
  forall (C D : Category) (F G H : Functor C D)
    (alpha : NatTrans C D F G) (beta : NatTrans C D G H) (a : cat_obj C),
  cat_mor_eq D (fobj F a) (fobj H a)
    (nt_comp (vert_comp_nat_trans C D F G H alpha beta) a)
    (cat_comp D _ _ _ (nt_comp beta a) (nt_comp alpha a)).
Proof.
  intros. simpl. apply cat_mor_eq_refl.
Qed.

(* ================================================================= *)
(*  PART V: CONCRETE FUNCTORS IN TypeCat (6 Qed)                     *)
(* ================================================================= *)

(** List functor: maps types to list types, functions to map *)
Definition ListFunctor : Functor TypeCat TypeCat.
Proof.
  apply (mkFunctor TypeCat TypeCat
    (fun A => list A)
    (fun A B (f : A -> B) => map f)).
  - (* fmor_compat: pointwise equal functions give pointwise equal maps *)
    intros A B f g Hfg. simpl. intro l.
    induction l as [| x xs IH].
    + reflexivity.
    + simpl. rewrite Hfg. rewrite IH. reflexivity.
  - (* fmor_id: map id = id *)
    intros A. simpl. intro l. apply map_id.
  - (* fmor_comp: map (g . f) = map g . map f *)
    intros A B C f g. simpl. intro l.
    symmetry. apply map_map.
Defined.

Lemma list_fmor_id : forall (A : Type) (l : list A),
  map (fun x => x) l = l.
Proof.
  intros A l. apply map_id.
Qed.

Lemma list_fmor_comp : forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  intros A B C f g l. apply map_map.
Qed.

Lemma list_functor_valid : forall (A : Type),
  fobj ListFunctor A = list A.
Proof.
  intros A. reflexivity.
Qed.

(** Option functor: maps types to option types, functions to option_map *)
Definition OptionFunctor : Functor TypeCat TypeCat.
Proof.
  apply (mkFunctor TypeCat TypeCat
    (fun A => option A)
    (fun A B (f : A -> B) => option_map f)).
  - (* fmor_compat *)
    intros A B f g Hfg. simpl. intro o.
    destruct o; simpl.
    + rewrite Hfg. reflexivity.
    + reflexivity.
  - (* fmor_id *)
    intros A. simpl. intro o. destruct o; reflexivity.
  - (* fmor_comp *)
    intros A B C f g. simpl. intro o. destruct o; reflexivity.
Defined.

Lemma option_fmor_id : forall (A : Type) (o : option A),
  option_map (fun x => x) o = o.
Proof.
  intros A o. destruct o; reflexivity.
Qed.

Lemma option_fmor_comp : forall (A B C : Type) (f : A -> B) (g : B -> C) (o : option A),
  option_map g (option_map f o) = option_map (fun x => g (f x)) o.
Proof.
  intros A B C f g o. destruct o; reflexivity.
Qed.

Lemma option_functor_valid : forall (A : Type),
  fobj OptionFunctor A = option A.
Proof.
  intros A. reflexivity.
Qed.

(* ================================================================= *)
(*  PART VI: FUNCTORS PRESERVE ISOMORPHISMS (1 Qed)                  *)
(* ================================================================= *)

(** A functor maps isomorphisms to isomorphisms *)
Lemma fmor_preserves_iso : forall (C D : Category) (F : Functor C D)
  (a b : cat_obj C) (f : cat_mor C a b),
  is_iso C a b f ->
  is_iso D (fobj F a) (fobj F b) (fmor F f).
Proof.
  intros C D F a b f [g [Hgf Hfg]].
  exists (fmor F g).
  split.
  - (* F(g) . F(f) = F(g . f) = F(id) = id *)
    apply (cat_mor_eq_trans D _ _ _ (fmor F (cat_comp C a b a g f))).
    + apply cat_mor_eq_sym. apply (fmor_comp F).
    + apply (cat_mor_eq_trans D _ _ _ (fmor F (cat_id C a))).
      * apply (fmor_compat F). exact Hgf.
      * apply (fmor_id F).
  - (* F(f) . F(g) = F(f . g) = F(id) = id *)
    apply (cat_mor_eq_trans D _ _ _ (fmor F (cat_comp C b a b f g))).
    + apply cat_mor_eq_sym. apply (fmor_comp F).
    + apply (cat_mor_eq_trans D _ _ _ (fmor F (cat_id C b))).
      * apply (fmor_compat F). exact Hfg.
      * apply (fmor_id F).
Qed.

(* ================================================================= *)
(*  PART VII: CONSTANT FUNCTOR AND ADDITIONAL LEMMAS (4 Qed)          *)
(* ================================================================= *)

(** Constant functor: maps every object to a fixed object d,
    every morphism to id_d *)
Definition const_functor (C D : Category) (d : cat_obj D) : Functor C D.
Proof.
  apply (mkFunctor C D
    (fun _ => d)
    (fun _ _ _ => cat_id D d)).
  - (* fmor_compat *)
    intros a b f g _. apply cat_mor_eq_refl.
  - (* fmor_id *)
    intros a. apply cat_mor_eq_refl.
  - (* fmor_comp *)
    intros a b c f g.
    apply cat_mor_eq_sym. apply cat_id_l.
Defined.

Lemma const_functor_on_mor : forall (C D : Category) (d : cat_obj D)
  (a b : cat_obj C) (f : cat_mor C a b),
  cat_mor_eq D d d (fmor (const_functor C D d) f) (cat_id D d).
Proof.
  intros. simpl. apply cat_mor_eq_refl.
Qed.

(** A natural transformation from const(c) to const(c') is determined
    by a single morphism c -> c' *)
Lemma const_nat_trans_from_mor : forall (C D : Category)
  (c c' : cat_obj D) (h : cat_mor D c c'),
  NatTrans C D (const_functor C D c) (const_functor C D c').
Proof.
  intros C D c c' h.
  apply (mkNatTrans C D (const_functor C D c) (const_functor C D c')
    (fun _ => h)).
  intros a b f. simpl.
  (* Goal: h . id_c = id_c' . h *)
  apply (cat_mor_eq_trans D c c'
    (cat_comp D c c c' h (cat_id D c))
    h
    (cat_comp D c c' c' (cat_id D c') h)).
  - apply cat_id_r.
  - apply cat_mor_eq_sym. apply cat_id_l.
Qed.

(** Composing any functor with the identity on the right
    gives morphism-equal results *)
Lemma compose_id_right_mor : forall (C D : Category) (F : Functor C D)
  (a b : cat_obj C) (f : cat_mor C a b),
  cat_mor_eq D (fobj F a) (fobj F b)
    (fmor (compose_functor C C D F (id_functor C)) f)
    (fmor F f).
Proof.
  intros C D F a b f. simpl. apply cat_mor_eq_refl.
Qed.

(** Composing any functor with the identity on the left
    gives morphism-equal results *)
Lemma compose_id_left_mor : forall (C D : Category) (F : Functor C D)
  (a b : cat_obj C) (f : cat_mor C a b),
  cat_mor_eq D (fobj F a) (fobj F b)
    (fmor (compose_functor C D D (id_functor D) F) f)
    (fmor F f).
Proof.
  intros C D F a b f. simpl. apply cat_mor_eq_refl.
Qed.

(* ================================================================= *)
(*  Summary: 18 Qed, 0 Admitted, 0 axioms                            *)
(*    2 identity/composition: id_functor_valid, compose_functor_valid  *)
(*    3 composition laws: compose_id_right, compose_id_left,           *)
(*                        compose_functor_assoc                        *)
(*    2 nat trans: id_nat_trans_component,                             *)
(*                 vert_comp_nat_trans_component                       *)
(*    6 concrete: list_fmor_id, list_fmor_comp, list_functor_valid,   *)
(*                option_fmor_id, option_fmor_comp,                    *)
(*                option_functor_valid                                 *)
(*    1 iso: fmor_preserves_iso                                        *)
(*    4 additional: const_functor_on_mor, const_nat_trans_from_mor,    *)
(*                  compose_id_right_mor, compose_id_left_mor          *)
(* ================================================================= *)
