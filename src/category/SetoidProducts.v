(** * SetoidProducts.v — Finite products in SetoidCat as a ToS System

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: pairs (a,b), projections, the mediating map <f,g>, the unit setoid
    Roles:    prod_setoid -> "joint state"; fst/snd -> component observers;
              <f,g> -> the mediator (the unique reconciling arrow);
              unit_setoid -> the terminal role (no distinctions)
    Rules:    the universal property (beta1, beta2, eta-uniqueness) constitutes the
              product; the unit setoid is terminal (constitution)
    Status:   SetoidCat has a terminal object and binary products

    P4 diagnostic.  A product is finitely actual (a pair is a finite carrier);
    the universal property is the RULE of unique factorization, not a completed
    object over all cones.  Equality on a product is componentwise conjunction —
    role-level, not Leibniz.

    Builds on: stdlib/Category.v, category/SetoidCategory.v.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import category.SetoidCategory.

(* ================================================================= *)
(*  Terminal object                                                  *)
(* ================================================================= *)

Definition unit_setoid : Setoid :=
  mkSetoid unit (fun _ _ => True)
    (fun _ => I) (fun _ _ _ => I) (fun _ _ _ _ _ => I).

Lemma setoid_terminal : is_terminal SetoidCat unit_setoid.
Proof.
  intro B.
  exists (mkSetoidMor B unit_setoid (fun _ => tt) (fun _ _ _ => I)).
  intro g. intro x. simpl. exact I.
Qed.

(* ================================================================= *)
(*  Binary product                                                   *)
(* ================================================================= *)

Definition prod_setoid (A B : Setoid) : Setoid :=
  mkSetoid (st_carrier A * st_carrier B)
    (fun p q => st_eq (fst p) (fst q) /\ st_eq (snd p) (snd q))
    (fun p => conj (st_refl (fst p)) (st_refl (snd p)))
    (fun p q H => conj (st_sym (proj1 H)) (st_sym (proj2 H)))
    (fun p q r H1 H2 =>
       conj (st_trans (proj1 H1) (proj1 H2)) (st_trans (proj2 H1) (proj2 H2))).

Definition setoid_fst (A B : Setoid) : SetoidMor (prod_setoid A B) A :=
  mkSetoidMor (prod_setoid A B) A (fun p => fst p) (fun p q H => proj1 H).

Definition setoid_snd (A B : Setoid) : SetoidMor (prod_setoid A B) B :=
  mkSetoidMor (prod_setoid A B) B (fun p => snd p) (fun p q H => proj2 H).

(** The mediating map <f,g> : C -> A x B *)
Definition setoid_pair (C A B : Setoid)
  (f : SetoidMor C A) (g : SetoidMor C B) : SetoidMor C (prod_setoid A B) :=
  mkSetoidMor C (prod_setoid A B)
    (fun c => (sm_map f c, sm_map g c))
    (fun c c' H => conj (sm_resp f H) (sm_resp g H)).

(* ----- universal property ----- *)

(** fst . <f,g> = f *)
Lemma setoid_prod_beta1 : forall (C A B : Setoid)
  (f : SetoidMor C A) (g : SetoidMor C B),
  cat_mor_eq SetoidCat C A
    (cat_comp SetoidCat C (prod_setoid A B) A (setoid_fst A B) (setoid_pair C A B f g))
    f.
Proof.
  intros C A B f g. intro c. simpl. apply st_refl.
Qed.

(** snd . <f,g> = g *)
Lemma setoid_prod_beta2 : forall (C A B : Setoid)
  (f : SetoidMor C A) (g : SetoidMor C B),
  cat_mor_eq SetoidCat C B
    (cat_comp SetoidCat C (prod_setoid A B) B (setoid_snd A B) (setoid_pair C A B f g))
    g.
Proof.
  intros C A B f g. intro c. simpl. apply st_refl.
Qed.

(** Uniqueness: any m with fst.m = f and snd.m = g equals <f,g> *)
Lemma setoid_prod_unique : forall (C A B : Setoid)
  (f : SetoidMor C A) (g : SetoidMor C B) (m : SetoidMor C (prod_setoid A B)),
  cat_mor_eq SetoidCat C A (cat_comp SetoidCat C (prod_setoid A B) A (setoid_fst A B) m) f ->
  cat_mor_eq SetoidCat C B (cat_comp SetoidCat C (prod_setoid A B) B (setoid_snd A B) m) g ->
  cat_mor_eq SetoidCat C (prod_setoid A B) m (setoid_pair C A B f g).
Proof.
  intros C A B f g m H1 H2. intro c. simpl. split.
  - exact (H1 c).
  - exact (H2 c).
Qed.

(* ================================================================= *)
(*  Summary: 4 Qed, 0 Admitted, 0 axioms                            *)
(*    setoid_terminal, setoid_prod_beta1, setoid_prod_beta2,         *)
(*    setoid_prod_unique                                             *)
(*    (unit_setoid, prod_setoid, setoid_fst/snd/pair are defs)       *)
(* ================================================================= *)
