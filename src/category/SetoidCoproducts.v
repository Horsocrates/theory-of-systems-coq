(** * SetoidCoproducts.v — Initial object and coproducts in SetoidCat

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: tagged points inl a / inr b, injections, the copairing [f,g],
              the empty setoid
    Roles:    sum_setoid -> "a disjoint choice of A or B"; injections -> the
              inclusions; [f,g] -> the comediator (the unique arrow OUT of the sum);
              empty_setoid -> the initial role (no points)
    Rules:    the universal property (beta1, beta2, uniqueness), dual to the
              product; initiality of the empty setoid (constitution)
    Status:   SetoidCat has an initial object and binary coproducts (hence finite
              colimits)

    P4 diagnostic.  A coproduct is a tagged union (finitely actual); the universal
    property is the RULE of unique co-factorization.  The empty carrier is the
    absence of distinctions.

    Builds on: stdlib/Category.v, category/SetoidCategory.v.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import category.SetoidCategory.

(* ================================================================= *)
(*  Initial object                                                   *)
(* ================================================================= *)

Definition empty_setoid : Setoid :=
  mkSetoid Empty_set (fun _ _ => True)
    (fun _ => I) (fun _ _ _ => I) (fun _ _ _ _ _ => I).

Lemma setoid_initial : is_initial SetoidCat empty_setoid.
Proof.
  intro B.
  exists (mkSetoidMor empty_setoid B
            (fun x : Empty_set => match x with end)
            (fun x : Empty_set => match x with end)).
  intro g. intro x. destruct x.
Qed.

(* ================================================================= *)
(*  Binary coproduct                                                 *)
(* ================================================================= *)

Definition sum_rel (A B : Setoid) (p q : st_carrier A + st_carrier B) : Prop :=
  match p, q with
  | inl a, inl a' => st_eq a a'
  | inr b, inr b' => st_eq b b'
  | _, _ => False
  end.

Definition sum_setoid (A B : Setoid) : Setoid.
Proof.
  refine (mkSetoid (st_carrier A + st_carrier B) (sum_rel A B) _ _ _).
  - intros [a|b]; simpl; apply st_refl.
  - intros [a|b] [a'|b'] H; simpl in *; try contradiction; apply st_sym; exact H.
  - intros [a|b] [a'|b'] [a''|b''] H1 H2; simpl in *; try contradiction;
      apply (st_trans H1 H2).
Defined.

Definition inl_mor (A B : Setoid) : SetoidMor A (sum_setoid A B) :=
  mkSetoidMor A (sum_setoid A B) (fun a => inl a) (fun a a' H => H).

Definition inr_mor (A B : Setoid) : SetoidMor B (sum_setoid A B) :=
  mkSetoidMor B (sum_setoid A B) (fun b => inr b) (fun b b' H => H).

(** The comediator [f,g] : A + B -> C *)
Definition sum_copair (C A B : Setoid)
  (f : SetoidMor A C) (g : SetoidMor B C) : SetoidMor (sum_setoid A B) C.
Proof.
  refine (mkSetoidMor (sum_setoid A B) C
    (fun p => match p with inl a => sm_map f a | inr b => sm_map g b end) _).
  intros [a|b] [a'|b'] H; simpl in *; try contradiction.
  - apply (sm_resp f H).
  - apply (sm_resp g H).
Defined.

(* ----- universal property ----- *)

(** [f,g] . inl = f *)
Lemma coprod_beta1 : forall (C A B : Setoid)
  (f : SetoidMor A C) (g : SetoidMor B C),
  cat_mor_eq SetoidCat A C
    (cat_comp SetoidCat A (sum_setoid A B) C (sum_copair C A B f g) (inl_mor A B))
    f.
Proof.
  intros C A B f g. intro a. simpl. apply st_refl.
Qed.

(** [f,g] . inr = g *)
Lemma coprod_beta2 : forall (C A B : Setoid)
  (f : SetoidMor A C) (g : SetoidMor B C),
  cat_mor_eq SetoidCat B C
    (cat_comp SetoidCat B (sum_setoid A B) C (sum_copair C A B f g) (inr_mor A B))
    g.
Proof.
  intros C A B f g. intro b. simpl. apply st_refl.
Qed.

(** Uniqueness: any m with m.inl = f and m.inr = g equals [f,g] *)
Lemma coprod_unique : forall (C A B : Setoid)
  (f : SetoidMor A C) (g : SetoidMor B C) (m : SetoidMor (sum_setoid A B) C),
  cat_mor_eq SetoidCat A C (cat_comp SetoidCat A (sum_setoid A B) C m (inl_mor A B)) f ->
  cat_mor_eq SetoidCat B C (cat_comp SetoidCat B (sum_setoid A B) C m (inr_mor A B)) g ->
  cat_mor_eq SetoidCat (sum_setoid A B) C m (sum_copair C A B f g).
Proof.
  intros C A B f g m H1 H2. intro p. destruct p as [a|b]; simpl.
  - exact (H1 a).
  - exact (H2 b).
Qed.

(* ================================================================= *)
(*  Summary: 4 Qed, 0 Admitted, 0 axioms                            *)
(*    setoid_initial, coprod_beta1, coprod_beta2, coprod_unique      *)
(*    (empty_setoid, sum_setoid, inl_mor, inr_mor, sum_copair defs)  *)
(* ================================================================= *)
