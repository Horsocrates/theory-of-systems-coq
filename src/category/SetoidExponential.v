(** * SetoidExponential.v — SetoidCat is cartesian closed

    Theory of Systems — Part XIV (Category of Systems), layer src/category/

    Elements: setoid maps A -> B as the points of B^A, evaluation, currying
    Roles:    exp_setoid B^A -> the internal object of maps A -> B;
              setoid_eval -> application; setoid_curry -> abstraction
    Rules:    cartesian closure: the bijection Hom(C x A, B) ~= Hom(C, B^A)
              (beta: eval . <curry h . fst, snd> = h; eta: uniqueness of curry)
    Status:   SetoidCat has exponentials, i.e. is cartesian closed

    P4 diagnostic.  "The object of all functions A -> B" is usually imagined as a
    completed set (cardinality B^|A|).  Here B^A is a setoid with pointwise
    equality — a role-level internal hom, not a cardinal; currying is a RULE, not
    a recount.

    Builds on: stdlib/Category.v, category/SetoidCategory.v, category/SetoidProducts.v.

    STATUS: 2 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import stdlib.Category.
From ToS Require Import category.SetoidCategory.
From ToS Require Import category.SetoidProducts.

(* ================================================================= *)
(*  The exponential setoid B^A = setoid maps with pointwise equality *)
(* ================================================================= *)

Definition exp_setoid (A B : Setoid) : Setoid :=
  mkSetoid (SetoidMor A B) (SetoidMorEq A B)
    (cat_mor_eq_refl SetoidCat A B)
    (cat_mor_eq_sym SetoidCat A B)
    (cat_mor_eq_trans SetoidCat A B).

(** Evaluation  (B^A) x A -> B,  (f,a) |-> f a *)
Definition setoid_eval (A B : Setoid) :
  SetoidMor (prod_setoid (exp_setoid A B) A) B.
Proof.
  refine (mkSetoidMor (prod_setoid (exp_setoid A B) A) B
    (fun p => sm_map (fst p) (snd p)) _).
  intros p q H. simpl in H. destruct H as [Hf Ha].
  apply (st_trans (y := sm_map (fst p) (snd q))).
  - apply (sm_resp (fst p)). exact Ha.
  - exact (Hf (snd q)).
Defined.

(** Partial application  c |-> (a |-> h(c,a)) *)
Definition curry_app (C A B : Setoid) (h : SetoidMor (prod_setoid C A) B)
  (c : st_carrier C) : SetoidMor A B.
Proof.
  refine (mkSetoidMor A B (fun a => sm_map h (c, a)) _).
  intros a a' Ha. apply (sm_resp h). split.
  - apply st_refl.
  - exact Ha.
Defined.

(** Currying  h : C x A -> B   |->   curry h : C -> B^A *)
Definition setoid_curry (C A B : Setoid) (h : SetoidMor (prod_setoid C A) B) :
  SetoidMor C (exp_setoid A B).
Proof.
  refine (mkSetoidMor C (exp_setoid A B) (fun c => curry_app C A B h c) _).
  intros c c' Hcc'. intro a. simpl.
  apply (sm_resp h). split.
  - exact Hcc'.
  - apply st_refl.
Defined.

(* ================================================================= *)
(*  Cartesian closure: the universal property of the exponential     *)
(* ================================================================= *)

(** beta:  eval . <curry h . fst, snd> = h *)
Lemma exp_beta : forall (C A B : Setoid) (h : SetoidMor (prod_setoid C A) B),
  cat_mor_eq SetoidCat (prod_setoid C A) B
    (cat_comp SetoidCat (prod_setoid C A) (prod_setoid (exp_setoid A B) A) B
       (setoid_eval A B)
       (setoid_pair (prod_setoid C A) (exp_setoid A B) A
          (cat_comp SetoidCat (prod_setoid C A) C (exp_setoid A B)
             (setoid_curry C A B h) (setoid_fst C A))
          (setoid_snd C A)))
    h.
Proof.
  intros C A B h. intro p. destruct p as [c a]. simpl. apply st_refl.
Qed.

(** eta / uniqueness: any k whose transpose-back is h equals curry h *)
Lemma exp_unique : forall (C A B : Setoid) (h : SetoidMor (prod_setoid C A) B)
  (k : SetoidMor C (exp_setoid A B)),
  cat_mor_eq SetoidCat (prod_setoid C A) B
    (cat_comp SetoidCat (prod_setoid C A) (prod_setoid (exp_setoid A B) A) B
       (setoid_eval A B)
       (setoid_pair (prod_setoid C A) (exp_setoid A B) A
          (cat_comp SetoidCat (prod_setoid C A) C (exp_setoid A B)
             k (setoid_fst C A))
          (setoid_snd C A)))
    h ->
  cat_mor_eq SetoidCat C (exp_setoid A B) k (setoid_curry C A B h).
Proof.
  intros C A B h k Hk. intro c. intro a. simpl.
  exact (Hk (c, a)).
Qed.

(* ================================================================= *)
(*  Summary: 2 Qed, 0 Admitted, 0 axioms                            *)
(*    exp_beta, exp_unique                                          *)
(*    (exp_setoid, setoid_eval, setoid_curry are definitions)       *)
(* ================================================================= *)
