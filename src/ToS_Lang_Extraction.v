(* ================================================================= *)
(*  THEORY OF SYSTEMS: ToS-Lang EXTRACTION                           *)
(*                                                                    *)
(*  Extracts verified type checker + evaluator to OCaml.             *)
(*  These OCaml functions are PROVEN CORRECT by Coq proofs.          *)
(*                                                                    *)
(*  Status: 6 Qed, 0 Admitted | Author: Horsocrates | 2026-03-06     *)
(* ================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
Import ListNotations.

From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import Expressions.
From ToS Require Import Reduction.
From ToS Require Import Typing_Expr.
From ToS Require Import TypeChecker.
From ToS Require Import Evaluator.

(** ================================================================= *)
(** ** 1. Type Extraction Mappings                                     *)
(** ================================================================= *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive nat => "int" [ "0" "succ"  ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".

(** ================================================================= *)
(** ** 2. Domain-Specific Type Extraction                              *)
(** ================================================================= *)

Extract Inductive Level => "level" [ "L1" "LS" ].

Extract Inductive Ty => "ty" [
  "TyNat" "TySystem" "TyArrow" "TyPair" "TyProcess" "TyLayer"
].

Extract Inductive Expr => "expr" [
  "EVar" "ESystem" "EElem" "EApp" "ELam" "EPair" "EFst" "ESnd"
  "EObserve" "EResolve" "ELayerProject" "EConst"
].

Extract Inductive ExprAnn => "expr_ann" [
  "EAVar" "EAConst" "EASystem" "EALamAnn" "EAApp" "EAPair"
  "EAFst" "EASnd" "EAObserve" "EAResolve"
].

Extract Inductive EvalResult => "eval_result" [
  "ER_Value" "ER_Partial" "ER_TypeError"
].

(** ================================================================= *)
(** ** 3. Main Extraction Directives                                   *)
(** ================================================================= *)

Separate Extraction

  (* === Types === *)
  Ty Expr ExprAnn Level EvalResult

  (* === Type checker (VERIFIED — typecheck_sound proven) === *)
  typecheck typecheck_ann ty_eq_dec

  (* === Evaluator (VERIFIED — eval_fuel_preservation proven) === *)
  eval_fuel try_step safe_eval classify_eval typecheck_and_eval
  safe_eval_ann

  (* === Expression utilities === *)
  erase_ann subst shift is_value_dec expr_eq_dec
.

(** ================================================================= *)
(** ** 4. Extraction Validation Lemmas                                 *)
(** ================================================================= *)

(** Computability rendered honestly (June 2026): the former lemmas here
    were the vacuous `exists r, f x = r` — provable for ANY function by
    `eexists; reflexivity`, hence stating nothing. What IS observable in
    the object logic is the CONSTRUCTOR DICHOTOMY of each result type:
    option lands in None-or-Some, EvalResult in one of its three
    constructors, expression size in a successor, valuehood is decidable. *)
Lemma extraction_typecheck_computable : forall Gamma e,
  typecheck Gamma e = None \/ exists T, typecheck Gamma e = Some T.
Proof.
  intros Gamma e. destruct (typecheck Gamma e) as [T |].
  - right. exists T. reflexivity.
  - left. reflexivity.
Qed.

Lemma extraction_typecheck_ann_computable : forall Gamma ea,
  typecheck_ann Gamma ea = None \/ exists T, typecheck_ann Gamma ea = Some T.
Proof.
  intros Gamma ea. destruct (typecheck_ann Gamma ea) as [T |].
  - right. exists T. reflexivity.
  - left. reflexivity.
Qed.

Lemma extraction_eval_computable : forall fuel e,
  is_value (eval_fuel fuel e) \/ ~ is_value (eval_fuel fuel e).
Proof.
  intros fuel e.
  destruct (is_value_dec (eval_fuel fuel e)) as [Hv | Hnv].
  - left. exact Hv.
  - right. exact Hnv.
Qed.

Lemma extraction_classify_computable : forall fuel e,
  (exists v T, classify_eval fuel e = ER_Value v T) \/
  (exists v T, classify_eval fuel e = ER_Partial v T) \/
  classify_eval fuel e = ER_TypeError.
Proof.
  intros fuel e. destruct (classify_eval fuel e) as [v T | v T |].
  - left. exists v, T. reflexivity.
  - right. left. exists v, T. reflexivity.
  - right. right. reflexivity.
Qed.

Lemma extraction_safe_eval_computable : forall fuel e,
  safe_eval fuel e = None \/ exists v, safe_eval fuel e = Some v.
Proof.
  intros fuel e. destruct (safe_eval fuel e) as [v |].
  - right. exists v. reflexivity.
  - left. reflexivity.
Qed.

Lemma extraction_erase_computable : forall ea,
  exists n, expr_size (erase_ann ea) = S n.
Proof.
  intros ea. apply expr_finite.
Qed.

(** Structural recursion: all extracted functions are structurally
    recursive; Coq's termination checker certifies this at Fixpoint
    definition time and it needs no in-logic restatement.
    (June 2026: the two former "documentation lemmas" restating this as
    the vacuous `exists r, f x = r` were removed — vacuity documents
    nothing.) *)

(** ================================================================= *)
(** ** 5. Extraction Notes                                             *)
(** ================================================================= *)

(**
  EXTRACTION NOTES
  =================

  1. Prop fields are erased:
     - expr_has_type (typing relation) -> erased entirely
     - is_value (value predicate as Prop) -> erased
     - is_value_dec (decidable is_value) -> kept (returns bool)
     - ty_eq_dec (type equality) -> kept (returns bool)

  2. The following functions are extraction-safe (no axioms in
     computational path):
     - typecheck : TyCtx -> Expr -> option Ty
     - typecheck_ann : TyCtx -> ExprAnn -> option Ty
     - eval_fuel : nat -> Expr -> Expr
     - try_step : Expr -> option Expr
     - safe_eval : nat -> Expr -> option Expr
     - classify_eval : nat -> Expr -> EvalResult
     - erase_ann : ExprAnn -> Expr
     - subst, shift : de Bruijn operations

  3. Output structure:
     tos_lang/TypeChecker.ml   -- verified type checker
     tos_lang/Evaluator.ml     -- verified evaluator
     tos_lang/Expressions.ml   -- expression types + operations

  4. Verified guarantee chain:
     typecheck_sound -> type_safety -> tos_lang_main_theorem
     "If typecheck says OK, evaluation preserves types and
      the result satisfies progress."
*)
