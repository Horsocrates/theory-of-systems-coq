(* ================================================================= *)
(*  THEORY OF SYSTEMS: VERIFIED EVALUATOR                            *)
(*                                                                    *)
(*  Wraps eval_fuel with type checking for safe evaluation.          *)
(*  Proves that the complete pipeline preserves types and safety.    *)
(*                                                                    *)
(*  Status: >=15 Qed, 0 Admitted | Author: Horsocrates | 2026-03-06  *)
(* ================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
Import ListNotations.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import Expressions.
From ToS Require Import Reduction.
From ToS Require Import Typing_Expr.
From ToS Require Import SubjectReduction.
From ToS Require Import Progress.
From ToS Require Import TypeSafety.
From ToS Require Import TypeChecker.

(** ================================================================= *)
(** ** 1. Safe Evaluation Pipeline                                     *)
(** ================================================================= *)

(** safe_eval: only evaluates expressions that pass type checking.
    Returns None if typecheck fails, Some result otherwise. *)
Definition safe_eval (fuel : nat) (e : Expr) : option Expr :=
  match typecheck [] e with
  | Some _ => Some (eval_fuel fuel e)
  | None   => None
  end.

(** typecheck_and_eval: returns both the type and evaluation result. *)
Definition typecheck_and_eval (Gamma : TyCtx) (fuel : nat) (e : Expr)
  : option (Ty * Expr) :=
  match typecheck Gamma e with
  | Some T => Some (T, eval_fuel fuel e)
  | None   => None
  end.

(** ================================================================= *)
(** ** 2. Evaluation Result Classification                             *)
(** ================================================================= *)

Inductive EvalResult : Type :=
  | ER_Value   : Expr -> Ty -> EvalResult  (** fully evaluated to value *)
  | ER_Partial : Expr -> Ty -> EvalResult  (** fuel exhausted, partial *)
  | ER_TypeError : EvalResult              (** type check failed *)
  .

(** classify_eval: type-check, evaluate, classify the result. *)
Definition classify_eval (fuel : nat) (e : Expr) : EvalResult :=
  match typecheck [] e with
  | None   => ER_TypeError
  | Some T =>
      let result := eval_fuel fuel e in
      match is_value_dec result with
      | left  _ => ER_Value result T
      | right _ => ER_Partial result T
      end
  end.

(** ================================================================= *)
(** ** 3. Soundness Theorems                                           *)
(** ================================================================= *)

(** safe_eval returns a well-typed result *)
Theorem safe_eval_sound : forall fuel e v,
  safe_eval fuel e = Some v ->
  exists T, expr_has_type [] e T /\ expr_has_type [] v T.
Proof.
  intros fuel e v H. unfold safe_eval in H.
  destruct (typecheck [] e) as [T |] eqn:ET; [| discriminate].
  injection H as <-.
  exists T. split.
  - apply typecheck_sound. exact ET.
  - apply type_safety. apply typecheck_sound. exact ET.
Qed.

(** safe_eval result satisfies progress (value or can step or benign) *)
Theorem safe_eval_safe : forall fuel e v,
  safe_eval fuel e = Some v ->
  exists T, expr_has_type [] v T /\ progress_result v.
Proof.
  intros fuel e v H.
  destruct (safe_eval_sound fuel e v H) as [T [_ Htyped]].
  exists T. split.
  - exact Htyped.
  - eapply progress. exact Htyped.
Qed.

(** typecheck_and_eval returns correct type and value *)
Theorem typecheck_and_eval_sound : forall Gamma fuel e T v,
  typecheck_and_eval Gamma fuel e = Some (T, v) ->
  typecheck Gamma e = Some T /\ v = eval_fuel fuel e.
Proof.
  intros Gamma fuel e T v H. unfold typecheck_and_eval in H.
  destruct (typecheck Gamma e) as [T' |] eqn:ET; [| discriminate].
  injection H as <- <-.
  split; reflexivity.
Qed.

(** ================================================================= *)
(** ** 4. Classification Correctness                                   *)
(** ================================================================= *)

(** ER_Value means: is_value, well-typed, and equals eval_fuel result *)
Theorem classify_value_correct : forall fuel e v T,
  classify_eval fuel e = ER_Value v T ->
  is_value v /\ expr_has_type [] v T /\ v = eval_fuel fuel e.
Proof.
  intros fuel e v T H. unfold classify_eval in H.
  destruct (typecheck [] e) as [T' |] eqn:ET; [| discriminate].
  destruct (is_value_dec (eval_fuel fuel e)) as [Hv | Hnv]; [| discriminate].
  injection H as <- <-.
  repeat split.
  - exact Hv.
  - apply type_safety. apply typecheck_sound. exact ET.
Qed.

(** ER_Partial means: not a value, but still well-typed *)
Theorem classify_partial_correct : forall fuel e v T,
  classify_eval fuel e = ER_Partial v T ->
  ~ is_value v /\ expr_has_type [] v T /\ v = eval_fuel fuel e.
Proof.
  intros fuel e v T H. unfold classify_eval in H.
  destruct (typecheck [] e) as [T' |] eqn:ET; [| discriminate].
  destruct (is_value_dec (eval_fuel fuel e)) as [Hv | Hnv]; [discriminate |].
  injection H as <- <-.
  repeat split.
  - exact Hnv.
  - apply type_safety. apply typecheck_sound. exact ET.
Qed.

(** ER_TypeError means: typecheck returned None *)
Theorem classify_error_correct : forall fuel e,
  classify_eval fuel e = ER_TypeError ->
  typecheck [] e = None.
Proof.
  intros fuel e H. unfold classify_eval in H.
  destruct (typecheck [] e) as [T |] eqn:ET.
  - destruct (is_value_dec (eval_fuel fuel e)); discriminate.
  - reflexivity.
Qed.

(** ================================================================= *)
(** ** 5. Termination and Determinism                                  *)
(** ================================================================= *)

(** safe_eval always returns (it's a total function) *)
Theorem safe_eval_terminates : forall fuel e,
  exists r, safe_eval fuel e = r.
Proof.
  intros fuel e. eexists. reflexivity.
Qed.

(** safe_eval is deterministic *)
Theorem safe_eval_deterministic : forall fuel e r1 r2,
  safe_eval fuel e = r1 ->
  safe_eval fuel e = r2 ->
  r1 = r2.
Proof.
  intros fuel e r1 r2 H1 H2. congruence.
Qed.

(** classify_eval is deterministic *)
Theorem classify_deterministic : forall fuel e r1 r2,
  classify_eval fuel e = r1 ->
  classify_eval fuel e = r2 ->
  r1 = r2.
Proof.
  intros fuel e r1 r2 H1 H2. congruence.
Qed.

(** ================================================================= *)
(** ** 6. Connection Theorems (Phase C bridge)                         *)
(** ================================================================= *)

(** If typecheck succeeds, the expression satisfies progress *)
Theorem typecheck_implies_progress : forall e T,
  typecheck [] e = Some T ->
  progress_result e.
Proof.
  intros e T H.
  eapply progress.
  apply typecheck_sound. exact H.
Qed.

(** If typecheck succeeds, evaluation preserves the type *)
Theorem typecheck_implies_type_safety : forall e T fuel,
  typecheck [] e = Some T ->
  expr_has_type [] (eval_fuel fuel e) T.
Proof.
  intros e T fuel H.
  apply type_safety.
  apply typecheck_sound. exact H.
Qed.

(** If typecheck succeeds, eval result satisfies progress *)
Theorem typecheck_eval_progress : forall e T fuel,
  typecheck [] e = Some T ->
  progress_result (eval_fuel fuel e).
Proof.
  intros e T fuel H.
  eapply progress.
  apply typecheck_implies_type_safety. exact H.
Qed.

(** ================================================================= *)
(** ** 7. The Verified Pipeline Theorem                                *)
(** ================================================================= *)

(** THE ultimate theorem: if typecheck succeeds, then for any fuel:
    (a) the evaluation result has the same type, AND
    (b) the result satisfies progress (value / can step / benign). *)
Theorem verified_pipeline : forall e T fuel,
  typecheck [] e = Some T ->
  let result := eval_fuel fuel e in
  expr_has_type [] result T /\ progress_result result.
Proof.
  intros e T fuel H. simpl.
  split.
  - apply typecheck_implies_type_safety. exact H.
  - apply typecheck_eval_progress with T. exact H.
Qed.

(** The verified pipeline always terminates (P4 principle). *)
Theorem verified_pipeline_terminates : forall e fuel,
  exists v, eval_fuel fuel e = v.
Proof.
  intros e fuel. eexists. reflexivity.
Qed.

(** The verified pipeline is deterministic. *)
Theorem verified_pipeline_deterministic : forall e fuel v1 v2,
  eval_fuel fuel e = v1 ->
  eval_fuel fuel e = v2 ->
  v1 = v2.
Proof.
  intros e fuel v1 v2 H1 H2. congruence.
Qed.

(** ================================================================= *)
(** ** 8. Annotated Pipeline (typecheck_ann + eval)                    *)
(** ================================================================= *)

(** Full pipeline for annotated expressions *)
Definition safe_eval_ann (fuel : nat) (ea : ExprAnn) : option Expr :=
  match typecheck_ann [] ea with
  | Some _ => Some (eval_fuel fuel (erase_ann ea))
  | None   => None
  end.

(** Annotated safe_eval returns well-typed result *)
Theorem safe_eval_ann_sound : forall fuel ea v,
  safe_eval_ann fuel ea = Some v ->
  exists T, expr_has_type [] (erase_ann ea) T /\ expr_has_type [] v T.
Proof.
  intros fuel ea v H. unfold safe_eval_ann in H.
  destruct (typecheck_ann [] ea) as [T |] eqn:ET; [| discriminate].
  injection H as <-.
  exists T. split.
  - apply typecheck_ann_sound. exact ET.
  - apply type_safety. apply typecheck_ann_sound. exact ET.
Qed.

(** Annotated safe_eval satisfies progress *)
Theorem safe_eval_ann_safe : forall fuel ea v,
  safe_eval_ann fuel ea = Some v ->
  exists T, expr_has_type [] v T /\ progress_result v.
Proof.
  intros fuel ea v H.
  destruct (safe_eval_ann_sound fuel ea v H) as [T [_ Htyped]].
  exists T. split.
  - exact Htyped.
  - eapply progress. exact Htyped.
Qed.

(** ================================================================= *)
(** ** 9. Additional Properties                                        *)
(** ================================================================= *)

(** Typecheck + eval for annotated: both type and result correct *)
Theorem typecheck_ann_eval_sound : forall fuel ea T,
  typecheck_ann [] ea = Some T ->
  expr_has_type [] (eval_fuel fuel (erase_ann ea)) T.
Proof.
  intros fuel ea T H.
  apply type_safety.
  apply typecheck_ann_sound. exact H.
Qed.

(** Values are fixed points of eval *)
Theorem eval_value_fixed : forall fuel v,
  is_value v -> eval_fuel fuel v = v.
Proof.
  intros fuel v Hv.
  apply eval_fuel_value. exact Hv.
Qed.

(** Multi-step from Phase C implies same type *)
Theorem multi_step_type_preservation : forall e e' T,
  typecheck [] e = Some T ->
  multi_step e e' ->
  expr_has_type [] e' T.
Proof.
  intros e e' T Hcheck Hms.
  apply multi_step_preservation with e.
  - apply typecheck_sound. exact Hcheck.
  - exact Hms.
Qed.
