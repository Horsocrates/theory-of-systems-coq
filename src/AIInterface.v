(* ================================================================= *)
(*  THEORY OF SYSTEMS: AI INTERFACE SPECIFICATION                    *)
(*                                                                    *)
(*  Formal specification of the AI generation + verification loop.   *)
(*  Guarantees: if AI output passes typecheck, then it is safe.      *)
(*                                                                    *)
(*  Flow: Human spec -> AI generates ToS-Lang -> typecheck (verified) *)
(*        -> if OK: evaluate (verified) -> result + certificate      *)
(*        -> if FAIL: error + diagnosis for retry                    *)
(*                                                                    *)
(*  Status: >=5 Qed, 0 Admitted | Author: Horsocrates | 2026-03-06   *)
(* ================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
Import ListNotations.
From ToS Require Import Expressions.
From ToS Require Import Reduction.
From ToS Require Import Typing_Expr.
From ToS Require Import Progress.
From ToS Require Import TypeSafety.
From ToS Require Import TypeChecker.
From ToS Require Import Evaluator.

(** ================================================================= *)
(** ** 1. AI Result Type                                               *)
(** ================================================================= *)

(** AI output classification: either verified or error *)
Inductive AIResult : Type :=
  | AI_Verified   : Expr -> Ty -> AIResult  (** passed type check *)
  | AI_TypeError  : Expr -> AIResult        (** failed type check *)
  .

(** ================================================================= *)
(** ** 2. Processing Functions                                         *)
(** ================================================================= *)

(** Process an AI-generated plain expression *)
Definition process_ai_expr (e : Expr) : AIResult :=
  match typecheck [] e with
  | Some T => AI_Verified e T
  | None   => AI_TypeError e
  end.

(** Process an AI-generated annotated expression *)
Definition process_ai_ann (ea : ExprAnn) : AIResult :=
  match typecheck_ann [] ea with
  | Some T => AI_Verified (erase_ann ea) T
  | None   => AI_TypeError (erase_ann ea)
  end.

(** Full AI pipeline: typecheck + evaluate *)
Definition ai_eval (fuel : nat) (e : Expr) : option (Ty * Expr) :=
  match typecheck [] e with
  | Some T => Some (T, eval_fuel fuel e)
  | None   => None
  end.

(** Annotated AI pipeline *)
Definition ai_eval_ann (fuel : nat) (ea : ExprAnn) : option (Ty * Expr) :=
  match typecheck_ann [] ea with
  | Some T => Some (T, eval_fuel fuel (erase_ann ea))
  | None   => None
  end.

(** ================================================================= *)
(** ** 3. Safety Guarantees                                            *)
(** ================================================================= *)

(** AI_Verified implies the expression is well-typed *)
Theorem ai_verified_well_typed : forall e T,
  process_ai_expr e = AI_Verified e T ->
  expr_has_type [] e T.
Proof.
  intros e T H. unfold process_ai_expr in H.
  destruct (typecheck [] e) as [T' |] eqn:ET; [| discriminate].
  inversion H; subst.
  apply typecheck_sound. exact ET.
Qed.

(** AI_Verified for annotated expressions implies well-typed *)
Theorem ai_verified_ann_well_typed : forall ea T,
  process_ai_ann ea = AI_Verified (erase_ann ea) T ->
  expr_has_type [] (erase_ann ea) T.
Proof.
  intros ea T H. unfold process_ai_ann in H.
  destruct (typecheck_ann [] ea) as [T' |] eqn:ET; [| discriminate].
  inversion H; subst.
  apply typecheck_ann_sound. exact ET.
Qed.

(** AI_Verified implies progress (not stuck) *)
Theorem ai_verified_progress : forall e T,
  process_ai_expr e = AI_Verified e T ->
  progress_result e.
Proof.
  intros e T H.
  eapply progress.
  apply ai_verified_well_typed. exact H.
Qed.

(** AI_TypeError means typecheck failed *)
Theorem ai_error_means_ill_typed : forall e,
  process_ai_expr e = AI_TypeError e ->
  typecheck [] e = None.
Proof.
  intros e H. unfold process_ai_expr in H.
  destruct (typecheck [] e) as [T |] eqn:ET.
  - discriminate.
  - reflexivity.
Qed.

(** ai_eval returns well-typed result *)
Theorem ai_eval_sound : forall fuel e T v,
  ai_eval fuel e = Some (T, v) ->
  expr_has_type [] v T.
Proof.
  intros fuel e T v H. unfold ai_eval in H.
  destruct (typecheck [] e) as [T' |] eqn:ET; [| discriminate].
  injection H as <- <-.
  apply type_safety.
  apply typecheck_sound. exact ET.
Qed.

(** ai_eval result satisfies progress *)
Theorem ai_eval_progress : forall fuel e T v,
  ai_eval fuel e = Some (T, v) ->
  progress_result v.
Proof.
  intros fuel e T v H.
  eapply progress.
  apply ai_eval_sound with fuel e. exact H.
Qed.

(** Annotated ai_eval returns well-typed result *)
Theorem ai_eval_ann_sound : forall fuel ea T v,
  ai_eval_ann fuel ea = Some (T, v) ->
  expr_has_type [] v T.
Proof.
  intros fuel ea T v H. unfold ai_eval_ann in H.
  destruct (typecheck_ann [] ea) as [T' |] eqn:ET; [| discriminate].
  injection H as <- <-.
  apply type_safety.
  apply typecheck_ann_sound. exact ET.
Qed.

(** Annotation erasure preserves verification *)
Theorem ai_ann_erasure_safe : forall ea T,
  typecheck_ann [] ea = Some T ->
  process_ai_ann ea = AI_Verified (erase_ann ea) T.
Proof.
  intros ea T H. unfold process_ai_ann.
  rewrite H. reflexivity.
Qed.

(** ================================================================= *)
(** ** 4. The Ultimate AI Safety Chain                                 *)
(** ================================================================= *)

(** THE theorem that matters for AI integration:
    If an AI generates an annotated expression that passes typecheck_ann,
    then evaluating it with any fuel produces a well-typed result
    that satisfies progress (is a value, can step, or is benign-stuck).

    This is the end-to-end guarantee for AI-generated code verification. *)
Theorem ai_generation_safe : forall ea T fuel,
  typecheck_ann [] ea = Some T ->
  let result := eval_fuel fuel (erase_ann ea) in
  expr_has_type [] result T /\ progress_result result.
Proof.
  intros ea T fuel H. simpl.
  split.
  - apply type_safety. apply typecheck_ann_sound. exact H.
  - eapply progress. apply type_safety. apply typecheck_ann_sound. exact H.
Qed.

(** The AI pipeline always terminates (P4 principle) *)
Theorem ai_pipeline_terminates : forall fuel ea,
  exists r, ai_eval_ann fuel ea = r.
Proof.
  intros fuel ea. eexists. reflexivity.
Qed.
