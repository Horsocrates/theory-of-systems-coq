(* ================================================================= *)
(*  ToS-Lang DEMO — Verified Type Checker + Evaluator in Action      *)
(*                                                                    *)
(*  Every Eval compute result below is produced by Coq's kernel.     *)
(*  The type checker and evaluator are PROVEN CORRECT:                *)
(*    typecheck_sound, verified_pipeline, ai_generation_safe          *)
(*                                                                    *)
(*  Author: Horsocrates | 2026-03-06                                  *)
(* ================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
Import ListNotations.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import Expressions.
From ToS Require Import Reduction.
From ToS Require Import Typing_Expr.
From ToS Require Import TypeChecker.
From ToS Require Import Evaluator.

(** ================================================================= *)
(** ** TEST 1: Identity function applied to 42                         *)
(**    (\x:Nat. x) 42  -->  42                                         *)
(** ================================================================= *)

(* Type check (annotated expression) *)
Eval compute in
  typecheck_ann [] (EAApp (EALamAnn TyNat (EAVar 0)) (EAConst 42)).
(* Expected: = Some TyNat *)

(* Erase annotations and evaluate *)
Eval compute in
  eval_fuel 100 (erase_ann (EAApp (EALamAnn TyNat (EAVar 0)) (EAConst 42))).
(* Expected: = EConst 42 *)

(* Note: classify_eval uses typecheck (not typecheck_ann), which returns
   None for ELam (no annotation). Use classify_eval on lambda-free expressions.
   See TEST 10 for classify_eval demo. *)

(** ================================================================= *)
(** ** TEST 2: Pair and first projection                                *)
(**    fst (42, 7)  -->  42                                            *)
(** ================================================================= *)

Eval compute in
  typecheck [] (EFst (EPair (EConst 42) (EConst 7))).
(* Expected: = Some TyNat *)

Eval compute in
  eval_fuel 100 (EFst (EPair (EConst 42) (EConst 7))).
(* Expected: = EConst 42 *)

(** ================================================================= *)
(** ** TEST 3: Pair and second projection                               *)
(**    snd (1, 2)  -->  2                                              *)
(** ================================================================= *)

Eval compute in
  typecheck [] (ESnd (EPair (EConst 1) (EConst 2))).
(* Expected: = Some TyNat *)

Eval compute in
  eval_fuel 100 (ESnd (EPair (EConst 1) (EConst 2))).
(* Expected: = EConst 2 *)

(** ================================================================= *)
(** ** TEST 4: Nested application                                      *)
(**    (\f:Nat->Nat. \x:Nat. f x) (\n:Nat. n) 5  -->  5              *)
(** ================================================================= *)

Eval compute in
  let id := EALamAnn TyNat (EAVar 0) in
  let apply_f := EALamAnn (TyArrow TyNat TyNat)
                   (EALamAnn TyNat (EAApp (EAVar 1) (EAVar 0))) in
  typecheck_ann [] (EAApp (EAApp apply_f id) (EAConst 5)).
(* Expected: = Some TyNat *)

Eval compute in
  let id := EALamAnn TyNat (EAVar 0) in
  let apply_f := EALamAnn (TyArrow TyNat TyNat)
                   (EALamAnn TyNat (EAApp (EAVar 1) (EAVar 0))) in
  eval_fuel 100 (erase_ann (EAApp (EAApp apply_f id) (EAConst 5))).
(* Expected: = EConst 5 *)

(** ================================================================= *)
(** ** TEST 5: Type error detection                                    *)
(**    fst 42  -->  None (42 is not a pair)                            *)
(** ================================================================= *)

Eval compute in
  typecheck [] (EFst (EConst 42)).
(* Expected: = None — type error correctly caught *)

(** ================================================================= *)
(** ** TEST 6: L5 Resolution                                           *)
(**    resolve (const 42)  -->  42                                     *)
(** ================================================================= *)

Eval compute in
  typecheck [] (EResolve (EConst 42)).
(* Expected: = Some TyNat *)

Eval compute in
  eval_fuel 100 (EResolve (EConst 42)).
(* Expected: = EConst 42 *)

(** ================================================================= *)
(** ** TEST 7: Process observation — type error                        *)
(**    observe (const 0) 5  -->  None (EConst is TyNat, not TyProcess) *)
(** ================================================================= *)

Eval compute in
  typecheck [] (EObserve (EConst 0) 5).
(* Expected: = None — EConst has type TyNat, not TyProcess *)
(* This is correct: type checker correctly requires process type *)

(** The evaluator still evaluates observations directly: *)
Eval compute in
  eval_fuel 100 (EObserve (EConst 0) 5).
(* Expected: = EConst 5 — reduction fires on any value *)

(** ================================================================= *)
(** ** TEST 8: Nested pair with double projection                      *)
(**    fst (fst ((1, 2), 3))  -->  1                                   *)
(** ================================================================= *)

Eval compute in
  typecheck [] (EFst (EFst (EPair (EPair (EConst 1) (EConst 2)) (EConst 3)))).
(* Expected: = Some TyNat *)

Eval compute in
  eval_fuel 100 (EFst (EFst (EPair (EPair (EConst 1) (EConst 2)) (EConst 3)))).
(* Expected: = EConst 1 *)

(** ================================================================= *)
(** ** TEST 9: Swap pair components                                    *)
(**    (\p:Nat*Nat. (snd p, fst p)) (42, 7)  -->  (7, 42)            *)
(** ================================================================= *)

Eval compute in
  let swap := EALamAnn (TyPair TyNat TyNat)
                (EAPair (EASnd (EAVar 0)) (EAFst (EAVar 0))) in
  typecheck_ann [] (EAApp swap (EAPair (EAConst 42) (EAConst 7))).
(* Expected: = Some (TyPair TyNat TyNat) *)

Eval compute in
  let swap := EALamAnn (TyPair TyNat TyNat)
                (EAPair (EASnd (EAVar 0)) (EAFst (EAVar 0))) in
  eval_fuel 100 (erase_ann (EAApp swap (EAPair (EAConst 42) (EAConst 7)))).
(* Expected: = EPair (EConst 7) (EConst 42) *)

(** ================================================================= *)
(** ** TEST 10: Constant (simplest case)                               *)
(** ================================================================= *)

Eval compute in typecheck [] (EConst 42).
(* Expected: = Some TyNat *)

Eval compute in eval_fuel 100 (EConst 42).
(* Expected: = EConst 42 *)

Eval compute in classify_eval 100 (EConst 42).
(* Expected: = ER_Value (EConst 42) TyNat *)

(** ================================================================= *)
(** ** CERTIFICATE CHAIN                                                *)
(**                                                                     *)
(**  For every test above where typecheck returns Some T:               *)
(**    1. typecheck_sound: typecheck G e = Some T → expr_has_type G e T *)
(**    2. subject_reduction: step preserves types                        *)
(**    3. progress: well-typed ≠ stuck                                   *)
(**    4. type_safety: eval preserves types                              *)
(**    5. verified_pipeline: typecheck OK → eval type-safe + progress    *)
(**    6. ai_generation_safe: end-to-end AI safety guarantee             *)
(** ================================================================= *)
