(* ================================================================= *)
(*  ToS-Lang Pretty Printer                                          *)
(*                                                                    *)
(*  Converts extracted Coq types (Ty, Expr, ExprAnn, EvalResult)     *)
(*  back to human-readable strings.                                   *)
(*                                                                    *)
(*  Author: Horsocrates | 2026-03-06                                  *)
(* ================================================================= *)

open UniversePolymorphism
open Typing_Expr
open Expressions
open TypeChecker
open Evaluator

(* ================================================================= *)
(* 1. Level printing                                                  *)
(* ================================================================= *)

let rec print_level = function
  | L1    -> "L1"
  | LS l  -> "L" ^ string_of_int (1 + level_depth l)
and level_depth = function
  | L1   -> 1
  | LS l -> 1 + level_depth l

(* ================================================================= *)
(* 2. Type printing                                                   *)
(* ================================================================= *)

let rec print_ty = function
  | TyNat          -> "Nat"
  | TySystem l     -> "System " ^ print_level l
  | TyArrow (a, b) -> paren_arrow a ^ " -> " ^ print_ty b
  | TyPair (a, b)  -> print_ty a ^ " * " ^ print_ty b
  | TyProcess t    -> "Process " ^ print_ty_atom t
  | TyLayer t      -> "Layer " ^ print_ty_atom t

and print_ty_atom = function
  | TyNat          -> "Nat"
  | TySystem l     -> "System " ^ print_level l
  | t              -> "(" ^ print_ty t ^ ")"

and paren_arrow = function
  | TyArrow _ as t -> "(" ^ print_ty t ^ ")"
  | t              -> print_ty t

(* ================================================================= *)
(* 3. Expression printing                                             *)
(* ================================================================= *)

let rec print_expr = function
  | EConst n          -> string_of_int n
  | EVar x            -> "v" ^ string_of_int x
  | ESystem l         -> "system " ^ print_level l
  | EElem e           -> "elem(" ^ print_expr e ^ ")"
  | ELam body         -> "\\. " ^ print_expr body
  | EApp (f, a)       -> print_app f ^ " " ^ print_expr_atom a
  | EPair (a, b)      -> "(" ^ print_expr a ^ ", " ^ print_expr b ^ ")"
  | EFst e            -> "fst " ^ print_expr_atom e
  | ESnd e            -> "snd " ^ print_expr_atom e
  | EObserve (e, n)   -> "observe " ^ print_expr_atom e ^ " " ^ string_of_int n
  | EResolve e        -> "resolve " ^ print_expr_atom e
  | ELayerProject (e, l) -> "project " ^ print_expr_atom e ^ " through " ^ print_expr_atom l
  | EConst n          -> string_of_int n

and print_expr_atom = function
  | EConst n  -> string_of_int n
  | EVar x    -> "v" ^ string_of_int x
  | e         -> "(" ^ print_expr e ^ ")"

and print_app = function
  | EApp (f, a) -> print_app f ^ " " ^ print_expr_atom a
  | e           -> print_expr_atom e

(* ================================================================= *)
(* 4. Annotated expression printing                                   *)
(* ================================================================= *)

let rec print_expr_ann = function
  | EAConst n            -> string_of_int n
  | EAVar x              -> "v" ^ string_of_int x
  | EASystem l           -> "system " ^ print_level l
  | EALamAnn (ty, body)  -> "\\(x : " ^ print_ty ty ^ "). " ^ print_expr_ann body
  | EAApp (f, a)         -> print_app_ann f ^ " " ^ print_expr_ann_atom a
  | EAPair (a, b)        -> "(" ^ print_expr_ann a ^ ", " ^ print_expr_ann b ^ ")"
  | EAFst e              -> "fst " ^ print_expr_ann_atom e
  | EASnd e              -> "snd " ^ print_expr_ann_atom e
  | EAObserve (e, n)     -> "observe " ^ print_expr_ann_atom e ^ " " ^ string_of_int n
  | EAResolve e          -> "resolve " ^ print_expr_ann_atom e

and print_expr_ann_atom = function
  | EAConst n  -> string_of_int n
  | EAVar x    -> "v" ^ string_of_int x
  | e          -> "(" ^ print_expr_ann e ^ ")"

and print_app_ann = function
  | EAApp (f, a) -> print_app_ann f ^ " " ^ print_expr_ann_atom a
  | e            -> print_expr_ann_atom e

(* ================================================================= *)
(* 5. Evaluation result printing                                      *)
(* ================================================================= *)

let print_eval_result = function
  | ER_Value (v, t) ->
      "Value: " ^ print_expr v ^ "\n" ^
      "Type:  " ^ print_ty t ^ "\n" ^
      "Certificate: well-typed, E/R/R well-formed, no paradox (Coq-proven)"
  | ER_Partial (e, t) ->
      "Partial (fuel exhausted): " ^ print_expr e ^ "\n" ^
      "Type (preserved): " ^ print_ty t
  | ER_TypeError ->
      "Type error: expression is ill-typed"
