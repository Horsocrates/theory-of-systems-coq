open Expressions
open Reduction
open TypeChecker
open Typing_Expr

(** val safe_eval : int -> expr -> expr option **)

let safe_eval fuel e =
  match typecheck [] e with
  | Some _ -> Some (eval_fuel fuel e)
  | None -> None

(** val typecheck_and_eval :
    coq_TyCtx -> int -> expr -> (ty * expr) option **)

let typecheck_and_eval gamma fuel e =
  match typecheck gamma e with
  | Some t -> Some (t,(eval_fuel fuel e))
  | None -> None

(** val classify_eval : int -> expr -> eval_result **)

let classify_eval fuel e =
  match typecheck [] e with
  | Some t ->
    let result = eval_fuel fuel e in
    if is_value_dec result
    then ER_Value (result, t)
    else ER_Partial (result, t)
  | None -> ER_TypeError

(** val safe_eval_ann : int -> expr_ann -> expr option **)

let safe_eval_ann fuel ea =
  match typecheck_ann [] ea with
  | Some _ -> Some (eval_fuel fuel (erase_ann ea))
  | None -> None
