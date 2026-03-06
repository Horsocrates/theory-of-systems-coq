open Expressions
open Reduction
open TypeChecker
open Typing_Expr

val safe_eval : int -> expr -> expr option

val typecheck_and_eval : coq_TyCtx -> int -> expr -> (ty * expr) option

val classify_eval : int -> expr -> eval_result

val safe_eval_ann : int -> expr_ann -> expr option
