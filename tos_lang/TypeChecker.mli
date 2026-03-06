open List
open Typing_Expr

val typecheck : coq_TyCtx -> expr -> ty option

val erase_ann : expr_ann -> expr

val typecheck_ann : coq_TyCtx -> expr_ann -> ty option
