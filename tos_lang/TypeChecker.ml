open List
open Typing_Expr

(** val typecheck : coq_TyCtx -> expr -> ty option **)

let rec typecheck gamma = function
| EVar x -> nth_error gamma x
| ESystem l -> Some (TySystem l)
| EApp (f, a) ->
  (match typecheck gamma f with
   | Some t ->
     (match t with
      | TyArrow (t1, t2) ->
        (match typecheck gamma a with
         | Some t1' -> if ty_eq_dec t1 t1' then Some t2 else None
         | None -> None)
      | _ -> None)
   | None -> None)
| EPair (e1, e2) ->
  (match typecheck gamma e1 with
   | Some t1 ->
     (match typecheck gamma e2 with
      | Some t2 -> Some (TyPair (t1, t2))
      | None -> None)
   | None -> None)
| EFst e0 ->
  (match typecheck gamma e0 with
   | Some t -> (match t with
                | TyPair (t1, _) -> Some t1
                | _ -> None)
   | None -> None)
| ESnd e0 ->
  (match typecheck gamma e0 with
   | Some t -> (match t with
                | TyPair (_, t2) -> Some t2
                | _ -> None)
   | None -> None)
| EObserve (e0, _) ->
  (match typecheck gamma e0 with
   | Some t -> (match t with
                | TyProcess t0 -> Some t0
                | _ -> None)
   | None -> None)
| EResolve e0 -> typecheck gamma e0
| EConst _ -> Some TyNat
| _ -> None

(** val erase_ann : expr_ann -> expr **)

let rec erase_ann = function
| EAVar x -> EVar x
| EAConst n -> EConst n
| EASystem l -> ESystem l
| EALamAnn (_, body) -> ELam (erase_ann body)
| EAApp (f, a) -> EApp ((erase_ann f), (erase_ann a))
| EAPair (e1, e2) -> EPair ((erase_ann e1), (erase_ann e2))
| EAFst e -> EFst (erase_ann e)
| EASnd e -> ESnd (erase_ann e)
| EAObserve (e, n) -> EObserve ((erase_ann e), n)
| EAResolve e -> EResolve (erase_ann e)

(** val typecheck_ann : coq_TyCtx -> expr_ann -> ty option **)

let rec typecheck_ann gamma = function
| EAVar x -> nth_error gamma x
| EAConst _ -> Some TyNat
| EASystem l -> Some (TySystem l)
| EALamAnn (t1, body) ->
  (match typecheck_ann (t1::gamma) body with
   | Some t2 -> Some (TyArrow (t1, t2))
   | None -> None)
| EAApp (f, a) ->
  (match typecheck_ann gamma f with
   | Some t ->
     (match t with
      | TyArrow (t1, t2) ->
        (match typecheck_ann gamma a with
         | Some t1' -> if ty_eq_dec t1 t1' then Some t2 else None
         | None -> None)
      | _ -> None)
   | None -> None)
| EAPair (e1, e2) ->
  (match typecheck_ann gamma e1 with
   | Some t1 ->
     (match typecheck_ann gamma e2 with
      | Some t2 -> Some (TyPair (t1, t2))
      | None -> None)
   | None -> None)
| EAFst e ->
  (match typecheck_ann gamma e with
   | Some t -> (match t with
                | TyPair (t1, _) -> Some t1
                | _ -> None)
   | None -> None)
| EASnd e ->
  (match typecheck_ann gamma e with
   | Some t -> (match t with
                | TyPair (_, t2) -> Some t2
                | _ -> None)
   | None -> None)
| EAObserve (e, _) ->
  (match typecheck_ann gamma e with
   | Some t -> (match t with
                | TyProcess t0 -> Some t0
                | _ -> None)
   | None -> None)
| EAResolve e -> typecheck_ann gamma e
