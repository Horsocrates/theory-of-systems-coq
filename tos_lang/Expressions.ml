open Nat
open UniversePolymorphism

type coq_Var = int

(** val shift : int -> expr -> expr **)

let rec shift c = function
| EVar n -> if PeanoNat.Nat.ltb n c then EVar n else EVar (add n (succ 0))
| EElem e1 -> EElem (shift c e1)
| EApp (f, a) -> EApp ((shift c f), (shift c a))
| ELam body -> ELam (shift (add c (succ 0)) body)
| EPair (a, b) -> EPair ((shift c a), (shift c b))
| EFst e1 -> EFst (shift c e1)
| ESnd e1 -> ESnd (shift c e1)
| EObserve (e1, n) -> EObserve ((shift c e1), n)
| EResolve e1 -> EResolve (shift c e1)
| ELayerProject (e1, l) -> ELayerProject ((shift c e1), (shift c l))
| x -> x

(** val subst : coq_Var -> expr -> expr -> expr **)

let rec subst k s = function
| EVar n ->
  if (=) n k
  then s
  else if PeanoNat.Nat.ltb k n then EVar (sub n (succ 0)) else EVar n
| EElem e1 -> EElem (subst k s e1)
| EApp (f, a) -> EApp ((subst k s f), (subst k s a))
| ELam body -> ELam (subst (add k (succ 0)) (shift 0 s) body)
| EPair (a, b) -> EPair ((subst k s a), (subst k s b))
| EFst e1 -> EFst (subst k s e1)
| ESnd e1 -> ESnd (subst k s e1)
| EObserve (e1, n) -> EObserve ((subst k s e1), n)
| EResolve e1 -> EResolve (subst k s e1)
| ELayerProject (e1, l) -> ELayerProject ((subst k s e1), (subst k s l))
| x -> x

(** val expr_eq_dec : expr -> expr -> bool **)

let rec expr_eq_dec e e2 =
  match e with
  | EVar v -> (match e2 with
               | EVar v0 -> (=) v v0
               | _ -> false)
  | ESystem l -> (match e2 with
                  | ESystem l0 -> level_eq_dec l l0
                  | _ -> false)
  | EElem e0 -> (match e2 with
                 | EElem e1 -> expr_eq_dec e0 e1
                 | _ -> false)
  | EApp (e0, e1) ->
    (match e2 with
     | EApp (e3, e4) ->
       let s = expr_eq_dec e0 e3 in if s then expr_eq_dec e1 e4 else false
     | _ -> false)
  | ELam e0 -> (match e2 with
                | ELam e1 -> expr_eq_dec e0 e1
                | _ -> false)
  | EPair (e0, e1) ->
    (match e2 with
     | EPair (e3, e4) ->
       let s = expr_eq_dec e0 e3 in if s then expr_eq_dec e1 e4 else false
     | _ -> false)
  | EFst e0 -> (match e2 with
                | EFst e1 -> expr_eq_dec e0 e1
                | _ -> false)
  | ESnd e0 -> (match e2 with
                | ESnd e1 -> expr_eq_dec e0 e1
                | _ -> false)
  | EObserve (e0, n) ->
    (match e2 with
     | EObserve (e1, n0) ->
       let s = expr_eq_dec e0 e1 in if s then (=) n n0 else false
     | _ -> false)
  | EResolve e0 ->
    (match e2 with
     | EResolve e1 -> expr_eq_dec e0 e1
     | _ -> false)
  | ELayerProject (e0, e1) ->
    (match e2 with
     | ELayerProject (e3, e4) ->
       let s = expr_eq_dec e0 e3 in if s then expr_eq_dec e1 e4 else false
     | _ -> false)
  | EConst n -> (match e2 with
                 | EConst n0 -> (=) n n0
                 | _ -> false)

(** val is_value_dec : expr -> bool **)

let rec is_value_dec = function
| ESystem _ -> true
| ELam _ -> true
| EPair (e0, e1) -> if is_value_dec e0 then is_value_dec e1 else false
| EConst _ -> true
| _ -> false
