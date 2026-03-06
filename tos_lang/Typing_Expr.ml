open UniversePolymorphism

type coq_TyCtx = ty list

(** val ty_eq_dec : ty -> ty -> bool **)

let rec ty_eq_dec t t2 =
  match t with
  | TyNat -> (match t2 with
              | TyNat -> true
              | _ -> false)
  | TySystem l ->
    (match t2 with
     | TySystem l0 -> level_eq_dec l l0
     | _ -> false)
  | TyArrow (t0, t1) ->
    (match t2 with
     | TyArrow (t3, t4) ->
       let s = ty_eq_dec t0 t3 in if s then ty_eq_dec t1 t4 else false
     | _ -> false)
  | TyPair (t0, t1) ->
    (match t2 with
     | TyPair (t3, t4) ->
       let s = ty_eq_dec t0 t3 in if s then ty_eq_dec t1 t4 else false
     | _ -> false)
  | TyProcess t0 ->
    (match t2 with
     | TyProcess t1 -> ty_eq_dec t0 t1
     | _ -> false)
  | TyLayer t0 -> (match t2 with
                   | TyLayer t1 -> ty_eq_dec t0 t1
                   | _ -> false)
