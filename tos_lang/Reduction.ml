open Expressions

(** val try_step : expr -> expr option **)

let rec try_step = function
| EApp (e1, e2) ->
  if is_value_dec e1
  then (match e1 with
        | ELam body ->
          if is_value_dec e2
          then Some (subst 0 e2 body)
          else (match try_step e2 with
                | Some e2p -> Some (EApp (e1, e2p))
                | None -> None)
        | _ ->
          (match try_step e2 with
           | Some e2p -> Some (EApp (e1, e2p))
           | None -> None))
  else (match try_step e1 with
        | Some e1p -> Some (EApp (e1p, e2))
        | None -> None)
| EPair (e1, e2) ->
  if is_value_dec e1
  then if is_value_dec e2
       then None
       else (match try_step e2 with
             | Some e2p -> Some (EPair (e1, e2p))
             | None -> None)
  else (match try_step e1 with
        | Some e1p -> Some (EPair (e1p, e2))
        | None -> None)
| EFst inner ->
  (match inner with
   | EPair (v1, v2) ->
     if is_value_dec v1
     then if is_value_dec v2
          then Some v1
          else (match try_step inner with
                | Some innerp -> Some (EFst innerp)
                | None -> None)
     else (match try_step inner with
           | Some innerp -> Some (EFst innerp)
           | None -> None)
   | _ ->
     (match try_step inner with
      | Some innerp -> Some (EFst innerp)
      | None -> None))
| ESnd inner ->
  (match inner with
   | EPair (v1, v2) ->
     if is_value_dec v1
     then if is_value_dec v2
          then Some v2
          else (match try_step inner with
                | Some innerp -> Some (ESnd innerp)
                | None -> None)
     else (match try_step inner with
           | Some innerp -> Some (ESnd innerp)
           | None -> None)
   | _ ->
     (match try_step inner with
      | Some innerp -> Some (ESnd innerp)
      | None -> None))
| EObserve (inner, n) ->
  if is_value_dec inner
  then Some (EConst n)
  else (match try_step inner with
        | Some innerp -> Some (EObserve (innerp, n))
        | None -> None)
| EResolve inner ->
  (match inner with
   | EConst n -> Some (EConst n)
   | _ ->
     (match try_step inner with
      | Some innerp -> Some (EResolve innerp)
      | None -> None))
| ELayerProject (e1, l) ->
  if is_value_dec e1
  then if is_value_dec l
       then Some e1
       else (match try_step e1 with
             | Some e1p -> Some (ELayerProject (e1p, l))
             | None -> None)
  else (match try_step e1 with
        | Some e1p -> Some (ELayerProject (e1p, l))
        | None -> None)
| _ -> None

(** val eval_fuel : int -> expr -> expr **)

let rec eval_fuel fuel e =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> e)
    (fun fuelp ->
    match try_step e with
    | Some ep -> eval_fuel fuelp ep
    | None -> e)
    fuel
