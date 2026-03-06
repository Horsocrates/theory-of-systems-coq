
(** val level_eq_dec : level -> level -> bool **)

let rec level_eq_dec l l2 =
  match l with
  | L1 -> (match l2 with
           | L1 -> true
           | LS _ -> false)
  | LS l0 -> (match l2 with
              | L1 -> false
              | LS l1 -> level_eq_dec l0 l1)
