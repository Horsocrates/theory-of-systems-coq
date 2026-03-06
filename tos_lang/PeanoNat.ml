
module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m
 end
