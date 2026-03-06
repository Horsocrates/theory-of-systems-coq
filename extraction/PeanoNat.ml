
module Nat =
 struct
  (** val min : int -> int -> int **)

  let rec min n m =
    (fun fO fS n -> if n = 0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> succ (min n' m'))
        m)
      n
 end
