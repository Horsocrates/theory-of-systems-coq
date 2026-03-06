open BinInt
open QArith_base

(** val coq_Qabs : coq_Q -> coq_Q **)

let coq_Qabs x =
  let { coq_Qnum = n; coq_Qden = d } = x in
  { coq_Qnum = (Z.abs n); coq_Qden = d }
