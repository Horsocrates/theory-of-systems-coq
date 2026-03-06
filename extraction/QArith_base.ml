open BinInt
open BinPos

type coq_Q = { coq_Qnum : int; coq_Qden : int }

(** val coq_Qplus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qplus x y =
  { coq_Qnum =
    (Z.add (Z.mul x.coq_Qnum y.coq_Qden) (Z.mul y.coq_Qnum x.coq_Qden));
    coq_Qden = (Pos.mul x.coq_Qden y.coq_Qden) }

(** val coq_Qopp : coq_Q -> coq_Q **)

let coq_Qopp x =
  { coq_Qnum = (Z.opp x.coq_Qnum); coq_Qden = x.coq_Qden }

(** val coq_Qminus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qminus x y =
  coq_Qplus x (coq_Qopp y)
