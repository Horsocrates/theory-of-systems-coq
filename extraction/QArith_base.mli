open BinInt
open BinPos

type coq_Q = { coq_Qnum : int; coq_Qden : int }

val coq_Qplus : coq_Q -> coq_Q -> coq_Q

val coq_Qopp : coq_Q -> coq_Q

val coq_Qminus : coq_Q -> coq_Q -> coq_Q
