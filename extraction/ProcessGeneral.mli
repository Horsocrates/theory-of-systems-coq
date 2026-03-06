open Datatypes
open QArith_base
open Qabs

type 'a coq_GenProcess = int -> 'a

val observe : 'a1 coq_GenProcess -> int -> 'a1

val prefix : 'a1 coq_GenProcess -> int -> 'a1 list

val process_map : ('a1 -> 'a2) -> 'a1 coq_GenProcess -> 'a2 coq_GenProcess

val const_process : 'a1 -> 'a1 coq_GenProcess

val coq_Qdist : coq_Q -> coq_Q -> coq_Q
