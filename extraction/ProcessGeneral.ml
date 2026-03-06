open Datatypes
open QArith_base
open Qabs

type 'a coq_GenProcess = int -> 'a

(** val observe : 'a1 coq_GenProcess -> int -> 'a1 **)

let observe p =
  p

(** val prefix : 'a1 coq_GenProcess -> int -> 'a1 list **)

let rec prefix p n =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> app (prefix p k) ((p k)::[]))
    n

(** val process_map :
    ('a1 -> 'a2) -> 'a1 coq_GenProcess -> 'a2 coq_GenProcess **)

let process_map f p n =
  f (p n)

(** val const_process : 'a1 -> 'a1 coq_GenProcess **)

let const_process a _ =
  a

(** val coq_Qdist : coq_Q -> coq_Q -> coq_Q **)

let coq_Qdist x y =
  coq_Qabs (coq_Qminus x y)
