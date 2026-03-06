open Nat
open UniversePolymorphism

type coq_Var = int

val shift : int -> expr -> expr

val subst : coq_Var -> expr -> expr -> expr

val expr_eq_dec : expr -> expr -> bool

val is_value_dec : expr -> bool
