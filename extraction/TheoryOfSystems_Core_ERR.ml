open List
open PeanoNat

type __ = Obj.t

type coq_Level =
| L1
| LS of coq_Level

(** val level_depth : coq_Level -> int **)

let rec level_depth = function
| L1 -> succ 0
| LS l' -> succ (level_depth l')

type coq_Criterion =
  coq_Level
  (* singleton inductive, whose constructor was mkCriterion *)

type crit_domain = __

type coq_PositionBound =
| Finite of int
| Unbounded

type coq_UniquenessConstraint =
| UniquePerRole
| MultiplePerRole

type coq_System = { sys_criterion : coq_Criterion;
                    sys_pos_bound : coq_PositionBound;
                    sys_uniqueness : coq_UniquenessConstraint }

type coq_RoleNecessity =
| Essential of int
| Optional

type 'elemType coq_RoleSpec = { rspec_id : int;
                                rspec_necessity : coq_RoleNecessity }

type coq_RoleInstance = { ri_system : coq_System;
                          ri_parent_level : coq_Level; ri_role_name : 
                          int }

type 'elemType coq_Generator = { gen_seed : 'elemType;
                                 gen_step : ('elemType -> 'elemType) }

type coq_Process = { proc_system : coq_System;
                     proc_generator : crit_domain coq_Generator option;
                     proc_depth : int }

(** val unfold_gen : 'a1 coq_Generator -> int -> 'a1 list **)

let rec unfold_gen g n =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> g.gen_seed::[])
    (fun n' ->
    let prev = unfold_gen g n' in
    (match prev with
     | [] -> []
     | h::_ -> (g.gen_step h)::prev))
    n

type coq_Position = int

type coq_StructuredSystem = { ss_base : coq_System;
                              ss_assignment : (coq_Position -> crit_domain
                                              option) }

(** val coq_L5_resolve : coq_Position list -> coq_Position -> coq_Position **)

let coq_L5_resolve candidates default =
  fold_right Nat.min default candidates
