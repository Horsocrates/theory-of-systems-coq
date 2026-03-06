open List
open TheoryOfSystems_Core_ERR

type __ = Obj.t

type coq_ERR_Category =
| Cat_Element
| Cat_Role
| Cat_Rule

(** val err_cat_eq_dec : coq_ERR_Category -> coq_ERR_Category -> bool **)

let err_cat_eq_dec c1 c2 =
  match c1 with
  | Cat_Element -> (match c2 with
                    | Cat_Element -> true
                    | _ -> false)
  | Cat_Role -> (match c2 with
                 | Cat_Role -> true
                 | _ -> false)
  | Cat_Rule -> (match c2 with
                 | Cat_Rule -> true
                 | _ -> false)

type coq_CategorizedComponent = { cc_id : int; cc_category : coq_ERR_Category }

(** val role_candidates :
    coq_Level -> coq_StructuredSystem -> (crit_domain -> bool) ->
    coq_Position list -> coq_Position list **)

let role_candidates _ s decide =
  filter (fun p ->
    match s.ss_assignment p with
    | Some e -> decide e
    | None -> false)

(** val resolve_role :
    coq_Level -> coq_StructuredSystem -> (crit_domain -> bool) ->
    coq_Position list -> coq_Position -> coq_Position **)

let resolve_role l s decide positions default =
  coq_L5_resolve (role_candidates l s decide positions) default

type coq_ElementStatus =
| ES_Active
| ES_Dormant
| ES_Constrained
| ES_Free

type coq_MathStatus =
| MS_Maximum
| MS_Minimum
| MS_Interior
| MS_Convergent
| MS_Divergent
| MS_Satisfies
| MS_Violates

type coq_EpistemicStatus =
| EP_Known
| EP_Unknown
| EP_Constrained
| EP_Free
| EP_Dependent

(** val math_status_eq_dec : coq_MathStatus -> coq_MathStatus -> bool **)

let math_status_eq_dec s1 s2 =
  match s1 with
  | MS_Maximum -> (match s2 with
                   | MS_Maximum -> true
                   | _ -> false)
  | MS_Minimum -> (match s2 with
                   | MS_Minimum -> true
                   | _ -> false)
  | MS_Interior -> (match s2 with
                    | MS_Interior -> true
                    | _ -> false)
  | MS_Convergent -> (match s2 with
                      | MS_Convergent -> true
                      | _ -> false)
  | MS_Divergent -> (match s2 with
                     | MS_Divergent -> true
                     | _ -> false)
  | MS_Satisfies -> (match s2 with
                     | MS_Satisfies -> true
                     | _ -> false)
  | MS_Violates -> (match s2 with
                    | MS_Violates -> true
                    | _ -> false)

(** val ep_status_eq_dec :
    coq_EpistemicStatus -> coq_EpistemicStatus -> bool **)

let ep_status_eq_dec s1 s2 =
  match s1 with
  | EP_Known -> (match s2 with
                 | EP_Known -> true
                 | _ -> false)
  | EP_Unknown -> (match s2 with
                   | EP_Unknown -> true
                   | _ -> false)
  | EP_Constrained -> (match s2 with
                       | EP_Constrained -> true
                       | _ -> false)
  | EP_Free -> (match s2 with
                | EP_Free -> true
                | _ -> false)
  | EP_Dependent -> (match s2 with
                     | EP_Dependent -> true
                     | _ -> false)

type ('d, 'statusSpace) coq_StatusAssignment = { sa_element : 'd;
                                                 sa_status : 'statusSpace }

type coq_DepDirection =
| Dep_Vertical
| Dep_Horizontal
| Dep_External

type coq_Dependency = { dep_from : int; dep_to : int;
                        dep_direction : coq_DepDirection }

type reachable_in = __

type coq_ERR_WellFormed_Full = { wf4_components : coq_CategorizedComponent
                                                  list;
                                 wf4_deps : coq_Dependency list }
