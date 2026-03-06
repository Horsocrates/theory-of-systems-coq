open List
open TheoryOfSystems_Core_ERR

type __ = Obj.t

type coq_ERR_Category =
| Cat_Element
| Cat_Role
| Cat_Rule

val err_cat_eq_dec : coq_ERR_Category -> coq_ERR_Category -> bool

type coq_CategorizedComponent = { cc_id : int; cc_category : coq_ERR_Category }

val role_candidates :
  coq_Level -> coq_StructuredSystem -> (crit_domain -> bool) -> coq_Position
  list -> coq_Position list

val resolve_role :
  coq_Level -> coq_StructuredSystem -> (crit_domain -> bool) -> coq_Position
  list -> coq_Position -> coq_Position

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

val math_status_eq_dec : coq_MathStatus -> coq_MathStatus -> bool

val ep_status_eq_dec : coq_EpistemicStatus -> coq_EpistemicStatus -> bool

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
