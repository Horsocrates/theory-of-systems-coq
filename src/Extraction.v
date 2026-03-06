(* ========================================================================= *)
(*               OCAML EXTRACTION: THEORY OF SYSTEMS                       *)
(*                                                                          *)
(*  Extracts key ToS definitions to executable OCaml code.                 *)
(*  Prop fields are erased; only computational content remains.            *)
(*                                                                          *)
(*  Output: extracted/theory_of_systems.{ml,mli}                           *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Import ListNotations.

Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Coq.extraction.ExtrOcamlZInt.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import Roles.
From ToS Require Import IntensionalIdentity.
From ToS Require Import ProcessGeneral.

(* ========================================================================= *)
(*                   EXTRACTION CONFIGURATION                               *)
(* ========================================================================= *)

(** Inline trivial definitions *)
Extraction Inline L2 L3 L4_level.
Extraction Inline SystemL2Index.
Extraction Inline Position.

(** Map Coq types to OCaml types *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".

(* ========================================================================= *)
(*                   EXTRACTION DIRECTIVES                                  *)
(* ========================================================================= *)

Separate Extraction

  (* --- Level hierarchy (Core_ERR) --- *)
  Level L1 LS
  level_depth

  (* --- Type structure (Core_ERR) --- *)
  PositionBound Finite Unbounded
  UniquenessConstraint UniquePerRole MultiplePerRole
  Criterion mkCriterion
  System mkSystem
  StructuredSystem mkStructuredSystem

  (* --- Roles and specs (Core_ERR) --- *)
  RoleNecessity Essential Optional
  RoleSpec mkRoleSpec
  RoleInstance mkRoleInstance

  (* --- Generators and unfolding (Core_ERR) --- *)
  Generator mkGenerator
  unfold_gen
  Process mkProcess

  (* --- L5 Resolution (Core_ERR) --- *)
  L5_resolve

  (* --- ERR Categories (Roles.v) --- *)
  ERR_Category Cat_Element Cat_Role Cat_Rule
  CategorizedComponent mkCategorized
  err_cat_eq_dec

  (* --- Element status (Roles.v) --- *)
  ElementStatus ES_Active ES_Dormant ES_Constrained ES_Free

  (* --- Role resolution (Roles.v — from Section, takes L) --- *)
  role_candidates
  resolve_role

  (* --- Math/Epistemic status (Roles.v) --- *)
  MathStatus MS_Maximum MS_Minimum MS_Interior
             MS_Convergent MS_Divergent MS_Satisfies MS_Violates
  EpistemicStatus EP_Known EP_Unknown EP_Constrained EP_Free EP_Dependent
  StatusAssignment mkStatusAssignment
  math_status_eq_dec
  ep_status_eq_dec

  (* --- Dependencies (Roles.v) --- *)
  DepDirection Dep_Vertical Dep_Horizontal Dep_External
  Dependency mkDep
  reachable_in

  (* --- Well-formedness (Roles.v) --- *)
  ERR_WellFormed_Full mkWF4

  (* --- General processes (ProcessGeneral.v) --- *)
  observe
  prefix
  process_map
  const_process
  Qdist

  (* --- Identity (IntensionalIdentity.v — from Section, takes L D) --- *)
  CriterionOver mkCriterionOver
.

(* ========================================================================= *)
(*                   NOTES                                                  *)
(* ========================================================================= *)

(**
  EXTRACTION NOTES
  =================

  1. Prop fields are erased:
     - crit_level_valid, crit_predicate (Prop-valued) → erased
     - ss_L5_valid, ra_at_position, ra_satisfies → erased
     - gen_preserves → erased
     These become unit () or are dropped entirely.

  2. Predicate fields (crit_predicate : D -> Prop):
     Erased to unit. For executable predicates, use bool-valued
     deciders passed to role_candidates / resolve_role.

  3. Nat → int via ExtrOcamlNatInt.
     Peano arithmetic becomes machine integers.

  4. GenProcess A = nat -> A is a function type alias.
     prefix builds a list by iterating.

  5. reachable_in is a fuel-bounded graph search.
     Extracting it gives an executable cycle checker.

  6. Section variables become explicit parameters:
     - role_candidates L S decide positions  (L added)
     - CriterionOver L D  (L, D added)

  7. Output files go to extraction/ directory:
       extraction/theory_of_systems.mli  (interface)
       extraction/theory_of_systems.ml   (implementation)
*)
