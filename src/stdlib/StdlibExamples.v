(* ========================================================================= *)
(* StdlibExamples: Cross-Module Integration Examples                         *)
(*                                                                           *)
(* Part of: Theory of Systems -- ToS-Lang Standard Library                   *)
(*                                                                           *)
(* Demonstrates interaction between multiple stdlib modules:                 *)
(*   TMap + TSet + TTree + TQueue + TInt + TStream +                        *)
(*   TSearch + THigherOrder + TOption                                        *)
(*                                                                           *)
(* STATUS: 12 Qed, 0 Admitted, 0 axioms                                     *)
(* Author: Horsocrates | Date: 2026                                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import L5Resolution.
From ToS Require Import stdlib.TMap.
From ToS Require Import stdlib.TSet.
From ToS Require Import stdlib.TTree.
From ToS Require Import stdlib.TQueue.
From ToS Require Import stdlib.TInt.
From ToS Require Import stdlib.TStream.
From ToS Require Import stdlib.TSearch.
From ToS Require Import stdlib.THigherOrder.
From ToS Require Import stdlib.TOption.

Close Scope Z_scope.
Open Scope nat_scope.

(* ========================================================================= *)
(*                    PART I: MAP + SET INTEGRATION                          *)
(* ========================================================================= *)

(** Example 1: Build a map with 3 entries and look up a key. *)
Example ex_map_lookup :
  @tm_lookup nat nat nat_dto 2
    (tm_insert 3 30 (tm_insert 2 20 (tm_insert 1 10 tm_empty))) = Some 20.
Proof. reflexivity. Qed.

(** Example 2: Build a set from adds, check membership. *)
Example ex_set_member :
  @ts_member nat nat_dto 3
    (ts_add 3 (ts_add 2 (ts_add 1 ts_empty))) = true.
Proof. reflexivity. Qed.

(** Example 3: Set union preserves subset relation. *)
Example ex_set_union_subset :
  @ts_subset nat nat_dto
    (ts_add 1 (ts_add 2 ts_empty))
    (ts_union (ts_add 1 ts_empty) (ts_add 2 (ts_add 3 ts_empty))) = true.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART II: TREE + QUEUE                                  *)
(* ========================================================================= *)

(** Example 4: BST insert three values, then look up the last. *)
Example ex_tree_member :
  let t := @tree_insert nat nat_dto 5 tree_empty in
  let t := tree_insert 2 t in
  let t := tree_insert 8 t in
  tree_member 8 t = true.
Proof. reflexivity. Qed.

(** Example 5: FIFO queue enqueue + to_list preserves insertion order. *)
Example ex_queue_to_list :
  @tq_to_list nat
    (tq_enqueue 3 (tq_enqueue 2 (tq_enqueue 1 tq_empty))) = [1; 2; 3].
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART III: SEARCH + HIGHER-ORDER                        *)
(* ========================================================================= *)

(** Example 6: Find element in list using predicate. *)
Example ex_find :
  ts_find (Nat.eqb 4) [1; 2; 3; 4; 5] = Some 4.
Proof. reflexivity. Qed.

(** Example 7: Map doubles, then filter to keep values below 5. *)
Example ex_map_filter :
  tfilter (fun n => Nat.ltb n 5)
    (tmap (fun n => n * 2) [1; 2; 3; 4; 5]) = [2; 4].
Proof. reflexivity. Qed.

(** Example 8: Left fold to compute sum of a list. *)
Example ex_fold_sum :
  tfold_left Nat.add 0 [1; 2; 3; 4; 5] = 15.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART IV: STREAM + OPTION + INTEGER                     *)
(* ========================================================================= *)

(** Example 9: Take first 5 elements from the natural number stream. *)
Example ex_stream_take :
  ts_take 5 (ts_iterate S 0) = [0; 1; 2; 3; 4].
Proof. reflexivity. Qed.

(** Example 10: Chained option bind. *)
Example ex_option_bind :
  toption_bind
    (toption_bind (Some 2) (fun n => Some (n + 1)))
    (fun n => if Nat.eqb n 0 then None else Some (n * 10)) = Some 30.
Proof. reflexivity. Qed.

(** Example 11: Integer absolute value of negation. *)
Example ex_int_abs :
  tint_abs (tint_neg 42%Z) = 42%Z.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART V: CROSS-MODULE INTEGRATION                       *)
(* ========================================================================= *)

(** Example 12: Use fold (THigherOrder) to build a set (TSet),
    then verify membership — a genuine cross-module pipeline. *)
Example ex_fold_builds_set :
  let s := tfold_left
    (fun acc x => @ts_add nat nat_dto x acc) ts_empty [3; 1; 4; 1; 5] in
  ts_member 4 s = true.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    SUMMARY                                                *)
(* ========================================================================= *)

(**
  12 Qed, 0 Admitted, 0 axioms.

  Cross-module integration demonstrated:
  - ex_map_lookup:       TMap insert + lookup
  - ex_set_member:       TSet add + member
  - ex_set_union_subset: TSet union + subset (L5-ordered)
  - ex_tree_member:      TTree insert + member (BST)
  - ex_queue_to_list:    TQueue enqueue + to_list (FIFO order)
  - ex_find:             TSearch find with predicate
  - ex_map_filter:       THigherOrder map + filter composition
  - ex_fold_sum:         THigherOrder fold_left
  - ex_stream_take:      TStream iterate + take (lazy → finite)
  - ex_option_bind:      TOption bind chain
  - ex_int_abs:          TInt negation + absolute value
  - ex_fold_builds_set:  THigherOrder fold + TSet add/member (cross-module)
*)
