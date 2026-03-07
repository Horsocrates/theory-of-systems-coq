(* ========================================================================= *)
(* TSort: Verified Sorting as L5-Resolution in Action                        *)
(*                                                                           *)
(* Part of: Theory of Systems -- ToS-Lang Standard Library                   *)
(*                                                                           *)
(* E/R/R Analysis:                                                           *)
(*   Elements: list items                                                    *)
(*   Roles: UnsortedInput -> SortedOutput                                    *)
(*   Rules: L5 ordering via DecTotalOrder                                    *)
(*   Status: unsorted -> sorted (status transition via sort)                 *)
(*   Constitution: sorted + permutation of input                             *)
(*                                                                           *)
(* STATUS: 20 Qed, 0 Admitted, 0 axioms                                     *)
(* Author: Horsocrates | Date: 2026                                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import L5Resolution.

(* ========================================================================= *)
(*                    PART I: SORTED PREDICATE                               *)
(* ========================================================================= *)

Section Sorting.
Context {A : Type} `{DTO : DecTotalOrder A}.

(** Sorted: a list is sorted if each adjacent pair is in dto_le order. *)
Inductive Sorted : list A -> Prop :=
  | Sorted_nil : Sorted []
  | Sorted_one : forall x, Sorted [x]
  | Sorted_cons : forall x y l,
      dto_le x y -> Sorted (y :: l) -> Sorted (x :: y :: l).

(* ========================================================================= *)
(*                    PART II: INSERTION SORT                                *)
(* ========================================================================= *)

(** Insert x into a sorted list, maintaining sort order. *)
Fixpoint insert_sorted (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | y :: ys =>
    if dto_le_dec x y then x :: y :: ys
    else y :: insert_sorted x ys
  end.

(** Insertion sort: repeatedly insert each element. *)
Fixpoint insertion_sort (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => insert_sorted x (insertion_sort xs)
  end.

(* ========================================================================= *)
(*                    PART III: FUEL-BASED MERGE                             *)
(* ========================================================================= *)

(** Merge two lists using fuel (sum of lengths) for termination. *)
Fixpoint merge_aux (fuel : nat) (l1 l2 : list A) : list A :=
  match fuel with
  | 0 => l1 ++ l2
  | S fuel' =>
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: xs, y :: ys =>
      if dto_le_dec x y then x :: merge_aux fuel' xs (y :: ys)
      else y :: merge_aux fuel' (x :: xs) ys
    end
  end.

Definition merge (l1 l2 : list A) : list A :=
  merge_aux (length l1 + length l2) l1 l2.

(* ========================================================================= *)
(*                    PART IV: INSERTION PROPERTIES                          *)
(* ========================================================================= *)

(** Lemma 1: Membership in insert_sorted *)
Lemma insert_sorted_In : forall x y l,
  In y (insert_sorted x l) <-> y = x \/ In y l.
Proof.
  intros x y l. induction l as [| z zs IH]; simpl.
  - intuition.
  - destruct (dto_le_dec x z); simpl.
    + intuition.
    + rewrite IH. intuition.
Qed.

(** Lemma 2: Length of insert_sorted *)
Lemma insert_sorted_length : forall x l,
  length (insert_sorted x l) = S (length l).
Proof.
  intros x l. induction l as [| z zs IH]; simpl.
  - reflexivity.
  - destruct (dto_le_dec x z); simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(** Lemma 3: insert_sorted preserves Sorted *)
Lemma insert_sorted_sorted : forall x l,
  Sorted l -> Sorted (insert_sorted x l).
Proof.
  intros x l. induction l as [| y ys IH]; intro Hsorted; simpl.
  - apply Sorted_one.
  - destruct (dto_le_dec x y) as [Hxy | Hxy].
    + apply Sorted_cons; assumption.
    + assert (Hyx : dto_le y x).
      { destruct (dto_le_total x y) as [Hc | Hc]; [contradiction | exact Hc]. }
      destruct ys as [| z zs].
      * simpl. apply Sorted_cons; [exact Hyx | apply Sorted_one].
      * simpl.
        assert (Hyz : dto_le y z) by (inversion Hsorted; subst; assumption).
        assert (Htail : Sorted (z :: zs)) by (inversion Hsorted; subst; assumption).
        destruct (dto_le_dec x z) as [Hxz | Hxz].
        -- apply Sorted_cons; [exact Hyx |].
           apply Sorted_cons; [exact Hxz | exact Htail].
        -- apply Sorted_cons; [exact Hyz |].
           specialize (IH Htail). simpl in IH.
           destruct (dto_le_dec x z); [contradiction | exact IH].
Qed.

(* ========================================================================= *)
(*                    PART V: INSERTION SORT PROPERTIES                      *)
(* ========================================================================= *)

(** Lemma 4: insertion_sort produces Sorted output *)
Lemma insertion_sort_sorted : forall l,
  Sorted (insertion_sort l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Sorted_nil.
  - apply insert_sorted_sorted. exact IH.
Qed.

(** Lemma 5: insertion_sort preserves length *)
Lemma insertion_sort_length : forall l,
  length (insertion_sort l) = length l.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite insert_sorted_length. rewrite IH. reflexivity.
Qed.

(** Lemma 6: insertion_sort of [] is [] *)
Lemma insertion_sort_nil : insertion_sort [] = @nil A.
Proof. reflexivity. Qed.

(** Lemma 7: insertion_sort preserves membership *)
Lemma insertion_sort_In : forall x l,
  In x (insertion_sort l) <-> In x l.
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - intuition.
  - rewrite insert_sorted_In. rewrite IH. intuition.
Qed.

(* ========================================================================= *)
(*                    PART VI: PERMUTATION PROPERTIES                        *)
(* ========================================================================= *)

(** Lemma 8: insert_sorted produces a Permutation *)
Lemma insert_sorted_perm : forall x l,
  Permutation (x :: l) (insert_sorted x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - apply Permutation_refl.
  - destruct (dto_le_dec x y) as [Hxy | Hxy].
    + apply Permutation_refl.
    + apply perm_trans with (y :: x :: ys).
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

(** Lemma 9: insertion_sort produces a Permutation of the input *)
Lemma insertion_sort_perm : forall l,
  Permutation l (insertion_sort l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - apply perm_trans with (x :: insertion_sort xs).
    + apply perm_skip. exact IH.
    + apply insert_sorted_perm.
Qed.

(* ========================================================================= *)
(*                    PART VII: MERGE PROPERTIES                             *)
(* ========================================================================= *)

(** Lemma 10: merge with [] on the left *)
Lemma merge_nil_l : forall l, merge [] l = l.
Proof.
  intros l. unfold merge. destruct l; reflexivity.
Qed.

(** Lemma 11: merge with [] on the right *)
Lemma merge_nil_r : forall l, merge l [] = l.
Proof.
  intros l. unfold merge.
  replace (length l + length (@nil A)) with (length l) by (simpl; lia).
  destruct l as [| a t]; reflexivity.
Qed.

(* ========================================================================= *)
(*                    PART VIII: SORTED INVERSION                            *)
(* ========================================================================= *)

(** Lemma 12: Sorted tail *)
Lemma sorted_tail : forall x l,
  Sorted (x :: l) -> Sorted l.
Proof.
  intros x l Hs.
  destruct l as [| y ys].
  - apply Sorted_nil.
  - inversion Hs; subst; assumption.
Qed.

(** Lemma 13: Sorted head is le next element *)
Lemma sorted_head_le : forall x y l,
  Sorted (x :: y :: l) -> dto_le x y.
Proof.
  intros x y l Hs. inversion Hs; subst; assumption.
Qed.

(** Lemma 14: Sorted is preserved by appending larger element *)
Lemma sorted_app_single : forall l x,
  Sorted l ->
  (forall y, In y l -> dto_le y x) ->
  Sorted (l ++ [x]).
Proof.
  intros l x Hs Hall. induction l as [| a t IH]; simpl.
  - apply Sorted_one.
  - destruct t as [| b t'].
    + simpl. apply Sorted_cons.
      * apply Hall. simpl. left. reflexivity.
      * apply Sorted_one.
    + simpl. apply Sorted_cons.
      * apply sorted_head_le in Hs. exact Hs.
      * apply IH.
        -- eapply sorted_tail. exact Hs.
        -- intros y Hy. apply Hall. simpl. right. exact Hy.
Qed.

End Sorting.

(* ========================================================================= *)
(*                    PART IX: NAT EXAMPLES                                  *)
(* ========================================================================= *)

(** Example 1: [1; 2; 3] is sorted *)
Example sorted_example_1 : @Sorted nat nat_dto [1; 2; 3].
Proof.
  apply Sorted_cons. simpl. lia.
  apply Sorted_cons. simpl. lia.
  apply Sorted_one.
Qed.

(** Example 2: [0; 5; 10] is sorted *)
Example sorted_example_2 : @Sorted nat nat_dto [0; 5; 10].
Proof.
  apply Sorted_cons. simpl. lia.
  apply Sorted_cons. simpl. lia.
  apply Sorted_one.
Qed.

(** Example 3: insertion_sort [3; 1; 2] = [1; 2; 3] *)
Example sort_example_1 :
  @insertion_sort nat nat_dto [3; 1; 2] = [1; 2; 3].
Proof. reflexivity. Qed.

(** Example 4: insertion_sort preserves elements (Permutation) *)
Example sort_preserves_elems :
  Permutation [3; 1; 2] (@insertion_sort nat nat_dto [3; 1; 2]).
Proof. apply insertion_sort_perm. Qed.

(** Example 5: merge of two sorted lists *)
Example merge_example :
  @merge nat nat_dto [1; 3; 5] [2; 4; 6] = [1; 2; 3; 4; 5; 6].
Proof. reflexivity. Qed.

(** Example 6: insertion_sort on already sorted list is identity *)
Example sort_sorted_id :
  @insertion_sort nat nat_dto [1; 2; 3] = [1; 2; 3].
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    SUMMARY                                                *)
(* ========================================================================= *)

(**
  20 Qed, 0 Admitted, 0 axioms.

  Sorting infrastructure:
  - Sorted predicate (inductive)
  - Insertion sort (functional, verified)
  - Fuel-based merge (functional)

  Key properties:
  - insert_sorted_sorted: inserting into sorted list preserves sortedness
  - insertion_sort_sorted: output is always sorted
  - insertion_sort_perm: output is a permutation of input
  - insertion_sort_In: membership preservation
  - merge_nil_l, merge_nil_r: merge identity laws
  - sorted_tail, sorted_head_le: inversion lemmas
  - sorted_app_single: append single larger element preserves sort
*)
