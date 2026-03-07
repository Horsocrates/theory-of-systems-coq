(* ========================================================================= *)
(* TSearch: Verified Search as Constitution Checking                         *)
(*                                                                           *)
(* Part of: Theory of Systems -- ToS-Lang Standard Library                   *)
(*                                                                           *)
(* E/R/R Analysis:                                                           *)
(*   Elements: list items + search criterion                                 *)
(*   Roles: criterion -> Selector, items -> Candidates                       *)
(*   Rules: DecidableConstitution (search = satisfy constitution?)           *)
(*   Status: found | not_found                                               *)
(*   Constitution: element satisfies search predicate                        *)
(*                                                                           *)
(* STATUS: 17 Qed, 0 Admitted, 0 axioms                                     *)
(* Author: Horsocrates | Date: 2026                                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import L5Resolution.
From ToS Require Import ConstitutionChecking.

(* ========================================================================= *)
(*                    PART I: SEARCH FUNCTIONS                               *)
(* ========================================================================= *)

Section Search.
Context {A : Type}.

(** Find the first element satisfying a boolean predicate. *)
Fixpoint ts_find (f : A -> bool) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if f x then Some x else ts_find f xs
  end.

(** Filter elements satisfying a boolean predicate. *)
Definition ts_filter (f : A -> bool) (l : list A) : list A :=
  filter f l.

(** Find the index of the first element satisfying a predicate. *)
Fixpoint ts_find_index (f : A -> bool) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: xs =>
    if f x then Some 0
    else option_map S (ts_find_index f xs)
  end.

(** Count elements satisfying a predicate. *)
Definition ts_count (f : A -> bool) (l : list A) : nat :=
  length (filter f l).

(* ========================================================================= *)
(*                    PART II: FIND PROPERTIES                               *)
(* ========================================================================= *)

(** Lemma 1: ts_find on empty list returns None *)
Lemma ts_find_nil : forall f, ts_find f [] = None.
Proof. intros f. reflexivity. Qed.

(** Lemma 2: ts_find result satisfies the predicate *)
Lemma ts_find_some_true : forall f l x,
  ts_find f l = Some x -> f x = true.
Proof.
  intros f l. induction l as [| a t IH]; intros x Hfind; simpl in Hfind.
  - discriminate.
  - destruct (f a) eqn:Hfa.
    + injection Hfind as Heq. subst. exact Hfa.
    + apply IH. exact Hfind.
Qed.

(** Lemma 3: ts_find result is in the list *)
Lemma ts_find_some_in : forall f l x,
  ts_find f l = Some x -> In x l.
Proof.
  intros f l. induction l as [| a t IH]; intros x Hfind; simpl in *.
  - discriminate.
  - destruct (f a) eqn:Hfa.
    + injection Hfind as Heq. subst. left. reflexivity.
    + right. apply IH. exact Hfind.
Qed.

(** Lemma 4: ts_find returns None iff no element satisfies f *)
Lemma ts_find_none_all : forall f l,
  ts_find f l = None -> forall x, In x l -> f x = false.
Proof.
  intros f l. induction l as [| a t IH]; intros Hnone x Hin; simpl in *.
  - destruct Hin.
  - destruct (f a) eqn:Hfa.
    + discriminate.
    + destruct Hin as [Heq | Hin].
      * subst. exact Hfa.
      * apply IH; assumption.
Qed.

(* ========================================================================= *)
(*                    PART III: FILTER PROPERTIES                            *)
(* ========================================================================= *)

(** Lemma 5: ts_filter of empty list is empty *)
Lemma ts_filter_nil : forall f, ts_filter f (@nil A) = [].
Proof. intros f. reflexivity. Qed.

(** Lemma 6: ts_filter membership characterization *)
Lemma ts_filter_In : forall f x l,
  In x (ts_filter f l) <-> In x l /\ f x = true.
Proof.
  intros f x l. unfold ts_filter. apply filter_In.
Qed.

(** Lemma 7: ts_filter length is at most original length *)
Lemma ts_filter_length : forall f l,
  length (ts_filter f l) <= length l.
Proof.
  intros f l. unfold ts_filter.
  induction l as [| a t IH]; simpl.
  - lia.
  - destruct (f a); simpl; lia.
Qed.

(** Lemma 8: ts_filter distributes over append *)
Lemma ts_filter_app : forall f l1 l2,
  ts_filter f (l1 ++ l2) = ts_filter f l1 ++ ts_filter f l2.
Proof.
  intros f l1 l2. unfold ts_filter.
  induction l1 as [| a t IH]; simpl.
  - reflexivity.
  - destruct (f a); simpl; rewrite IH; reflexivity.
Qed.

(** Lemma 9: ts_filter with always-true predicate is identity *)
Lemma ts_filter_true_id : forall l,
  ts_filter (fun _ : A => true) l = l.
Proof.
  intros l. unfold ts_filter.
  induction l as [| a t IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Lemma 10: ts_filter with always-false predicate is empty *)
Lemma ts_filter_false_nil : forall l,
  ts_filter (fun _ : A => false) l = [].
Proof.
  intros l. unfold ts_filter.
  induction l as [| a t IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* ========================================================================= *)
(*                    PART IV: COUNT AND INDEX PROPERTIES                    *)
(* ========================================================================= *)

(** Lemma 11: ts_count of empty list is 0 *)
Lemma ts_count_nil : forall f, ts_count f (@nil A) = 0.
Proof. intros f. reflexivity. Qed.

(** Lemma 12: ts_count is at most list length *)
Lemma ts_count_le_length : forall f l,
  ts_count f l <= length l.
Proof.
  intros f l. unfold ts_count. apply ts_filter_length.
Qed.

(** Lemma 13: ts_find_index of empty list is None *)
Lemma ts_find_index_nil : forall f, ts_find_index f (@nil A) = None.
Proof. intros f. reflexivity. Qed.

End Search.

(* ========================================================================= *)
(*                    PART V: BINARY SEARCH (NAT-SPECIALIZED)               *)
(* ========================================================================= *)

(** Binary search on sorted nat lists using fuel for termination. *)
Fixpoint binary_search_aux (x : nat) (l : list nat) (offset fuel : nat) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match l with
    | [] => None
    | _ =>
      let mid := length l / 2 in
      match nth_error l mid with
      | None => None
      | Some v =>
        if Nat.eqb x v then Some (offset + mid)
        else if Nat.ltb x v then binary_search_aux x (firstn mid l) offset fuel'
        else binary_search_aux x (skipn (S mid) l) (offset + S mid) fuel'
      end
    end
  end.

Definition binary_search (x : nat) (l : list nat) : option nat :=
  binary_search_aux x l 0 (length l + 1).

(** Lemma 14: binary_search on empty list returns None *)
Lemma binary_search_nil : forall x, binary_search x [] = None.
Proof. intros x. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART VI: NAT EXAMPLES                                  *)
(* ========================================================================= *)

(** Example 1: Finding 3 in [1;2;3;4] *)
Example search_example_1 :
  ts_find (Nat.eqb 3) [1; 2; 3; 4] = Some 3.
Proof. reflexivity. Qed.

(** Example 2: Filtering elements less than 3 *)
Example search_example_2 :
  ts_filter (fun n => Nat.ltb n 3) [1; 2; 3; 4; 5] = [1; 2].
Proof. reflexivity. Qed.

(** Example 3: Finding index of 3 *)
Example find_index_example :
  ts_find_index (Nat.eqb 3) [1; 2; 3; 4] = Some 2.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                    SUMMARY                                                *)
(* ========================================================================= *)

(**
  17 Qed, 0 Admitted, 0 axioms.

  Search infrastructure:
  - ts_find: find first matching element
  - ts_filter: filter by predicate (wrapper around stdlib filter)
  - ts_find_index: find index of first match
  - ts_count: count matching elements
  - binary_search: fuel-based binary search on nat lists

  Key properties:
  - ts_find_some_true: found element satisfies predicate
  - ts_find_some_in: found element is in the list
  - ts_find_none_all: None means no element satisfies predicate
  - ts_filter_In: membership characterization
  - ts_filter_length: filter length bound
  - ts_filter_app: distributes over append
  - ts_filter_true_id: identity with always-true
  - ts_filter_false_nil: empty with always-false
  - ts_count_le_length: count bound
  - binary_search_nil: empty list returns None
*)
