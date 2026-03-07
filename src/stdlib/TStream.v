(* TStream: Infinite Streams as ToS Observable System (P4) *)
(* STATUS: 14 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: 2026 *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import ProcessGeneral.
From ToS Require Import CoinductiveSystems.

(* ================================================================= *)
(*                   PART I: TYPE AND OPERATIONS                     *)
(* ================================================================= *)

Definition TStream (A : Type) := GenProcess A.

Definition ts_head {A} (s : TStream A) : A := s 0.
Definition ts_tail {A} (s : TStream A) : TStream A := fun n => s (S n).
Definition ts_nth {A} (n : nat) (s : TStream A) : A := s n.
Definition ts_take {A} (n : nat) (s : TStream A) : list A := prefix s n.

Definition ts_cons {A} (x : A) (s : TStream A) : TStream A :=
  fun n => match n with 0 => x | S k => s k end.

Definition ts_map {A B} (f : A -> B) (s : TStream A) : TStream B :=
  process_map f s.

Definition ts_iterate {A} (f : A -> A) (x : A) : TStream A :=
  fun n => Nat.iter n f x.

Definition ts_zip_with {A B C} (f : A -> B -> C)
    (s1 : TStream A) (s2 : TStream B) : TStream C :=
  fun n => f (s1 n) (s2 n).

Definition ts_constant {A} (x : A) : TStream A := const_process x.

(* ================================================================= *)
(*                   PART II: PROPERTIES                             *)
(* ================================================================= *)

(** 1. Head of cons is the prepended element *)
Lemma ts_head_cons : forall {A} (x : A) (s : TStream A),
    ts_head (ts_cons x s) = x.
Proof. intros A x s. unfold ts_head, ts_cons. reflexivity. Qed.

(** 2. Tail of cons recovers the original stream (pointwise) *)
Lemma ts_tail_cons : forall {A} (x : A) (s : TStream A) (n : nat),
    ts_tail (ts_cons x s) n = s n.
Proof. intros A x s n. unfold ts_tail, ts_cons. reflexivity. Qed.

(** 3. Zeroth element is head *)
Lemma ts_nth_zero : forall {A} (s : TStream A),
    ts_nth 0 s = ts_head s.
Proof. intros A s. unfold ts_nth, ts_head. reflexivity. Qed.

(** 4. Take gives a list of the right length *)
Lemma ts_take_length : forall {A} (n : nat) (s : TStream A),
    length (ts_take n s) = n.
Proof. intros A n s. unfold ts_take. apply prefix_length. Qed.

(** 5. Map distributes over head *)
Lemma ts_map_head : forall {A B} (f : A -> B) (s : TStream A),
    ts_head (ts_map f s) = f (ts_head s).
Proof. intros A B f s. unfold ts_head, ts_map, process_map. reflexivity. Qed.

(** 6. Map composition (pointwise) *)
Lemma ts_map_compose : forall {A B C} (f : A -> B) (g : B -> C)
    (s : TStream A) (n : nat),
    ts_map g (ts_map f s) n = ts_map (fun x => g (f x)) s n.
Proof.
  intros A B C f g s n. unfold ts_map, process_map. reflexivity.
Qed.

(** 7. Iterate at zero yields initial value *)
Lemma ts_iterate_zero : forall {A} (f : A -> A) (x : A),
    ts_nth 0 (ts_iterate f x) = x.
Proof. intros A f x. unfold ts_nth, ts_iterate. simpl. reflexivity. Qed.

(** 8. Iterate at successor applies f once more *)
Lemma ts_iterate_succ : forall {A} (f : A -> A) (x : A) (n : nat),
    ts_nth (S n) (ts_iterate f x) = f (ts_nth n (ts_iterate f x)).
Proof.
  intros A f x n. unfold ts_nth, ts_iterate. simpl. reflexivity.
Qed.

(** 9. Constant stream always returns the same value *)
Lemma ts_constant_nth : forall {A} (x : A) (n : nat),
    ts_nth n (ts_constant x) = x.
Proof. intros A x n. unfold ts_nth, ts_constant, const_process. reflexivity. Qed.

(** 10. Zip-with accesses both streams pointwise *)
Lemma ts_zip_with_nth : forall {A B C} (f : A -> B -> C)
    (s1 : TStream A) (s2 : TStream B) (n : nat),
    ts_nth n (ts_zip_with f s1 s2) = f (ts_nth n s1) (ts_nth n s2).
Proof.
  intros A B C f s1 s2 n. unfold ts_nth, ts_zip_with. reflexivity.
Qed.

(** 11. Take-nth correspondence *)
Lemma ts_take_nth : forall {A} (k n : nat) (s : TStream A) (d : A),
    (k < n)%nat -> nth k (ts_take n s) d = ts_nth k s.
Proof.
  intros A k n s d Hk. unfold ts_take, ts_nth.
  apply prefix_nth. exact Hk.
Qed.

(** 12. Cons then tail is identity (at each position) *)
Lemma ts_cons_tail_head : forall {A} (s : TStream A) (n : nat),
    ts_cons (ts_head s) (ts_tail s) n = s n.
Proof.
  intros A s n. unfold ts_cons, ts_head, ts_tail.
  destruct n; reflexivity.
Qed.

(** 13. Map preserves constant streams *)
Lemma ts_map_constant : forall {A B} (f : A -> B) (x : A) (n : nat),
    ts_map f (ts_constant x) n = ts_constant (f x) n.
Proof.
  intros A B f x n. unfold ts_map, ts_constant, process_map, const_process.
  reflexivity.
Qed.

(** 14. Nth of cons at successor is tail *)
Lemma ts_nth_cons_succ : forall {A} (x : A) (s : TStream A) (n : nat),
    ts_nth (S n) (ts_cons x s) = ts_nth n s.
Proof.
  intros A x s n. unfold ts_nth, ts_cons. reflexivity.
Qed.
