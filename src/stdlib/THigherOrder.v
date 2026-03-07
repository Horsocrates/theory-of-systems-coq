(* ========================================================================= *)
(* THigherOrder: Map, Filter, Fold as Pi-System Applications                 *)
(*                                                                           *)
(* Part of: Theory of Systems -- ToS-Lang Standard Library                   *)
(*                                                                           *)
(* E/R/R Analysis:                                                           *)
(*   Elements: list items + transformation function                          *)
(*   Roles: f -> Transformer (Pi-type), p -> Selector (Constitution check)   *)
(*   Rules: f preserves structure (map), p decides membership (filter)       *)
(*   Status: mapped | filtered | folded                                      *)
(*   Constitution: function application preserves well-formedness            *)
(*                                                                           *)
(* STATUS: 18 Qed, 0 Admitted, 0 axioms                                     *)
(* Author: Horsocrates | Date: 2026                                          *)
(* ========================================================================= *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import DependentSystems.
From ToS Require Import ConstitutionChecking.

(* ========================================================================= *)
(*                    PART I: DEFINITIONS                                    *)
(* ========================================================================= *)

Definition tmap {A B : Type} (f : A -> B) (l : list A) : list B := map f l.

Definition tfilter {A : Type} (p : A -> bool) (l : list A) : list A := filter p l.

Definition tfold_left {A B : Type} (f : A -> B -> A) (init : A) (l : list B) : A :=
  fold_left f l init.

Definition tfold_right {A B : Type} (f : B -> A -> A) (init : A) (l : list B) : A :=
  fold_right f init l.

Definition tmap_filter {A B : Type} (f : A -> B) (p : A -> bool) (l : list A) : list B :=
  map f (filter p l).

Definition tfilter_map {A B : Type} (p : B -> bool) (f : A -> B) (l : list A) : list B :=
  filter p (map f l).

Definition tforall {A : Type} (p : A -> bool) (l : list A) : bool :=
  forallb p l.

Definition texists {A : Type} (p : A -> bool) (l : list A) : bool :=
  existsb p l.

(* ========================================================================= *)
(*                    PART II: MAP PROPERTIES                                *)
(* ========================================================================= *)

Theorem tmap_nil : forall (A B : Type) (f : A -> B),
  tmap f [] = [].
Proof. intros. reflexivity. Qed.

Theorem tmap_cons : forall (A B : Type) (f : A -> B) (x : A) (l : list A),
  tmap f (x :: l) = f x :: tmap f l.
Proof. intros. reflexivity. Qed.

Theorem tmap_length : forall (A B : Type) (f : A -> B) (l : list A),
  length (tmap f l) = length l.
Proof.
  intros. unfold tmap. apply map_length.
Qed.

Theorem tmap_compose : forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
  tmap g (tmap f l) = tmap (fun x => g (f x)) l.
Proof.
  intros. unfold tmap. rewrite map_map. reflexivity.
Qed.

Theorem tmap_id : forall (A : Type) (l : list A),
  tmap (fun x => x) l = l.
Proof.
  intros. unfold tmap. apply map_id.
Qed.

Theorem tmap_app : forall (A B : Type) (f : A -> B) (l1 l2 : list A),
  tmap f (l1 ++ l2) = tmap f l1 ++ tmap f l2.
Proof.
  intros. unfold tmap. apply map_app.
Qed.

(* ========================================================================= *)
(*                    PART III: FILTER PROPERTIES                            *)
(* ========================================================================= *)

Theorem tfilter_nil : forall (A : Type) (p : A -> bool),
  tfilter p [] = [].
Proof. intros. reflexivity. Qed.

Theorem tfilter_length : forall (A : Type) (p : A -> bool) (l : list A),
  length (tfilter p l) <= length l.
Proof.
  intros. unfold tfilter. induction l as [| x l0 IH].
  - simpl. lia.
  - simpl. destruct (p x).
    + simpl. lia.
    + lia.
Qed.

Theorem tfilter_all_true : forall (A : Type) (l : list A),
  tfilter (fun _ => true) l = l.
Proof.
  intros. unfold tfilter. induction l as [| x l0 IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Theorem tfilter_all_false : forall (A : Type) (l : list A),
  tfilter (fun _ => false) l = [].
Proof.
  intros. unfold tfilter. induction l as [| x l0 IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

Theorem tfilter_In : forall (A : Type) (p : A -> bool) (x : A) (l : list A),
  In x (tfilter p l) <-> In x l /\ p x = true.
Proof.
  intros. unfold tfilter. apply filter_In.
Qed.

(* ========================================================================= *)
(*                    PART IV: FOLD PROPERTIES                               *)
(* ========================================================================= *)

Theorem tfold_left_nil : forall (A B : Type) (f : A -> B -> A) (init : A),
  tfold_left f init [] = init.
Proof. intros. reflexivity. Qed.

Theorem tfold_right_nil : forall (A B : Type) (f : B -> A -> A) (init : A),
  tfold_right f init [] = init.
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART V: FORALL / EXISTS PROPERTIES                     *)
(* ========================================================================= *)

Theorem tforall_nil : forall (A : Type) (p : A -> bool),
  tforall p [] = true.
Proof. intros. reflexivity. Qed.

Theorem texists_nil : forall (A : Type) (p : A -> bool),
  texists p [] = false.
Proof. intros. reflexivity. Qed.

Theorem tmap_filter_length : forall (A B : Type) (f : A -> B) (p : A -> bool) (l : list A),
  length (tmap_filter f p l) <= length l.
Proof.
  intros. unfold tmap_filter.
  rewrite map_length.
  induction l as [| x l0 IH].
  - simpl. lia.
  - simpl. destruct (p x).
    + simpl. lia.
    + lia.
Qed.

Theorem tforall_true : forall (A : Type) (p : A -> bool) (l : list A),
  tforall p l = true -> forall x, In x l -> p x = true.
Proof.
  intros A p l H x Hx.
  unfold tforall in H.
  rewrite forallb_forall in H.
  apply H. exact Hx.
Qed.

Theorem texists_true : forall (A : Type) (p : A -> bool) (l : list A),
  texists p l = true -> exists x, In x l /\ p x = true.
Proof.
  intros A p l H.
  unfold texists in H.
  rewrite existsb_exists in H.
  exact H.
Qed.
