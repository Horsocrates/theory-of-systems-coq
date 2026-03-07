(* ========================================================================= *)
(* TOption: Option and Result Types as ToS Systems                           *)
(*                                                                           *)
(* Part of: Theory of Systems -- ToS-Lang Standard Library                   *)
(*                                                                           *)
(* E/R/R Analysis:                                                           *)
(*   Elements: wrapped value (or absence/error)                              *)
(*   Roles: Some -> Present (P1: what IS), None -> Absent                    *)
(*   Rules: must pattern match before access (constitution)                  *)
(*   Status: present | absent | ok | error                                   *)
(*   Constitution: no partial access without checking                        *)
(*                                                                           *)
(* STATUS: 14 Qed, 0 Admitted, 0 axioms                                     *)
(* Author: Horsocrates | Date: 2026                                          *)
(* ========================================================================= *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import DependentSystems.

(* ========================================================================= *)
(*                    PART I: OPTION OPERATIONS                              *)
(* ========================================================================= *)

(** Option map: apply f inside Some, propagate None. *)
Definition toption_map {A B : Type} (f : A -> B) (o : option A) : option B :=
  match o with Some x => Some (f x) | None => None end.

(** Option bind (monadic): chain computations that may fail. *)
Definition toption_bind {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.

(** Option default: unwrap with fallback value. *)
Definition toption_default {A : Type} (o : option A) (d : A) : A :=
  match o with Some x => x | None => d end.

(** Option is_some: boolean check for presence. *)
Definition toption_is_some {A : Type} (o : option A) : bool :=
  match o with Some _ => true | None => false end.

(* ========================================================================= *)
(*                    PART II: RESULT TYPE                                   *)
(* ========================================================================= *)

(** Result type: Either a success value or an error.
    Models D6-Reflection: computations that can fail with an error reason. *)
Inductive TResult (A E : Type) : Type :=
  | TOk : A -> TResult A E
  | TErr : E -> TResult A E.

Arguments TOk {A E}.
Arguments TErr {A E}.

(** Result map: apply f to the success value, propagate errors. *)
Definition tresult_map {A B E : Type} (f : A -> B) (r : TResult A E) : TResult B E :=
  match r with TOk a => TOk (f a) | TErr e => TErr e end.

(** Result bind (monadic): chain computations that may error. *)
Definition tresult_bind {A B E : Type} (r : TResult A E) (f : A -> TResult B E) : TResult B E :=
  match r with TOk a => f a | TErr e => TErr e end.

(** Result map_err: transform the error type, keep success unchanged. *)
Definition tresult_map_err {A E1 E2 : Type} (f : E1 -> E2) (r : TResult A E1) : TResult A E2 :=
  match r with TOk a => TOk a | TErr e => TErr (f e) end.

(** Result unwrap_or: extract value or use default on error. *)
Definition tresult_unwrap_or {A E : Type} (r : TResult A E) (d : A) : A :=
  match r with TOk a => a | TErr _ => d end.

(** Result is_ok: boolean check for success. *)
Definition tresult_is_ok {A E : Type} (r : TResult A E) : bool :=
  match r with TOk _ => true | TErr _ => false end.

(* ========================================================================= *)
(*                    PART III: OPTION PROPERTIES                            *)
(* ========================================================================= *)

(** Theorem 1: Map over Some applies f. *)
Theorem toption_map_some : forall (A B : Type) (f : A -> B) (x : A),
  toption_map f (Some x) = Some (f x).
Proof. intros. reflexivity. Qed.

(** Theorem 2: Map over None returns None. *)
Theorem toption_map_none : forall (A B : Type) (f : A -> B),
  toption_map f None = None.
Proof. intros. reflexivity. Qed.

(** Theorem 3: Bind over Some applies f. *)
Theorem toption_bind_some : forall (A B : Type) (x : A) (f : A -> option B),
  toption_bind (Some x) f = f x.
Proof. intros. reflexivity. Qed.

(** Theorem 4: Bind over None returns None. *)
Theorem toption_bind_none : forall (A B : Type) (f : A -> option B),
  toption_bind None f = None.
Proof. intros. reflexivity. Qed.

(** Theorem 5: Default of Some returns the wrapped value. *)
Theorem toption_default_some : forall (A : Type) (x d : A),
  toption_default (Some x) d = x.
Proof. intros. reflexivity. Qed.

(** Theorem 6: Default of None returns the default. *)
Theorem toption_default_none : forall (A : Type) (d : A),
  toption_default None d = d.
Proof. intros. reflexivity. Qed.

(** Theorem 7: is_some of Some is true. *)
Theorem toption_is_some_some : forall (A : Type) (x : A),
  toption_is_some (Some x) = true.
Proof. intros. reflexivity. Qed.

(** Theorem 8: is_some of None is false. *)
Theorem toption_is_some_none : forall (A : Type),
  toption_is_some (@None A) = false.
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART IV: RESULT PROPERTIES                             *)
(* ========================================================================= *)

(** Theorem 9: Result map over TOk applies f. *)
Theorem tresult_map_ok : forall (A B E : Type) (f : A -> B) (x : A),
  tresult_map f (@TOk A E x) = TOk (f x).
Proof. intros. reflexivity. Qed.

(** Theorem 10: Result map_err over TOk preserves the value. *)
Theorem tresult_map_err_ok : forall (A E1 E2 : Type) (f : E1 -> E2) (x : A),
  tresult_map_err f (@TOk A E1 x) = TOk x.
Proof. intros. reflexivity. Qed.

(** Theorem 11: Result bind over TOk applies f. *)
Theorem tresult_bind_ok : forall (A B E : Type) (x : A) (f : A -> TResult B E),
  tresult_bind (@TOk A E x) f = f x.
Proof. intros. reflexivity. Qed.

(** Theorem 12: Result bind over TErr propagates the error. *)
Theorem tresult_bind_err : forall (A B E : Type) (e : E) (f : A -> TResult B E),
  tresult_bind (@TErr A E e) f = TErr e.
Proof. intros. reflexivity. Qed.

(** Theorem 13: unwrap_or of TOk returns the value. *)
Theorem tresult_unwrap_or_ok : forall (A E : Type) (x : A) (d : A),
  tresult_unwrap_or (@TOk A E x) d = x.
Proof. intros. reflexivity. Qed.

(** Theorem 14: unwrap_or of TErr returns the default. *)
Theorem tresult_unwrap_or_err : forall (A E : Type) (e : E) (d : A),
  tresult_unwrap_or (@TErr A E e) d = d.
Proof. intros. reflexivity. Qed.
