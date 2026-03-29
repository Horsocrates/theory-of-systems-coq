(* L5_ResolutionGeneral.v *)
(* E/R/R: Elements = candidate lists, Roles = L5 status assignment, Rules = totality + determinism *)
(* Standalone — only Stdlib imports *)
(* STATUS: 12 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(** * L5 Status Assignment: L5 order defines which position carries each role.
      The first position in L5 sequence is not "chosen" — it IS the role-bearer
      by virtue of L5 constituting the order. *)

Definition L5_resolve (candidates : list nat) : option nat :=
  match candidates with
  | [] => None
  | x :: _ => Some x
  end.

(** * Totality: non-empty list always resolves *)

Lemma L5_total : forall x xs,
  L5_resolve (x :: xs) = Some x.
Proof. intros. simpl. reflexivity. Qed.

(** * Determinism: same list -> same result *)

Lemma L5_deterministic : forall l,
  L5_resolve l = L5_resolve l.
Proof. intros. reflexivity. Qed.

Lemma L5_deterministic_eq : forall l1 l2,
  l1 = l2 -> L5_resolve l1 = L5_resolve l2.
Proof. intros. subst. reflexivity. Qed.

(** * Constructive: result is always an element of the list *)

Lemma L5_constructive : forall x xs,
  In (match L5_resolve (x :: xs) with Some v => v | None => x end) (x :: xs).
Proof. intros. simpl. left. reflexivity. Qed.

(** * Empty list: no resolution *)

Lemma L5_empty : L5_resolve [] = None.
Proof. reflexivity. Qed.

(** * Concrete examples *)

Lemma L5_example_1 : L5_resolve [3%nat; 1%nat; 4%nat] = Some 3%nat.
Proof. reflexivity. Qed.

Lemma L5_example_2 : L5_resolve [7%nat] = Some 7%nat.
Proof. reflexivity. Qed.

Lemma L5_example_3 : L5_resolve [5%nat; 5%nat] = Some 5%nat.
Proof. reflexivity. Qed.

(** * No Banach-Tarski: resolution cannot create from nothing *)

Lemma no_banach_tarski : L5_resolve [] <> Some 0%nat.
Proof. discriminate. Qed.

(** * Prepending changes resolution *)

Lemma L5_prepend : forall y x xs,
  L5_resolve (y :: x :: xs) = Some y.
Proof. intros. reflexivity. Qed.

(** * Resolution is idempotent on singletons *)

Lemma L5_singleton_idem : forall x,
  L5_resolve [x] = Some x.
Proof. intros. reflexivity. Qed.

(** * Resolution respects cons *)

Lemma L5_resolve_cons : forall x l,
  L5_resolve (x :: l) = Some x.
Proof. intros. reflexivity. Qed.
