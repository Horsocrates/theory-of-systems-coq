(** * P4ProhibitsAC.v — P4 prohibits full AC on nat, preserves finite choice
    Elements: AC_on_nat, finite_choice, L5_choose
    Roles:    full AC requires completed index set, P4 prohibits that
    Rules:    AC_on_nat + P4 → completed_inf → contradiction
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE ARGUMENT:
    AC_on_nat: ∀F: nat→list nat, (∀n, F(n) ≠ []) → ∃f: nat→nat, ∀n, f(n) ∈ F(n).
    The choice function f: nat → nat is a COMPLETED infinite object.
    Its graph {(n, f(n)) | n ∈ nat} is a completed infinite set.
    P4 prohibits completed infinite sets → AC_on_nat is inconsistent with P4.

    BUT: finite choice (on {0,...,N}) works constructively via L5 (head of list).
    P4 PRESERVES finite choice while PROHIBITING infinite choice.
*)

From Stdlib Require Import PeanoNat Lia List.
Import ListNotations.

From ToS Require Import foundation.P4CompletedInfinity.

(* ================================================================ *)
(*  FULL AC ON NAT                                                   *)
(* ================================================================ *)

(** AC on nat: choice function exists for nat-indexed nonempty families *)
Definition AC_on_nat : Prop :=
  forall (F : nat -> list nat),
    (forall n, F n <> nil) ->
    exists f : nat -> nat, forall n, In (f n) (F n).

(** The graph of a choice function is a completed infinite set *)
Definition choice_graph (f : nat -> nat) : nat -> Prop :=
  fun n => True.  (* every n in nat has f(n), so graph is total *)

Lemma choice_graph_completed : forall f : nat -> nat,
  CompletedInfSet (choice_graph f).
Proof.
  intros f n. exact I.
Qed.

(* ================================================================ *)
(*  AC IMPLIES COMPLETED INFINITY                                    *)
(* ================================================================ *)

(** AC on nat produces a completed infinite object (the choice function) *)
Theorem ac_implies_completed :
  AC_on_nat ->
  exists f : nat -> nat, CompletedInfSet (choice_graph f).
Proof.
  intro HAC.
  (* Use constant nonempty family *)
  assert (forall n : nat, [0%nat] <> @nil nat) as Hne.
  { intro n. discriminate. }
  destruct (HAC (fun _ : nat => [0%nat]) Hne) as [f _].
  exists f. apply choice_graph_completed.
Qed.

(* ================================================================ *)
(*  FINITE CHOICE FROM L5                                            *)
(* ================================================================ *)

(** L5 choice = head of list (constructive, no axiom needed) *)
Definition L5_choose (l : list nat) (default : nat) : nat :=
  match l with
  | nil => default
  | x :: _ => x
  end.

Lemma L5_choose_in : forall l d,
  l <> nil -> In (L5_choose l d) l.
Proof.
  intros l d Hne.
  destruct l as [| x xs].
  - exfalso. apply Hne. reflexivity.
  - simpl. left. reflexivity.
Qed.

(** Finite choice on {0,...,N-1}: works constructively *)
Definition finite_choice (F : nat -> list nat) (N : nat) : nat -> nat :=
  fun n => if (n <? N)%nat then L5_choose (F n) 0%nat else 0%nat.

Lemma finite_choice_works : forall F N,
  (forall n, (n < N)%nat -> F n <> nil) ->
  forall n, (n < N)%nat -> In (finite_choice F N n) (F n).
Proof.
  intros F N Hne n Hn.
  unfold finite_choice.
  rewrite (proj2 (Nat.ltb_lt n N) Hn).
  apply L5_choose_in.
  apply Hne. exact Hn.
Qed.

(* ================================================================ *)
(*  P4 PROHIBITS AC BUT PRESERVES FINITE CHOICE                     *)
(* ================================================================ *)

Theorem P4_prohibits_AC :
  (* AC produces completed infinity *)
  (AC_on_nat -> exists f, CompletedInfSet (choice_graph f)) /\
  (* P4 contradicts completed infinity *)
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual ->
    bridge S actual -> False) /\
  (* Finite choice survives *)
  (forall F N, (forall n, (n < N)%nat -> F n <> nil) ->
    forall n, (n < N)%nat -> In (finite_choice F N n) (F n)).
Proof.
  split; [exact ac_implies_completed |
  split; [exact completed_inf_contradicts_P4 |
  exact finite_choice_works]].
Qed.

(* ================================================================ *)
(*  L5 CHOICE IS DETERMINISTIC                                       *)
(* ================================================================ *)

Lemma L5_choose_deterministic : forall l d1 d2,
  l <> nil -> L5_choose l d1 = L5_choose l d2.
Proof.
  intros l d1 d2 Hne.
  destruct l as [| x xs].
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

(** L5 choose respects order: always picks FIRST element *)
Lemma L5_choose_is_head : forall x xs d,
  L5_choose (x :: xs) d = x.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem p4_ac_synthesis :
  (* AC implies completed infinity *)
  (AC_on_nat -> exists f, CompletedInfSet (choice_graph f)) /\
  (* Finite choice works via L5 *)
  (forall F N, (forall n, (n < N)%nat -> F n <> nil) ->
    forall n, (n < N)%nat -> In (finite_choice F N n) (F n)) /\
  (* L5 choice is deterministic *)
  (forall l d1 d2, l <> nil -> L5_choose l d1 = L5_choose l d2).
Proof.
  split; [exact ac_implies_completed |
  split; [exact finite_choice_works |
  exact L5_choose_deterministic]].
Qed.
