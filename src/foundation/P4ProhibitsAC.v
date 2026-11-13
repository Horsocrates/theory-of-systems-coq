(** * P4ProhibitsAC.v — P4 cuts off the choice function read as a completed graph
    Elements: AC_on_nat, choice_graph (pairs index-value), graph_indices,
              finite_choice, L5_choose
    Roles:    the choice function as a RULE (answers any presented index) vs
              the same function as a completed GRAPH (all pairs at once)
    Rules:    completed graph + P4 stage bound + bridge → contradiction;
              the rule reading stays (choice from nonempty lists = head)
    STATUS:   15 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: April 2026 (graph made genuine: November 2026)

    THE ARGUMENT:
    AC_on_nat: ∀F: nat→list nat, (∀n, F(n) ≠ []) → ∃f: nat→nat, ∀n, f(n) ∈ F(n).
    The graph of f is the collection of pairs {(n, f(n)) | n ∈ nat}.
    It holds a pair at EVERY index: read as one collected whole it is a
    completed infinite set, and together with the P4 stage bound and the
    bridge this gives a contradiction (ac_completed_graph_contradicts_P4).

    WHAT IS AND IS NOT PROVED (honest scope):
    - AC_on_nat itself is NOT refuted and cannot be: for nonempty LISTS it is
      a theorem (AC_on_nat_as_rule: take the head of each list).
    - Nothing in the contradiction is special to choice: the graph of ANY
      total function, read as completed, contradicts the P4 bound under the
      bridge (completed_graph_contradicts_P4).  What P4 cuts off is the
      READING "function = completed graph", not the function as a rule.
    - Finite choice (on {0,...,N-1}) works constructively via L5 (head of list).

    Nov 2026: [choice_graph f] used to be [fun n => True], a predicate that
    did not look at [f], so the conclusion of [ac_implies_completed] held
    without its premise.  The graph is now the graph, and the theorem ties
    the choice function to the family it chooses from.
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

(** The graph of a function: the collection of pairs (index, value). *)
Definition choice_graph (f : nat -> nat) : nat -> nat -> Prop :=
  fun n m => m = f n.

(** The indices at which a collection of pairs holds a pair. *)
Definition graph_indices (G : nat -> nat -> Prop) : nat -> Prop :=
  fun n => exists m, G n m.

(** It is the graph of a function: one value per index. *)
Lemma choice_graph_functional : forall (f : nat -> nat) (n m1 m2 : nat),
  choice_graph f n m1 -> choice_graph f n m2 -> m1 = m2.
Proof.
  unfold choice_graph. intros f n m1 m2 H1 H2. rewrite H1, H2. reflexivity.
Qed.

(** The graph of a total function holds a pair at EVERY index:
    read as one collected whole, it is a completed infinite set. *)
Lemma choice_graph_completed : forall f : nat -> nat,
  CompletedInfSet (graph_indices (choice_graph f)).
Proof.
  intros f n. exists (f n). reflexivity.
Qed.

(* ================================================================ *)
(*  AC IMPLIES COMPLETED INFINITY                                    *)
(* ================================================================ *)

(** "AC on nat produces a completed graph", as one named statement:
    for every family of nonempty lists there is a function whose graph
    (1) consists of pairs (index, element chosen from the list at that index)
    and (2) holds a pair at every index. *)
Definition AC_gives_completed_graph : Prop :=
  AC_on_nat ->
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  exists f : nat -> nat,
    (forall n m, choice_graph f n m -> In m (F n)) /\
    CompletedInfSet (graph_indices (choice_graph f)).

Theorem ac_implies_completed :
  AC_on_nat ->
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  exists f : nat -> nat,
    (forall n m, choice_graph f n m -> In m (F n)) /\
    CompletedInfSet (graph_indices (choice_graph f)).
Proof.
  intros HAC F Hne.
  destruct (HAC F Hne) as [f Hf].
  exists f. split.
  - intros n m Hg. unfold choice_graph in Hg. rewrite Hg. apply Hf.
  - apply choice_graph_completed.
Qed.

(* ================================================================ *)
(*  THE COMPLETED GRAPH CONTRADICTS P4                               *)
(* ================================================================ *)

(** Reading the graph of ANY total function as a completed whole
    (bridge: every index of the graph is actual at stage 0) contradicts
    the P4 stage bound.  Nothing here is special to choice: what P4 cuts
    off is the completed-graph READING, not the function as a rule. *)
Theorem completed_graph_contradicts_P4 :
  forall (f : nat -> nat) (actual : nat -> nat -> Prop),
  P4_stage_bounded actual ->
  bridge (graph_indices (choice_graph f)) actual ->
  False.
Proof.
  intros f actual HP4 Hb.
  exact (completed_inf_contradicts_P4 (graph_indices (choice_graph f)) actual
           (choice_graph_completed f) HP4 Hb).
Qed.

(** The whole argument in one theorem: AC on nat gives a choice function;
    if the graph of every choice function for the family is read as
    completed (bridge), the P4 stage bound is contradicted. *)
Theorem ac_completed_graph_contradicts_P4 :
  AC_on_nat ->
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  forall actual : nat -> nat -> Prop,
  P4_stage_bounded actual ->
  (forall f : nat -> nat, (forall n, In (f n) (F n)) ->
     bridge (graph_indices (choice_graph f)) actual) ->
  False.
Proof.
  intros HAC F Hne actual HP4 Hb.
  destruct (HAC F Hne) as [f Hf].
  exact (completed_graph_contradicts_P4 f actual HP4 (Hb f Hf)).
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

(** Read as a RULE, AC on nat for nonempty lists is a theorem: the head of
    each list.  (The same fact: P4_Eliminates_AC.AC_is_L5.)  So the
    prohibition above is not a refutation of AC_on_nat; it concerns the
    completed-graph reading of the choice function. *)
Lemma AC_on_nat_as_rule : AC_on_nat.
Proof.
  intros F Hne.
  exists (fun n => L5_choose (F n) 0%nat).
  intro n. apply L5_choose_in. apply Hne.
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
  (* AC produces a choice function whose graph is a completed infinite set *)
  AC_gives_completed_graph /\
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
  (* AC implies a completed graph *)
  AC_gives_completed_graph /\
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

(* ================================================================ *)
(*  Nov 2026: THE TWO READINGS OF A GRAPH, AS THEOREMS               *)
(* ================================================================ *)

(* Elements: a collection S of indices (here: the indices of a graph) and a
             staged actuality.
   Roles:    S read as a COMPLETED WHOLE (bridge: every member actual at
             stage 0) vs S read as a RULE ON DEMAND (every member becomes
             actual at SOME stage).
   Rules:    the first reading entails the second and not conversely; under
             the P4 stage bound the first is impossible, the second is
             realised by the stages 0..n. *)

(** The rule reading: every member becomes actual at some stage. *)
Definition rule_reading (S : nat -> Prop) (actual : nat -> nat -> Prop) : Prop :=
  forall n, S n -> exists stage, actual stage n.

(** Choice from nonempty lists, read as a rule, is compatible with P4. *)
Theorem choice_as_rule_compatible_with_P4 :
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  exists (f : nat -> nat) (actual : nat -> nat -> Prop),
    (forall n, In (f n) (F n)) /\
    P4_stage_bounded actual /\
    rule_reading (graph_indices (choice_graph f)) actual.
Proof.
  intros F Hne.
  exists (fun n => L5_choose (F n) 0%nat), (fun stage n => (n <= stage)%nat).
  split; [| split].
  - intro n. apply L5_choose_in. apply Hne.
  - intro stage. exists stage. intros n H. exact H.
  - intros n _. exists n. apply Nat.le_refl.
Qed.

(** P4 cuts off the completed reading of EVERY choice function for the family
    and keeps the rule reading of one. *)
Theorem P4_cuts_completed_keeps_rule :
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  (forall (f : nat -> nat) (actual : nat -> nat -> Prop),
     (forall n, In (f n) (F n)) ->
     P4_stage_bounded actual ->
     ~ bridge (graph_indices (choice_graph f)) actual) /\
  (exists (f : nat -> nat) (actual : nat -> nat -> Prop),
     (forall n, In (f n) (F n)) /\
     P4_stage_bounded actual /\
     rule_reading (graph_indices (choice_graph f)) actual).
Proof.
  intros F Hne. split.
  - intros f actual _ HP4 Hb. exact (completed_graph_contradicts_P4 f actual HP4 Hb).
  - exact (choice_as_rule_compatible_with_P4 F Hne).
Qed.

(** The completed reading demands strictly more than the rule reading: it
    entails it, and for the graph of any function there is a stage-bounded
    actuality under which the rule reading holds and the bridge fails. *)
Theorem completed_reading_strictly_stronger :
  (forall S actual, bridge S actual -> rule_reading S actual) /\
  (forall f : nat -> nat, exists actual : nat -> nat -> Prop,
     P4_stage_bounded actual /\
     rule_reading (graph_indices (choice_graph f)) actual /\
     ~ bridge (graph_indices (choice_graph f)) actual).
Proof.
  split.
  - intros S actual Hb n Hn. exists 0%nat. apply Hb. exact Hn.
  - intro f. exists (fun stage n => (n <= stage)%nat).
    assert (HP4 : P4_stage_bounded (fun stage n => (n <= stage)%nat)).
    { intro stage. exists stage. intros n H. exact H. }
    split; [exact HP4 | split].
    + intros n _. exists n. apply Nat.le_refl.
    + intro Hb. exact (completed_graph_contradicts_P4 f _ HP4 Hb).
Qed.
