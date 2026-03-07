(** * FormalLanguages.v — Regular Languages as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: words (list nat), regular expressions
    Roles:    regexp -> LanguageSpec, word -> Instance
    Rules:    matching (constitution: structural pattern matching)
    Status:   matched | unmatched

    Connection: Automata.v (DFA/NFA recognize same languages)

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import stdlib.Automata.

(* ================================================================= *)
(** ** Regular Expressions *)
(* ================================================================= *)

Inductive Regexp : Type :=
  | RE_Empty    (* matches nothing *)
  | RE_Epsilon  (* matches empty string *)
  | RE_Char (c : nat)  (* matches single character *)
  | RE_Union (r1 r2 : Regexp)
  | RE_Concat (r1 r2 : Regexp)
  | RE_Star (r : Regexp).

(* ================================================================= *)
(** ** Matching Relation *)
(* ================================================================= *)

Inductive matches : Regexp -> list nat -> Prop :=
  | M_Epsilon : matches RE_Epsilon []
  | M_Char : forall c, matches (RE_Char c) [c]
  | M_Union_L : forall r1 r2 w, matches r1 w -> matches (RE_Union r1 r2) w
  | M_Union_R : forall r1 r2 w, matches r2 w -> matches (RE_Union r1 r2) w
  | M_Concat : forall r1 r2 w1 w2, matches r1 w1 -> matches r2 w2 ->
      matches (RE_Concat r1 r2) (w1 ++ w2)
  | M_Star_Nil : forall r, matches (RE_Star r) []
  | M_Star_Cons : forall r w1 w2, matches r w1 -> matches (RE_Star r) w2 ->
      matches (RE_Star r) (w1 ++ w2).

(* ================================================================= *)
(** ** Nullable Check *)
(* ================================================================= *)

Fixpoint re_nullable (r : Regexp) : bool :=
  match r with
  | RE_Empty => false
  | RE_Epsilon => true
  | RE_Char _ => false
  | RE_Union r1 r2 => re_nullable r1 || re_nullable r2
  | RE_Concat r1 r2 => re_nullable r1 && re_nullable r2
  | RE_Star _ => true
  end.

(* ================================================================= *)
(** ** Regexp Size (for induction) *)
(* ================================================================= *)

Fixpoint re_size (r : Regexp) : nat :=
  match r with
  | RE_Empty => 1
  | RE_Epsilon => 1
  | RE_Char _ => 1
  | RE_Union r1 r2 => 1 + re_size r1 + re_size r2
  | RE_Concat r1 r2 => 1 + re_size r1 + re_size r2
  | RE_Star r1 => 1 + re_size r1
  end.

(* ================================================================= *)
(** ** Theorems *)
(* ================================================================= *)

(** 1. RE_Empty matches nothing *)
Lemma empty_matches_nothing : forall w, ~ matches RE_Empty w.
Proof.
  intros w H. inversion H.
Qed.

(** 2. RE_Epsilon matches the empty string *)
Lemma epsilon_matches_nil : matches RE_Epsilon [].
Proof.
  apply M_Epsilon.
Qed.

(** 3. RE_Epsilon matches only the empty string *)
Lemma epsilon_matches_only_nil : forall w, matches RE_Epsilon w -> w = [].
Proof.
  intros w H. inversion H. reflexivity.
Qed.

(** 4. RE_Char c matches the singleton [c] *)
Lemma char_matches_singleton : forall c, matches (RE_Char c) [c].
Proof.
  intro c. apply M_Char.
Qed.

(** 5. RE_Char c matches only the singleton [c] *)
Lemma char_matches_only_singleton : forall c w, matches (RE_Char c) w -> w = [c].
Proof.
  intros c w H. inversion H. reflexivity.
Qed.

(** 6. RE_Star r always matches the empty string *)
Lemma star_matches_nil : forall r, matches (RE_Star r) [].
Proof.
  intro r. apply M_Star_Nil.
Qed.

(** 7. re_nullable RE_Epsilon = true *)
Lemma re_nullable_epsilon : re_nullable RE_Epsilon = true.
Proof.
  reflexivity.
Qed.

(** 8. re_nullable RE_Empty = false *)
Lemma re_nullable_empty : re_nullable RE_Empty = false.
Proof.
  reflexivity.
Qed.

(** 9. re_nullable (RE_Char c) = false *)
Lemma re_nullable_char : forall c, re_nullable (RE_Char c) = false.
Proof.
  reflexivity.
Qed.

(** 10. re_nullable (RE_Star r) = true *)
Lemma re_nullable_star : forall r, re_nullable (RE_Star r) = true.
Proof.
  reflexivity.
Qed.

(** 11. Nullable soundness: re_nullable r = true -> matches r [] *)
Lemma re_nullable_correct_true : forall r, re_nullable r = true -> matches r [].
Proof.
  induction r; simpl; intro H; try discriminate.
  - apply M_Epsilon.
  - apply orb_true_iff in H. destruct H as [H|H].
    + apply M_Union_L. apply IHr1. exact H.
    + apply M_Union_R. apply IHr2. exact H.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    replace ([] : list nat) with ([] ++ [] : list nat) by reflexivity.
    apply M_Concat; [apply IHr1 | apply IHr2]; assumption.
  - apply M_Star_Nil.
Qed.

(** 12. Nullable completeness: matches r [] -> re_nullable r = true *)
Lemma re_nullable_correct_false : forall r, matches r [] -> re_nullable r = true.
Proof.
  intros r H.
  remember [] as w eqn:Hw.
  induction H; simpl; try discriminate; try reflexivity.
  - (* M_Union_L *)
    rewrite IHmatches; auto.
  - (* M_Union_R *)
    rewrite IHmatches; auto.
    apply orb_true_r.
  - (* M_Concat *)
    apply app_eq_nil in Hw. destruct Hw as [Hw1 Hw2]. subst.
    rewrite IHmatches1, IHmatches2; auto.
Qed.

(** 13. Union example: (0|1) matches [1] *)
Lemma union_comm_example : matches (RE_Union (RE_Char 0) (RE_Char 1)) [1].
Proof.
  apply M_Union_R. apply M_Char.
Qed.

(** 14. Concat example: (0 . 1) matches [0; 1] *)
Lemma concat_example : matches (RE_Concat (RE_Char 0) (RE_Char 1)) [0; 1].
Proof.
  replace [0; 1] with ([0] ++ [1]) by reflexivity.
  apply M_Concat; apply M_Char.
Qed.

(** 15. Star matches one repetition: c* matches [c] *)
Lemma star_one : forall c, matches (RE_Star (RE_Char c)) [c].
Proof.
  intro c.
  replace [c] with ([c] ++ []) by (apply app_nil_r).
  apply M_Star_Cons.
  - apply M_Char.
  - apply M_Star_Nil.
Qed.

(** 16. Star matches two repetitions: c* matches [c; c] *)
Lemma star_two : forall c, matches (RE_Star (RE_Char c)) [c; c].
Proof.
  intro c.
  replace [c; c] with ([c] ++ [c]) by reflexivity.
  apply M_Star_Cons.
  - apply M_Char.
  - apply star_one.
Qed.

(** 17. re_size is always positive *)
Lemma re_size_pos : forall r, re_size r >= 1.
Proof.
  induction r; simpl; lia.
Qed.

(** 18. Union is "monotone": if r1 matches w, so does Union r1 r2 *)
Lemma union_left_inclusion : forall r1 r2 w,
  matches r1 w -> matches (RE_Union r1 r2) w.
Proof.
  intros r1 r2 w H. apply M_Union_L. exact H.
Qed.
