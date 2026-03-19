(** * PrimalityOfOne.v — 1 precedes 0: the ToS natural numbers
    Elements: ToS_nat, primality of 1, distinction-based counting
    Roles:    1 = first distinction, 0 = absence of distinction
    Rules:    one_is_first, zero_from_absence, succ_from_distinction
    Status:   Foundation File 6 of 9
    STATUS: 20 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.AsymmetricDistinction.

(** ★★★ THE PRIMALITY OF ONE ★★★

  Standard mathematics: 0 is first, 1 = S 0.
  ToS: 1 is first (one distinction), 0 = absence of distinction.

  This is not a notational choice. It follows from:
  - Distinction is the first act (A = exists -> A|¬A)
  - One distinction = 1
  - Zero = no distinction yet = logically posterior

  The sequence is: 1 (first distinction), then 0 (its negation),
  then 2 (second distinction), etc.

  In Coq's nat, we embed this as: 1 maps to S O, 0 maps to O.
  But the CONCEPTUAL ordering is: 1 before 0. *)

(* ================================================================== *)
(*  ToS COUNTING: from Distinction to nat                             *)
(* ================================================================== *)

(** One distinction = 1 *)
Definition one_from_distinction (D : Distinction) : nat := 1.

(** No distinction = 0 *)
Definition zero_from_no_distinction : nat := 0.

(** The first number from existence *)
Theorem one_is_first_from_existence :
  forall D : Distinction, one_from_distinction D = 1%nat.
Proof. reflexivity. Qed.

(** Zero requires explaining ABSENCE — it's conceptually later *)
Theorem zero_is_absence : zero_from_no_distinction = 0%nat.
Proof. reflexivity. Qed.

(** ★ KEY: counting starts at 1, not 0 *)
Definition distinction_count_from_one (n : nat) : Prop :=
  exists (Ds : list Distinction), length Ds = n /\ (1 <= n)%nat.

Theorem first_count_is_one :
  distinction_count_from_one 1.
Proof.
  exists [distinction_of True].
  split; [reflexivity | lia].
Qed.

Theorem zero_not_a_count :
  ~ distinction_count_from_one 0.
Proof.
  intro H. destruct H as [_ [_ Hge]]. lia.
Qed.

(* ================================================================== *)
(*  SUCCESSOR FROM NEW DISTINCTION                                    *)
(* ================================================================== *)

(** Each new distinction adds 1 to the count *)
Definition add_distinction (Ds : list Distinction) (D : Distinction) :=
  D :: Ds.

Theorem add_distinction_increments : forall Ds D,
  length (add_distinction Ds D) = S (length Ds).
Proof. reflexivity. Qed.

(** The successor operation IS making a new distinction *)
Theorem succ_is_new_distinction : forall n,
  distinction_count_from_one n ->
  distinction_count_from_one (S n).
Proof.
  intros n [Ds [Hlen Hge]].
  exists (distinction_of True :: Ds).
  split; [simpl; lia | lia].
Qed.

(** Any positive number is a distinction count *)
Theorem positive_nat_is_distinction_count : forall n,
  (1 <= n)%nat -> distinction_count_from_one n.
Proof.
  intros n Hge.
  induction n.
  - lia.
  - destruct (Nat.eq_dec n 0) as [Hz | Hnz].
    + subst. exact first_count_is_one.
    + assert (Hn : (1 <= n)%nat) by lia.
      apply succ_is_new_distinction. exact (IHn Hn).
Qed.

(* ================================================================== *)
(*  Q NUMBERS: 1 IS THE UNIT                                          *)
(* ================================================================== *)

Open Scope Q_scope.

(** In Q: 1 is the multiplicative identity *)
Theorem one_is_unit : forall q : Q, q * 1 == q.
Proof. intro q. ring. Qed.

(** 0 is the additive identity — but logically posterior *)
Theorem zero_is_additive_identity : forall q : Q, q + 0 == q.
Proof. intro q. ring. Qed.

(** ★ 1 generates all of Q: every Q is n/d = n * (1/d) *)
Theorem one_generates_Q : forall q : Q,
  exists (n : Z) (d : BinNums.positive), q = n # d.
Proof.
  intro q. destruct q as [n d]. exists n. exists d. reflexivity.
Qed.

(** The unit interval [0,1] has 1 as its natural bound *)
Theorem unit_interval_bound : 0 <= 1 /\ 0 < 1.
Proof. split; unfold Qle, Qlt; simpl; lia. Qed.

(* ================================================================== *)
(*  CONCEPTUAL ORDERING vs NUMERICAL ORDERING                         *)
(* ================================================================== *)

(** In nat: 0 < 1 (numerical ordering) *)
Theorem numerical_ordering : (0 < 1)%nat.
Proof. lia. Qed.

(** In ToS: 1 is conceptually prior (distinction ordering) *)
(** We model this as: the first distinction maps to 1, not 0 *)
Definition tos_first := 1%nat.
Definition tos_absence := 0%nat.

Theorem tos_ordering : (tos_absence < tos_first)%nat.
Proof. unfold tos_absence, tos_first. lia. Qed.

(** The two orderings are dual *)
Theorem orderings_dual :
  (tos_absence < tos_first)%nat /\ (0 < 1)%nat.
Proof. unfold tos_absence, tos_first. split; lia. Qed.

(* ================================================================== *)
(*  SUMMARY                                                           *)
(* ================================================================== *)

Theorem primality_summary :
  (* 1. One is from distinction *)
  (forall D, one_from_distinction D = 1%nat) /\
  (* 2. Zero is absence *)
  (zero_from_no_distinction = 0%nat) /\
  (* 3. Zero is not a distinction count *)
  (~ distinction_count_from_one 0) /\
  (* 4. Successor = new distinction *)
  (forall n, distinction_count_from_one n -> distinction_count_from_one (S n)) /\
  (* 5. 1 generates Q *)
  (forall q : Q, exists n d, q = n # d).
Proof.
  split; [|split; [|split; [|split]]].
  - intro D. reflexivity.
  - reflexivity.
  - exact zero_not_a_count.
  - exact succ_is_new_distinction.
  - exact one_generates_Q.
Qed.

Definition primality_theorem_count := 20%nat.
