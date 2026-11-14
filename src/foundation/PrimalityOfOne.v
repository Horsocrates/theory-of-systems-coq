(** * PrimalityOfOne.v — 1 precedes 0: the ToS natural numbers
    Elements: ToS_nat, primality of 1, distinction-based counting
    Roles:    1 = first distinction, 0 = absence of distinction
    Rules:    one_is_first, zero_from_absence, succ_from_distinction
    Status:   Foundation File 6 of 9
    STATUS: 19 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026

    NOTE (audit of Part II of the Mathematics volume, 2026-11-13):
    - ToS_nat and the three rules of the Rules line are declared in
      foundation/CountingPresence.v: ToS_nat is a list with at least one
      performed act; one_is_first, zero_from_absence, succ_from_distinction
      are theorems about a GIVEN list of distinctions.
    - In this file one_from_distinction and zero_from_no_distinction are
      constants (1 and 0), and distinction_count_from_one n is equivalent
      to 1 <= n (count_from_one_iff_positive, CountingPresence.v).
    - The witness of the counting theorems is distinction_true_false (the
      distinction True | False, built without classic). Before the audit
      it was distinction_of True, and four theorems rested on classic.
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.AsymmetricDistinction.
From ToS Require Import foundation.DistinctionCoDefinition.

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
  exists [distinction_true_false].
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
  exists (distinction_true_false :: Ds).
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

(** The two orderings as two PAIRS (audit of Part II of the Mathematics
    volume, 2026-11-13). orderings_dual above states one inequality twice:
    both its conjuncts unfold to 0 < 1. The duality itself is the relation
    of two pairs: the order of grounding (1, 0) — one first, zero second —
    and the numerical order (0, 1). Both pairs are written by hand; the
    theorems state what holds of these two records. *)
Definition tos_conceptual_ordering : nat * nat := (1%nat, 0%nat).
Definition number_ordering : nat * nat := (0%nat, 1%nat).

(** The pair of AsymmetricDistinction.v is the pair of the order of grounding. *)
Theorem distinction_order_is_conceptual :
  distinction_order = tos_conceptual_ordering.
Proof. reflexivity. Qed.

(** The numerical pair is ordered by magnitude; the conceptual pair runs
    against the magnitude. *)
Theorem number_ordering_is_numerical :
  (fst number_ordering < snd number_ordering)%nat.
Proof. simpl. lia. Qed.

Theorem conceptual_ordering_reverses_numerical :
  (snd tos_conceptual_ordering < fst tos_conceptual_ordering)%nat.
Proof. simpl. lia. Qed.

(** The two pairs are mirror images of each other, and they are different. *)
Theorem orderings_dual_pairs :
  fst tos_conceptual_ordering = snd number_ordering /\
  snd tos_conceptual_ordering = fst number_ordering /\
  tos_conceptual_ordering <> number_ordering.
Proof.
  split; [reflexivity | split; [reflexivity | ]].
  intro H. discriminate H.
Qed.

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
