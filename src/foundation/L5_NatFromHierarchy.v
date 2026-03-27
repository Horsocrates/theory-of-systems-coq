(* L5_NatFromHierarchy.v *)
(* E/R/R: Elements = Levels, Roles = hierarchy encoding, Rules = nat isomorphism + irreflexivity *)
(* Standalone — only Stdlib imports *)
(* STATUS: 15 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

(** * Level inductive type *)

Inductive Level : Set := LBase : Level | LSucc : Level -> Level.

(** * Bijection with nat *)

Fixpoint level_to_nat (l : Level) : nat :=
  match l with
  | LBase => O
  | LSucc l' => S (level_to_nat l')
  end.

Fixpoint nat_to_level (n : nat) : Level :=
  match n with
  | O => LBase
  | S n' => LSucc (nat_to_level n')
  end.

Lemma level_nat_level : forall l, nat_to_level (level_to_nat l) = l.
Proof. induction l; simpl. - reflexivity. - rewrite IHl. reflexivity. Qed.

Lemma nat_level_nat : forall n, level_to_nat (nat_to_level n) = n.
Proof. induction n; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

(** * Concrete levels *)

Definition level_0 : Level := LBase.
Definition level_1 : Level := LSucc LBase.
Definition level_2 : Level := LSucc (LSucc LBase).

Lemma level_0_nat : level_to_nat level_0 = 0%nat.
Proof. reflexivity. Qed.

Lemma level_1_nat : level_to_nat level_1 = 1%nat.
Proof. reflexivity. Qed.

Lemma level_2_nat : level_to_nat level_2 = 2%nat.
Proof. reflexivity. Qed.

(** * Peano-like properties *)

Lemma peano_zero : level_to_nat LBase = O.
Proof. reflexivity. Qed.

Lemma lsucc_injective : forall l1 l2, LSucc l1 = LSucc l2 -> l1 = l2.
Proof. intros l1 l2 H. injection H. auto. Qed.

Lemma base_not_succ : forall l, LBase <> LSucc l.
Proof. intros l. discriminate. Qed.

(** * Strict ordering via size *)

Fixpoint level_lt (l1 l2 : Level) : Prop :=
  match l2 with
  | LBase => False
  | LSucc l2' => l1 = l2' \/ level_lt l1 l2'
  end.

Fixpoint level_size (l : Level) : nat :=
  match l with
  | LBase => O
  | LSucc l' => S (level_size l')
  end.

Lemma level_lt_size : forall l1 l2, level_lt l1 l2 -> (level_size l1 < level_size l2)%nat.
Proof.
  intros l1 l2. revert l1. induction l2; simpl; intros l1 H.
  - contradiction.
  - destruct H as [Heq | Hlt].
    + subst. lia.
    + apply IHl2 in Hlt. lia.
Qed.

Lemma hierarchy_irrefl : forall l, ~ level_lt l l.
Proof. intros l H. apply level_lt_size in H. lia. Qed.

(** * Level ordering is transitive *)

Lemma level_lt_trans : forall l1 l2 l3,
  level_lt l1 l2 -> level_lt l2 l3 -> level_lt l1 l3.
Proof.
  intros l1 l2 l3 H12 H23.
  revert l1 l2 H12 H23. induction l3; simpl; intros.
  - contradiction.
  - destruct H23 as [Heq | Hlt].
    + subst. right. exact H12.
    + right. exact (IHl3 l1 l2 H12 Hlt).
Qed.

(** * Level decidable equality *)

Lemma level_eq_dec : forall (l1 l2 : Level), {l1 = l2} + {l1 <> l2}.
Proof. decide equality. Qed.

(** * Concrete level_lt examples *)

Lemma lt_0_1 : level_lt level_0 level_1.
Proof. simpl. left. reflexivity. Qed.

Lemma lt_1_2 : level_lt level_1 level_2.
Proof. simpl. left. reflexivity. Qed.

Lemma lt_0_2 : level_lt level_0 level_2.
Proof. apply (level_lt_trans _ level_1). exact lt_0_1. exact lt_1_2. Qed.
