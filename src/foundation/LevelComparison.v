(** * LevelComparison.v — Comparability of Concrete Ordinals
    Elements: nat_to_ord, omega, omega_tower (from Ordinal.v)
    Roles:    ord_le, comparison, embedding, trichotomy
    Rules:    Structural induction on nat, ord_lt constructors
    STATUS:   18 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    Proves comparability results for CONCRETE ordinals
    (nat, omega, omega_tower) using the ord_lt relation.
    General ord_lt a (OSucc a) for limit ordinals is NOT provable
    from the current ord_lt constructors — we focus on what IS provable:
    nat embedding, trichotomy, omega bounds, and domain-level comparisons.
*)

From ToS Require Import foundation.Ordinal.
From ToS Require Import foundation.TransfiniteInduction.
From Stdlib Require Import Lia ZArith List Bool.
Import ListNotations.

(* ================================================================= *)
(* LESS-OR-EQUAL                                                      *)
(* ================================================================= *)

Definition ord_le (a b : Ord) : Prop := ord_lt a b \/ a = b.

Lemma ord_le_refl : forall a, ord_le a a.
Proof. intros a. right. reflexivity. Qed.

Lemma ord_lt_implies_le : forall a b, ord_lt a b -> ord_le a b.
Proof. intros a b H. left. exact H. Qed.

(* ================================================================= *)
(* NAT STRICT ORDERING                                                *)
(* ================================================================= *)

(** Key lemma: nat ordering lifts to ord_lt on nat_to_ord. *)
Lemma nat_to_ord_lt : forall m n : nat,
  (m < n)%nat -> ord_lt (nat_to_ord m) (nat_to_ord n).
Proof.
  intros m. induction m as [| m' IHm].
  - intros n Hn. destruct n as [| n']. lia.
    simpl. apply lt_zero_succ.
  - intros n Hn. destruct n as [| n']. lia.
    simpl. apply lt_succ_mono. apply IHm. lia.
Qed.

(* ================================================================= *)
(* NAT COMPARISON AND TRICHOTOMY                                      *)
(* ================================================================= *)

Lemma nat_le_compare : forall m n : nat,
  (m <= n)%nat -> ord_le (nat_to_ord m) (nat_to_ord n).
Proof.
  intros m n Hmn.
  assert (m = n \/ m < n)%nat as [Heq | Hlt] by lia.
  - subst. right. reflexivity.
  - left. apply nat_to_ord_lt. exact Hlt.
Qed.

Lemma nat_trichotomy : forall m n : nat,
  ord_lt (nat_to_ord m) (nat_to_ord n) \/ m = n \/
  ord_lt (nat_to_ord n) (nat_to_ord m).
Proof.
  intros m n.
  destruct (Nat.lt_trichotomy m n) as [Hlt | [Heq | Hgt]].
  - left. apply nat_to_ord_lt. exact Hlt.
  - right. left. exact Heq.
  - right. right. apply nat_to_ord_lt. exact Hgt.
Qed.

(* ================================================================= *)
(* TWO FINITE HIERARCHIES ARE ALWAYS COMPARABLE                       *)
(* ================================================================= *)

Lemma two_finite_comparable : forall m n : nat,
  ord_le (nat_to_ord m) (nat_to_ord n) \/
  ord_le (nat_to_ord n) (nat_to_ord m).
Proof.
  intros m n.
  destruct (Nat.le_ge_cases m n) as [Hle | Hge].
  - left. apply nat_le_compare. exact Hle.
  - right. apply nat_le_compare. exact Hge.
Qed.

(* ================================================================= *)
(* NAT EMBEDDING PRESERVES AND REFLECTS ORDER                         *)
(* ================================================================= *)

Lemma nat_embed_preserves_lt : forall m n : nat,
  (m < n)%nat -> ord_lt (nat_to_ord m) (nat_to_ord n).
Proof. exact nat_to_ord_lt. Qed.

Lemma nat_embed_reflects_lt : forall m n : nat,
  ord_lt (nat_to_ord m) (nat_to_ord n) -> (m < n)%nat.
Proof.
  intros m. induction m as [| m' IH].
  - intros n H. destruct n. inversion H. lia.
  - intros n H. destruct n as [| n']. simpl in H. inversion H.
    simpl in H. inversion H; subst.
    assert (m' < n')%nat by (apply IH; assumption). lia.
Qed.

(* ================================================================= *)
(* ALL FINITE ORDINALS ARE BELOW OMEGA                                *)
(* ================================================================= *)

Lemma nat_lt_omega_all : forall n : nat,
  ord_lt (nat_to_ord n) omega.
Proof. exact nat_lt_omega. Qed.

(* ================================================================= *)
(* ORD_LT IRREFLEXIVITY                                              *)
(* ================================================================= *)

Lemma ord_lt_irrefl : forall a, ~ ord_lt a a.
Proof.
  intro a.
  apply (well_founded_ind wf_ord_lt (fun x => ~ ord_lt x x)).
  intros x IH Hxx. exact (IH x Hxx Hxx).
Qed.

(* ================================================================= *)
(* ORD_LT WEAKENING FOR FINITE ORDINALS                               *)
(* ================================================================= *)

(** For finite ordinals: a < b implies a < OSucc b. *)
Lemma nat_ord_lt_trans_succ : forall m n,
  ord_lt (nat_to_ord m) (nat_to_ord n) ->
  ord_lt (nat_to_ord m) (OSucc (nat_to_ord n)).
Proof.
  intros m n H.
  apply nat_embed_reflects_lt in H.
  change (OSucc (nat_to_ord n)) with (nat_to_ord (S n)).
  apply nat_to_ord_lt. lia.
Qed.

(* ================================================================= *)
(* ORD_LT MONOTONICITY UNDER ORD_ADD                                  *)
(* ================================================================= *)

(** ord_lt a b implies ord_lt a (ord_add c b) for any c.
    Proof by structural induction on b. *)
Lemma ord_lt_add_r : forall a b c,
  ord_lt a b -> ord_lt a (ord_add c b).
Proof.
  intros a b. revert a.
  induction b as [| b' IHb | f IHf]; intros a c Hab.
  - inversion Hab.
  - simpl. inversion Hab; subst.
    + apply lt_zero_succ.
    + apply lt_succ_mono. apply IHb. assumption.
  - simpl. inversion Hab; subst.
    + eapply lt_to_lim. apply IHf. eassumption.
    + apply lt_succ_to_lim.
      match goal with H : exists _, _ |- _ => destruct H as [m Hm] end.
      exists m. apply IHf. exact Hm.
Qed.

(* ================================================================= *)
(* CONCRETE FINITE COMPARISONS (E/R/R domain levels)                  *)
(* ================================================================= *)

Lemma d1_lt_d5 : ord_lt (nat_to_ord 1) (nat_to_ord 5).
Proof. apply nat_to_ord_lt. lia. Qed.

Lemma d_levels_ordered : forall i j : nat,
  (1 <= i)%nat -> (i < j)%nat -> (j <= 6)%nat ->
  ord_lt (nat_to_ord i) (nat_to_ord j).
Proof. intros. apply nat_to_ord_lt. lia. Qed.

Lemma finite_hierarchy_embeds : forall n : nat,
  (n <= 5)%nat -> ord_le (nat_to_ord n) (nat_to_ord 5).
Proof. intros n Hn. apply nat_le_compare. exact Hn. Qed.

(* ================================================================= *)
(* ZERO IS BELOW ALL SUCCESSORS                                       *)
(* ================================================================= *)

Lemma zero_lt_succ : forall a, ord_lt OZero (OSucc a).
Proof. intros. apply lt_zero_succ. Qed.

(* ================================================================= *)
(* TOS DOMAIN COMPARABILITY                                           *)
(* ================================================================= *)

(** ToS domain levels D1..D6 are encoded as nat_to_ord 1 .. nat_to_ord 6.
    These are fully comparable. *)
Lemma tos_domains_comparable : forall i j : nat,
  (1 <= i)%nat -> (i <= 6)%nat -> (1 <= j)%nat -> (j <= 6)%nat ->
  ord_le (nat_to_ord i) (nat_to_ord j) \/ ord_le (nat_to_ord j) (nat_to_ord i).
Proof. intros. apply two_finite_comparable. Qed.

(** All ToS domains are below omega. *)
Lemma tos_domains_below_omega : forall i : nat,
  (1 <= i)%nat -> (i <= 6)%nat ->
  ord_lt (nat_to_ord i) omega.
Proof. intros. apply nat_lt_omega. Qed.
