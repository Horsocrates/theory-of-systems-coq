(** * CountabilityQValues.v — The countability of the rationals at the level
      of VALUES: equal fractions receive one index

    E/R/R reading (done before coding; audit of Part III of the Mathematics
    volume, chapter III.3, places 3.1, 3.2 and place 2.3 of chapter III.2,
    2026-11-14):

    Elements: the natural indices; the fractions (records of Q); the nodes
              of the Calkin-Wilf tree — pairs of positive numbers.
    Roles:    a rational VALUE — a class of fractions equal by Qeq; its
              reduced fraction — the representative; the index of a value.
    Rules:    the walk enum_Q and its inverse index_of_Q (Countability_Q.v);
              the index is taken by the reduced fraction (Qred).
    Proved:   (1) the index depends on the value only, the walk repeats no
                  value, different values receive different indices — so
                  nat and the rational values are in bijection (the two
                  round trips of Q_bijection alone do not give this: a
                  counter-scheme is included);
              (2) a positive value has exactly one coprime pair, and every
                  positive value stands in the positive walk exactly once;
              (3) the positive walk is one-to-one with the COPRIME pairs,
                  not with the whole type QPos: the pair (2, 4) is not
                  reached;
              (4) the result of path_to_node_fuel does not depend on the
                  supply, for every pair.
    P4 diagnostic ("could it be otherwise?"): finite indices and fractions
              only; nothing completed. Forced: (1)-(4). NOT claimed: a
              quotient type of Q (a value is a class by the relation Qeq);
              a completed set of all rationals; a general theorem "every
              collection of finite expressions is enumerable".

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qreduction.
From Stdlib Require Qcanon.
From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.Pnat.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

From ToS Require Import Countability_Q.

(* Countability_Q.v leaves positive_scope open. *)
Close Scope positive_scope.

(* ========================================================================= *)
(*  1. THE BIJECTION nat <-> Q AT THE LEVEL OF VALUES (Q UP TO Qeq)          *)
(* ========================================================================= *)

(** The index depends on the VALUE only: 2#4 and 1#2 receive one index. *)
Lemma index_of_Q_Qeq : forall q q' : Q, q == q' -> index_of_Q q = index_of_Q q'.
Proof.
  intros q q' H. unfold index_of_Q.
  rewrite (Qred_complete q q' H). reflexivity.
Qed.

(** The walk repeats no rational value. *)
Theorem enum_Q_Qeq_injective : forall n m : nat, enum_Q n == enum_Q m -> n = m.
Proof.
  intros n m H.
  transitivity (index_of_Q (enum_Q n)); [ symmetry; apply index_of_Q_enum_id | ].
  transitivity (index_of_Q (enum_Q m)); [ | apply index_of_Q_enum_id ].
  apply index_of_Q_Qeq. exact H.
Qed.

(** Different values receive different indices. *)
Theorem index_of_Q_inj_Qeq : forall q q' : Q, index_of_Q q = index_of_Q q' -> q == q'.
Proof.
  intros q q' H.
  transitivity (enum_Q (index_of_Q q)); [ symmetry; apply enum_Q_index_id | ].
  rewrite H. apply enum_Q_index_id.
Qed.

(** The bijection between nat and the rational VALUES, in full: the two round trips of
    Q_bijection, and the index is a function of the value and separates the values. *)
Theorem Q_bijection_values :
  (forall n : nat, index_of_Q (enum_Q n) = n) /\
  (forall q : Q, enum_Q (index_of_Q q) == q) /\
  (forall q q' : Q, q == q' <-> index_of_Q q = index_of_Q q') /\
  (forall n m : nat, enum_Q n == enum_Q m <-> n = m).
Proof.
  split; [ exact index_of_Q_enum_id | ].
  split; [ exact enum_Q_index_id | ].
  split.
  - intros q q'. split; [ apply index_of_Q_Qeq | apply index_of_Q_inj_Qeq ].
  - intros n m. split; [ apply enum_Q_Qeq_injective | intros ->; reflexivity ].
Qed.

(* ========================================================================= *)
(*  2. POSITIVE VALUES: EVERY VALUE STANDS IN THE WALK EXACTLY ONCE          *)
(* ========================================================================= *)

(** A positive value has exactly one coprime pair. *)
Lemma qpos_coprime_Qeq_eq : forall a b c d : positive,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  Z.gcd (Z.pos c) (Z.pos d) = 1%Z ->
  (Z.pos a # b) == (Z.pos c # d) -> (a, b) = (c, d).
Proof.
  intros a b c d H1 H2 H.
  apply Qred_complete in H.
  rewrite (Qred_id_pos a b H1), (Qred_id_pos c d H2) in H.
  injection H as Ha Hb. subst. reflexivity.
Qed.

Theorem enum_QPos_value_injective : forall n m : nat,
  qpos_to_Q (enum_QPos n) == qpos_to_Q (enum_QPos m) -> n = m.
Proof.
  intros n m H. apply enum_injective.
  pose proof (enum_coprime n) as Hn. pose proof (enum_coprime m) as Hm.
  destruct (enum_QPos n) as [a b]. destruct (enum_QPos m) as [c d].
  cbn [qpos_to_Q] in H. apply qpos_coprime_Qeq_eq; assumption.
Qed.

Theorem enum_QPos_value_surjective : forall q : Q,
  0 < q -> exists n : nat, qpos_to_Q (enum_QPos n) == q.
Proof.
  intros q Hq.
  pose proof (Qred_correct q) as Hr.
  pose proof (Qred_coprime q) as Hc.
  assert (Hpos : 0 < Qred q) by (rewrite Hr; exact Hq).
  remember (Qred q) as r eqn:E. destruct r as [z d].
  cbn [Qnum Qden] in Hc.
  destruct z as [ | a | a ].
  - exfalso. unfold Qlt in Hpos. cbn in Hpos. lia.
  - destruct (enum_surjective a d Hc) as [n Hn]. exists n.
    rewrite Hn. cbn [qpos_to_Q]. exact Hr.
  - exfalso. unfold Qlt in Hpos. cbn in Hpos. lia.
Qed.

(** Every positive rational VALUE stands in the walk exactly once. *)
Theorem enum_QPos_each_value_once : forall q : Q, 0 < q ->
  exists n : nat, qpos_to_Q (enum_QPos n) == q /\
    forall m : nat, qpos_to_Q (enum_QPos m) == q -> m = n.
Proof.
  intros q Hq. destruct (enum_QPos_value_surjective q Hq) as [n Hn].
  exists n. split; [ exact Hn | ].
  intros m Hm. apply enum_QPos_value_injective. rewrite Hm, Hn. reflexivity.
Qed.

(* ========================================================================= *)
(*  3. nat <-> THE COPRIME PAIRS, NOT THE WHOLE TYPE QPos                    *)
(* ========================================================================= *)

(** The walk is one-to-one with the COPRIME pairs: every pair of the walk is coprime, and
    the two passages are mutually inverse on the coprime pairs. *)
Theorem enum_QPos_bijection_coprime :
  (forall n : nat, let (a, b) := enum_QPos n in Z.gcd (Z.pos a) (Z.pos b) = 1%Z) /\
  (forall n : nat, index_of_QPos (enum_QPos n) = n) /\
  (forall a b : positive, Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
     enum_QPos (index_of_QPos (a, b)) = (a, b)).
Proof.
  split; [ exact enum_coprime | ].
  split; [ exact index_of_QPos_enum | exact enum_QPos_index ].
Qed.

(** On the whole type QPos there is no bijection: the walk does not reach the reducible
    pair (2, 4), and the index does not separate (2, 4) from (1, 2). *)
Lemma enum_QPos_misses_2_4 : forall n : nat, enum_QPos n <> (2, 4)%positive.
Proof.
  intros n H. pose proof (enum_coprime n) as Hc. rewrite H in Hc.
  vm_compute in Hc. discriminate.
Qed.

Lemma index_of_QPos_not_injective :
  index_of_QPos (2, 4)%positive = index_of_QPos (1, 2)%positive /\ (2, 4)%positive <> (1, 2)%positive.
Proof. split; [ vm_compute; reflexivity | discriminate ]. Qed.

Lemma roundtrip_fails_off_coprime :
  cw_node (path_to_node (2, 4)%positive) <> (2, 4)%positive.
Proof. vm_compute. discriminate. Qed.

(* ========================================================================= *)
(*  4. TWO ROUND TRIPS ALONE DO NOT GIVE A BIJECTION OF VALUES               *)
(* ========================================================================= *)

(** A scheme: two round trips hold, and yet a value is repeated — so the statement
    "equal values receive one index" does not follow from the round trips alone. *)
Lemma roundtrips_do_not_force_value_injectivity :
  exists (R : nat -> nat -> Prop) (E I : nat -> nat),
    (forall x, R x x) /\ (forall x y, R x y -> R y x) /\
    (forall x y z, R x y -> R y z -> R x z) /\
    (forall n, I (E n) = n) /\ (forall x, R (E (I x)) x) /\
    R (E 0%nat) (E 1%nat) /\ 0%nat <> 1%nat /\ I 0%nat <> I 1%nat.
Proof.
  exists (fun x y => Nat.div2 x = Nat.div2 y), (fun n => n), (fun n => n).
  repeat split; try reflexivity; try discriminate.
  - intros x y H; symmetry; exact H.
  - intros x y z H1 H2; rewrite H1; exact H2.
Qed.

(* ========================================================================= *)
(*  5. THE FUEL: THE RESULT DOES NOT DEPEND ON THE SUPPLY, FOR EVERY PAIR    *)
(* ========================================================================= *)

(** The result of path_to_node_fuel does not depend on the supply once it is at least
    a + b — for EVERY pair, reducible ones included. *)
Lemma path_fuel_indep : forall (f1 f2 : nat) (a b : positive),
  (f1 >= Pos.to_nat a + Pos.to_nat b)%nat ->
  (f2 >= Pos.to_nat a + Pos.to_nat b)%nat ->
  path_to_node_fuel f1 a b = path_to_node_fuel f2 a b.
Proof.
  induction f1 as [ | f1 IH ]; intros f2 a b H1 H2.
  - exfalso. pose proof (Pos2Nat.is_pos a). pose proof (Pos2Nat.is_pos b). lia.
  - destruct f2 as [ | f2 ].
    { exfalso. pose proof (Pos2Nat.is_pos a). pose proof (Pos2Nat.is_pos b). lia. }
    cbn [path_to_node_fuel].
    destruct (Pos.eqb_spec a b) as [ Heq | Hne ]; [ reflexivity | ].
    destruct (Pos.ltb_spec a b) as [ Hlt | Hge ].
    + f_equal. apply IH.
      * rewrite Pos2Nat.inj_sub by exact Hlt. pose proof (Pos2Nat.is_pos a).
        apply Pos2Nat.inj_lt in Hlt. lia.
      * rewrite Pos2Nat.inj_sub by exact Hlt. pose proof (Pos2Nat.is_pos a).
        apply Pos2Nat.inj_lt in Hlt. lia.
    + assert (Hlt : (b < a)%positive) by lia.
      f_equal. apply IH.
      * rewrite Pos2Nat.inj_sub by exact Hlt. pose proof (Pos2Nat.is_pos b).
        apply Pos2Nat.inj_lt in Hlt. lia.
      * rewrite Pos2Nat.inj_sub by exact Hlt. pose proof (Pos2Nat.is_pos b).
        apply Pos2Nat.inj_lt in Hlt. lia.
Qed.
