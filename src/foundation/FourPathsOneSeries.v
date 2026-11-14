(** * FourPathsOneSeries.v — Four paths, one series: the count of a list,
      the depth of a level, the length of a binary record and the number of
      a position are one number

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, closing step: the words "four paths — one series" of chapters
    II.2-II.5, 2026-11-14):

    Elements: a list of performed distinctions; a level; a binary record; a
              position.
    Roles:    the count of the list; the depth of the level; the length of
              the record; the number of the position — four readings of one
              number.
    Rules:    every path has a base (one) and a step (one more); the step is
              the successor S.
    Proved:   (1) the four bases are 1 and the four steps are S;
              (2) the four ranges coincide: a number is a count from one,
                  a depth, the length of a non-empty record, the number of a
                  position — in each case exactly when it is >= 1;
              (3) the paths are tied DIRECTLY, not only through the number:
                  a list of performed distinctions has a level, a binary
                  record and a position, and its count is the depth of that
                  level, the length of that record and the number of that
                  position;
              (4) ONE more act of distinction moves all four at once: the
                  next level, one more bit, the next position.
    P4 diagnostic ("could it be otherwise?"): finite lists and levels only.
              Forced: (1)-(4). NOT claimed: that the four derivations are
              independent — that is said in the prose of the chapters; that
              the series is BUILT here — all four measures take values in
              the standard type nat, which is given; that the four paths are
              the only ones.

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.PrimalityOfOne.
From ToS Require Import foundation.CountingPresence.
From ToS Require Import foundation.DistinctionSideRole.
From ToS Require Import foundation.Binarity.
From ToS Require Import foundation.BitString.
From ToS Require Import foundation.BitStringCount.
From ToS Require Import foundation.LevelAscent.
From ToS Require Import foundation.StructuralPath.
(* Require WITHOUT Import: the file declares names used elsewhere. *)
From ToS Require foundation.LevelNatIso.

(* Binarity.v leaves Q_scope open. *)
Close Scope Q_scope.
Open Scope nat_scope.

(* ========================================================================= *)
(*  1. FOUR BASES ARE ONE, FOUR STEPS ARE S                                  *)
(* ========================================================================= *)

Lemma pos_number_step : forall p : Position, pos_number (S p) = S (pos_number p).
Proof. reflexivity. Qed.

Theorem four_bases_are_one : forall D : Distinction,
  length [D] = 1 /\ level_depth L1 = 1 /\ bit_length one_bit = 1 /\ pos_number 0 = 1.
Proof. intro D. repeat split. Qed.

Theorem four_steps_are_S :
  (forall (Ds : list Distinction) (D : Distinction),
      length (add_distinction Ds D) = S (length Ds))
  /\ (forall l : Level, level_depth (LS l) = S (level_depth l))
  /\ (forall (b : Bit) (bs : BitString), bit_length (add_bit b bs) = S (bit_length bs))
  /\ (forall p : Position, pos_number (S p) = S (pos_number p)).
Proof.
  split; [exact add_distinction_increments | split; [exact level_depth_LS | split]].
  - exact add_bit_increments_length.
  - exact pos_number_step.
Qed.

(* ========================================================================= *)
(*  2. THE FOUR RANGES COINCIDE                                              *)
(* ========================================================================= *)

(** A number is reached on each of the four paths exactly when it is >= 1. *)
Theorem four_ranges_coincide : forall n : nat,
  (distinction_count_from_one n <-> 1 <= n)
  /\ ((exists l : Level, level_depth l = n) <-> 1 <= n)
  /\ ((exists bs : BitString, bs <> [] /\ bit_length bs = n) <-> 1 <= n)
  /\ ((exists p : Position, pos_number p = n) <-> 1 <= n).
Proof.
  intro n. split; [apply count_from_one_iff_positive | split; [ | split]].
  - split.
    + intros [l H]. rewrite <- H. apply level_depth_ge_one.
    + intro H. exists (level_of_depth n). exact (depth_level_of_depth n H).
  - apply bit_count_iff_positive.
  - split.
    + intros [p H]. rewrite <- H. apply pos_number_positive.
    + apply pos_number_onto_positive.
Qed.

(** Hence the four paths reach the same numbers. *)
Corollary four_paths_reach_the_same_numbers : forall n : nat,
  distinction_count_from_one n <->
  ((exists l : Level, level_depth l = n) /\
   (exists bs : BitString, bs <> [] /\ bit_length bs = n) /\
   (exists p : Position, pos_number p = n)).
Proof.
  intro n. destruct (four_ranges_coincide n) as [H1 [H2 [H3 H4]]]. split.
  - intro H. apply H1 in H. split; [apply H2; exact H | split].
    + apply H3. exact H.
    + apply H4. exact H.
  - intros [H _]. apply H1. apply H2. exact H.
Qed.

(* ========================================================================= *)
(*  3. THE PATHS TIED DIRECTLY                                               *)
(* ========================================================================= *)

(** The level of a list of performed distinctions: the list of one act
    stands at the base, every further act builds one level over. *)
Definition level_of_count (Ds : list Distinction) : Level :=
  level_of_depth (length Ds).

Lemma level_of_count_one : forall D : Distinction, level_of_count [D] = L1.
Proof. reflexivity. Qed.

Lemma level_of_count_step : forall (Ds : list Distinction) (D : Distinction),
  presented Ds -> level_of_count (add_distinction Ds D) = LS (level_of_count Ds).
Proof.
  intros Ds D Hp. unfold level_of_count. rewrite add_distinction_increments.
  apply level_of_depth_succ. apply presented_iff_count_ge_one. exact Hp.
Qed.

Lemma depth_of_level_of_count : forall Ds : list Distinction,
  presented Ds -> level_depth (level_of_count Ds) = length Ds.
Proof.
  intros Ds Hp. unfold level_of_count. apply depth_level_of_depth.
  apply presented_iff_count_ge_one. exact Hp.
Qed.

(** Every level is the level of some list of performed distinctions. *)
Lemma every_level_is_level_of_count : forall l : Level,
  exists Ds : list Distinction, presented Ds /\ level_of_count Ds = l.
Proof.
  intro l.
  destruct (positive_number_is_presented_count (level_depth l) (level_depth_ge_one l))
    as [Ds [Hp Hc]].
  exists Ds. split; [exact Hp | ].
  unfold level_of_count. unfold counts in Hc. rewrite Hc. apply level_of_depth_depth.
Qed.

(** The position of a level: the base stands at the first position (the
    technical index 0, the number 1). *)
Definition position_of_level (l : Level) : Position := LevelNatIso.level_to_nat l.

Lemma position_of_level_base : position_of_level L1 = 0.
Proof. reflexivity. Qed.

Lemma position_of_level_step : forall l : Level,
  position_of_level (LS l) = S (position_of_level l).
Proof. intro l. reflexivity. Qed.

Lemma pos_number_of_level : forall l : Level,
  pos_number (position_of_level l) = level_depth l.
Proof.
  intro l. unfold pos_number, position_of_level.
  symmetry. apply LevelNatIso.level_depth_eq.
Qed.

(** FOUR PATHS — ONE SERIES. For a list of performed distinctions with its
    binary record: the count of the list is the depth of its level, the
    length of its record and the number of its position. *)
Theorem four_paths_one_series :
  forall (Ds : list Distinction) (bs : BitString),
    presented Ds -> binary_record Ds bs ->
    level_depth (level_of_count Ds) = length Ds
    /\ bit_length bs = length Ds
    /\ pos_number (position_of_level (level_of_count Ds)) = length Ds.
Proof.
  intros Ds bs Hp Hr. split; [exact (depth_of_level_of_count Ds Hp) | split].
  - exact (record_keeps_count Ds bs Hr).
  - rewrite pos_number_of_level. exact (depth_of_level_of_count Ds Hp).
Qed.

(* ========================================================================= *)
(*  4. ONE MORE ACT MOVES ALL FOUR                                           *)
(* ========================================================================= *)

(** One more act of distinction: the count grows by one, the level is built
    over, the record gets one more bit — the side this act places — and the
    position moves to the next. *)
Theorem one_more_act_moves_all_four :
  forall (Ds : list Distinction) (bs : BitString) (D : Distinction) (s : Side),
    presented Ds -> binary_record Ds bs -> side_holds D s ->
    length (add_distinction Ds D) = S (length Ds)
    /\ level_of_count (add_distinction Ds D) = LS (level_of_count Ds)
    /\ binary_record (add_distinction Ds D) (add_bit s bs)
    /\ position_of_level (level_of_count (add_distinction Ds D))
       = S (position_of_level (level_of_count Ds)).
Proof.
  intros Ds bs D s Hp Hr Hs.
  split; [apply add_distinction_increments | split; [ | split]].
  - exact (level_of_count_step Ds D Hp).
  - exact (record_of_one_more_act Ds bs D s Hr Hs).
  - rewrite (level_of_count_step Ds D Hp). apply position_of_level_step.
Qed.
