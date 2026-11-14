(** * CountingStages.v — The count of a given list as a PROCESS OF STAGES:
      counting is unique, induction runs along the list, and no stage
      presents the whole series

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapter II.2, sections 2.3, 2.6 and 2.7, 2026-11-13):

    Elements: the performed acts of distinction — the members of a GIVEN
              list Ds : list Distinction.
    Roles:    a stage — the list of the acts performed so far; a count
              present at a stage — the count of a non-empty earlier part of
              that list; the next stage — the same list with one more act.
    Rules:    counting gives 0 on the empty list and adds one at every act;
              the next stage is the present one plus one act; every stage is
              a finite list (P4).
    Proved:   (1) counting is unique: any function that gives 0 on the empty
                  list and adds one at every attached act is the length;
              (2) induction along the list: a base for the count of one act
                  and a step for one more act give the property for the
                  count of every list in which at least one act is
                  presented — the proof goes by induction on the LIST;
              (3) at the stage Ds exactly the counts 1 .. length Ds are
                  present; what is present depends on the count of the
                  stage only;
              (4) the next stage keeps everything present and adds exactly
                  one new count; there is no last stage;
              (5) every positive number is present at some stage, and no
                  stage presents all positive numbers — "every number is
                  realizable" and "not all numbers at once" in one theorem;
              (6) P4 in general form: under stage-boundedness no stage holds
                  all numbers; a bridge to ANY one stage contradicts a
                  completed set; a bridge "each member at its own stage" is
                  compatible with P4.
    P4 diagnostic ("could it be otherwise?"): finite lists only; a stage is
              a list. Forced: (1)-(6). NOT claimed: that the induction
              principle of nat is derived from Distinction — induction along
              a list is the principle that comes with the type of lists, and
              that every positive number HAS a list is proved by recursion
              on the number (CountingPresence.v); that P4 itself is derived
              here — stage-boundedness is a property of the stages defined
              in this file and a premise in the general statements.

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.PrimalityOfOne.
From ToS Require Import foundation.P4CompletedInfinity.
From ToS Require Import foundation.CountingPresence.

Local Open Scope nat_scope.

(* ========================================================================= *)
(*  1. COUNTING IS UNIQUE                                                    *)
(* ========================================================================= *)

(** Any count that gives 0 on the empty list and adds one at every element
    met is the length — over any type. *)
Theorem length_is_the_count : forall (A : Type) (f : list A -> nat),
  f [] = 0 ->
  (forall (a : A) (l : list A), f (a :: l) = S (f l)) ->
  forall l, f l = length l.
Proof.
  intros A f H0 Hs l. induction l as [| a l IH].
  - exact H0.
  - rewrite Hs, IH. reflexivity.
Qed.

(** The same for lists of performed acts and the operation of attaching an
    act: the count of a given list is fixed by the two rules of counting. *)
Theorem counting_of_acts_is_unique : forall f : list Distinction -> nat,
  f [] = 0 ->
  (forall Ds D, f (add_distinction Ds D) = S (f Ds)) ->
  forall Ds, counts Ds (f Ds).
Proof.
  intros f H0 Hs Ds. unfold counts. symmetry.
  apply (length_is_the_count Distinction f H0).
  intros a l. exact (Hs l a).
Qed.

(* ========================================================================= *)
(*  2. INDUCTION ALONG THE LIST                                              *)
(* ========================================================================= *)

(** A base for the count of one act and a step for one more act give the
    property for the count of every list in which at least one act is
    presented. The proof is an induction on the LIST of distinctions: the
    base is used at the list of one act, the step at every further act. *)
Theorem count_induction_along_list : forall P : nat -> Prop,
  P 1 ->
  (forall n, P n -> P (S n)) ->
  forall Ds : list Distinction, presented Ds -> P (length Ds).
Proof.
  intros P H1 Hs Ds. induction Ds as [| D Ds IH].
  - intro H. exfalso. apply H. reflexivity.
  - intros _. destruct Ds as [| D' Ds'].
    + exact H1.
    + apply (Hs (length (D' :: Ds'))). apply IH. intro E. discriminate E.
Qed.

(** The same in the words of the chapter: for every number that is a count
    from one. *)
Theorem count_induction_from_list : forall P : nat -> Prop,
  P 1 ->
  (forall n, P n -> P (S n)) ->
  forall n, distinction_count_from_one n -> P n.
Proof.
  intros P H1 Hs n Hn.
  destruct (proj1 (from_one_iff_some_present_list n) Hn) as [Ds [Hp Hc]].
  unfold counts in Hc. subst n.
  exact (count_induction_along_list P H1 Hs Ds Hp).
Qed.

(** Induction from one over nat, read through counts. That the property
    reaches EVERY positive number rests on the realizability of every
    positive number (positive_nat_is_distinction_count), which is itself
    proved by recursion on the number. *)
Theorem induction_from_one_via_counts : forall P : nat -> Prop,
  P 1 ->
  (forall n, P n -> P (S n)) ->
  forall n, 1 <= n -> P n.
Proof.
  intros P H1 Hs n Hn.
  apply (count_induction_from_list P H1 Hs).
  apply positive_nat_is_distinction_count. exact Hn.
Qed.

(* ========================================================================= *)
(*  3. WHAT IS PRESENT AT A STAGE                                            *)
(* ========================================================================= *)

(** The count n is present at the stage Ds: n is the count of a non-empty
    earlier part of the list. New acts are attached at the head
    (add_distinction), so the earlier parts of a list are its tails. *)
Definition present_at (Ds : list Distinction) (n : nat) : Prop :=
  exists Later Earlier : list Distinction,
    Ds = Later ++ Earlier /\ counts_from_one Earlier n.

(** At the stage Ds exactly the counts 1 .. length Ds are present. *)
Theorem present_at_iff : forall Ds n,
  present_at Ds n <-> 1 <= n /\ n <= length Ds.
Proof.
  intros Ds n. split.
  - intros [L [E [H [Hp Hc]]]]. subst Ds. unfold counts in Hc.
    apply presented_iff_count_ge_one in Hp. rewrite length_app. lia.
  - intros [H1 H2].
    exists (firstn (length Ds - n) Ds), (skipn (length Ds - n) Ds).
    split; [symmetry; apply firstn_skipn | ].
    assert (E : length (skipn (length Ds - n) Ds) = n)
      by (rewrite length_skipn; lia).
    split.
    + apply presented_iff_count_ge_one. rewrite E. exact H1.
    + exact E.
Qed.

(** Every stage is bounded: P4 for the stages of counting. *)
Theorem stage_is_bounded : forall Ds n, present_at Ds n -> n <= length Ds.
Proof. intros Ds n H. apply present_at_iff in H. lia. Qed.

(** At the empty stage nothing is present. *)
Theorem empty_stage_presents_nothing : forall n, ~ present_at [] n.
Proof. intros n H. apply present_at_iff in H. simpl in H. lia. Qed.

(** A stage in which at least one act is presented presents its own count. *)
Theorem stage_presents_its_own_count : forall Ds,
  presented Ds -> present_at Ds (length Ds).
Proof.
  intros Ds H. apply present_at_iff.
  apply presented_iff_count_ge_one in H. lia.
Qed.

(** What is present at a stage depends on the count of the stage only, not
    on what the acts are. *)
Theorem present_at_depends_only_on_count : forall Ds1 Ds2 n,
  length Ds1 = length Ds2 -> (present_at Ds1 n <-> present_at Ds2 n).
Proof.
  intros Ds1 Ds2 n E. rewrite !present_at_iff, E. reflexivity.
Qed.

(* ========================================================================= *)
(*  4. THE NEXT STAGE; NO LAST STAGE                                         *)
(* ========================================================================= *)

(** The next stage keeps everything present and adds exactly one new count. *)
Theorem next_stage_adds_exactly_one : forall Ds D n,
  present_at (add_distinction Ds D) n <->
  present_at Ds n \/ n = S (length Ds).
Proof.
  intros Ds D n. rewrite !present_at_iff, add_distinction_increments. lia.
Qed.

Theorem next_stage_keeps_present : forall Ds D n,
  present_at Ds n -> present_at (add_distinction Ds D) n.
Proof. intros Ds D n H. apply next_stage_adds_exactly_one. left. exact H. Qed.

(** There is no last stage: the count that follows the count of a stage is
    absent at it and present at the next one — whatever act is attached. *)
Theorem no_last_stage : forall Ds D,
  ~ present_at Ds (S (length Ds)) /\
  present_at (add_distinction Ds D) (S (length Ds)).
Proof.
  intros Ds D. split.
  - intro H. apply present_at_iff in H. lia.
  - apply next_stage_adds_exactly_one. right. reflexivity.
Qed.

(* ========================================================================= *)
(*  5. EVERY NUMBER — BUT NOT ALL NUMBERS AT ONCE                            *)
(* ========================================================================= *)

(** Every positive number is present at some stage. *)
Theorem every_positive_present_at_some_stage : forall n,
  1 <= n -> exists Ds, present_at Ds n.
Proof.
  intros n Hn.
  destruct (proj1 (from_one_iff_some_present_list n)
              (positive_nat_is_distinction_count n Hn)) as [Ds [Hp Hc]].
  exists Ds. unfold counts in Hc. subst n.
  exact (stage_presents_its_own_count Ds Hp).
Qed.

(** No stage presents all positive numbers. *)
Theorem no_stage_presents_all : forall Ds,
  exists n, 1 <= n /\ ~ present_at Ds n.
Proof.
  intro Ds. exists (S (length Ds)). split; [lia | ].
  intro H. apply present_at_iff in H. lia.
Qed.

(** The two sides of the potential reading in one statement. *)
Theorem every_number_but_not_all_at_once :
  (forall n, 1 <= n -> exists Ds, present_at Ds n) /\
  (forall Ds, ~ (forall n, 1 <= n -> present_at Ds n)).
Proof.
  split; [exact every_positive_present_at_some_stage | ].
  intros Ds H. destruct (no_stage_presents_all Ds) as [n [Hn Hno]].
  exact (Hno (H n Hn)).
Qed.

(* ========================================================================= *)
(*  6. P4 IN GENERAL FORM                                                    *)
(* ========================================================================= *)

(** Under stage-boundedness no stage holds all numbers. *)
Theorem P4_no_stage_holds_all : forall actual : nat -> nat -> Prop,
  P4_stage_bounded actual -> forall stage, ~ (forall n, actual stage n).
Proof.
  intros actual HP4 stage Hall.
  destruct (HP4 stage) as [bound Hbound].
  pose proof (Hbound (S bound) (Hall _)) as H. lia.
Qed.

(** The bridge of P4CompletedInfinity.v leads to stage 0. The contradiction
    is the same for a bridge to ANY one stage. *)
Theorem completed_inf_contradicts_P4_at_any_stage :
  forall (M : nat -> Prop) (actual : nat -> nat -> Prop) (s : nat),
    CompletedInfSet M ->
    P4_stage_bounded actual ->
    (forall n, M n -> actual s n) ->
    False.
Proof.
  intros M actual s HM HP4 Hb.
  apply (P4_no_stage_holds_all actual HP4 s).
  intro n. apply Hb. apply HM.
Qed.

(** A bridge "each member is actual at ITS OWN stage" is compatible with P4. *)
Theorem pointwise_bridge_is_compatible :
  exists (M : nat -> Prop) (actual : nat -> nat -> Prop),
    CompletedInfSet M /\ P4_stage_bounded actual /\
    (forall n, M n -> exists stage, actual stage n).
Proof.
  exists (fun _ => True), (fun stage n => n <= stage).
  split; [intro n; exact I | split].
  - intro stage. exists stage. intros n H. exact H.
  - intros n _. exists n. apply Nat.le_refl.
Qed.

(* ========================================================================= *)
(*  7. THE CARDINAL PATH AS A PROCESS OF STAGES                              *)
(* ========================================================================= *)

(** Stages numbered by their counts: at the stage k the counts from one up
    to k are actual. *)
Definition count_actual (stage n : nat) : Prop :=
  distinction_count_from_one n /\ n <= stage.

(** The numbered stage is the stage of any list with that count. *)
Theorem count_actual_iff_present_at : forall Ds n,
  count_actual (length Ds) n <-> present_at Ds n.
Proof.
  intros Ds n. unfold count_actual.
  rewrite present_at_iff, count_from_one_iff_positive. reflexivity.
Qed.

(** The cardinal path is a process in the sense of P4: every stage is
    bounded, the stages are nested, every positive number is actual at some
    stage, and no stage holds all positive numbers. *)
Theorem cardinal_path_is_P4_process :
  P4_stage_bounded count_actual /\
  (forall stage n, count_actual stage n -> count_actual (S stage) n) /\
  (forall n, 1 <= n -> exists stage, count_actual stage n) /\
  (forall stage, exists n, 1 <= n /\ ~ count_actual stage n).
Proof.
  split; [ | split; [ | split]].
  - intro stage. exists stage. intros n [_ H]. exact H.
  - intros stage n [H1 H2]. split; [exact H1 | lia].
  - intros n Hn. exists n. split; [ | apply Nat.le_refl].
    apply count_from_one_iff_positive. exact Hn.
  - intro stage. exists (S stage). split; [lia | ]. intros [_ H]. lia.
Qed.

(** The series of counts is not a completed set under P4: a bridge that
    would make every count actual at one stage is impossible. *)
Theorem counts_not_completed_at_any_stage : forall s : nat,
  ~ (forall n, 1 <= n -> count_actual s n).
Proof.
  intros s H. destruct (H (S s)) as [_ Hle]; lia.
Qed.
