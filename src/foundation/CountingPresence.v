(** * CountingPresence.v — Counting as fixing presence: the count of a GIVEN
      list of performed distinctions

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapters II.1 and II.2, 2026-11-13):

    Elements: the performed acts of distinction — the members of a GIVEN
              list Ds : list Distinction.
    Roles:    the count of the list (its number); one — the count of a
              single performed act; zero — the mark of the list in which
              nothing is presented (a boundary, not a count of what is
              present).
    Rules:    one_is_first, zero_from_absence, succ_from_distinction — the
              three rules named in the header of PrimalityOfOne.v, here as
              theorems about given lists.
    Proved:   (1) a given list has exactly one count;
              (2) ONE AS THE LOWER BOUND IS A CONSEQUENCE OF PRESENCE: if at
                  least one act is presented, the count is >= 1; zero is the
                  count of the empty list and of it only — so zero is not a
                  count of what is present BY A THEOREM, not by a clause
                  written into a definition;
              (3) the next distinction — ANY distinction — gives the next
                  number, and a list has the count S n exactly when it is a
                  list of the count n with one more act;
              (4) what the two number-predicates of the chapters say:
                  distinction_count n holds for EVERY n;
                  distinction_count_from_one n <-> 1 <= n <-> "some list with
                  at least one act has the count n" — all without axioms;
              (5) ToS_nat — a count grounded in distinctions: a list with at
                  least one performed act; its counts are exactly the
                  positive numbers;
              (6) attaching at the end of the list (the chronological
                  reading) gives the same count as attaching at the head;
              (7) the pair (1, 0) of the order of grounding is the pair of
                  two counts: of one performed act and of the empty list.
    P4 diagnostic ("could it be otherwise?"): finite lists only; nothing
              infinite. Forced: (1)-(7). NOT claimed: that the number is
              BUILT from distinctions — it stays a value of nat (the length
              of the list); that the count depends on WHAT the distinctions
              are — the length of a list is the same over any inhabited type
              (count_predicates_ignore_what_is_counted says so explicitly);
              that the order "one grounds zero" is a theorem — the pair
              distinction_order stays a hand-written record.

    STATUS: 30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.DistinctionCoDefinition.
From ToS Require Import foundation.IndivisibleDistinction.
From ToS Require Import foundation.PrimalityOfOne.

Local Open Scope nat_scope.

(* ========================================================================= *)
(*  1. THE COUNT OF A GIVEN LIST                                             *)
(* ========================================================================= *)

(** The count of a given list of performed distinctions. *)
Definition counts (Ds : list Distinction) (n : nat) : Prop := length Ds = n.

(** At least one act of distinction is presented in the list. *)
Definition presented (Ds : list Distinction) : Prop := Ds <> [].

(** The count of what is present: a list with at least one performed act,
    and its number. *)
Definition counts_from_one (Ds : list Distinction) (n : nat) : Prop :=
  presented Ds /\ counts Ds n.

(** A given list has exactly one count. *)
Theorem counts_functional : forall Ds n m, counts Ds n -> counts Ds m -> n = m.
Proof. unfold counts. intros Ds n m H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

Theorem every_list_has_exactly_one_count : forall Ds : list Distinction,
  counts Ds (length Ds) /\ (forall n, counts Ds n -> n = length Ds).
Proof.
  intro Ds. split.
  - reflexivity.
  - intros n H. symmetry. exact H.
Qed.

(** This is the count already used in the repository for lengths and
    concatenations: distinction_count_nat (IndivisibleDistinction.v). *)
Theorem counts_is_count_nat : forall Ds n,
  counts Ds n <-> distinction_count_nat Ds = n.
Proof. intros Ds n. unfold counts, distinction_count_nat. tauto. Qed.

(* ========================================================================= *)
(*  2. ONE AS THE LOWER BOUND — A CONSEQUENCE OF PRESENCE                    *)
(* ========================================================================= *)

(** At least one act is presented exactly when the count is not less than
    one. *)
Theorem presented_iff_count_ge_one : forall Ds : list Distinction,
  presented Ds <-> 1 <= length Ds.
Proof.
  intro Ds. unfold presented. destruct Ds as [| D Ds']; simpl.
  - split; [intro H; exfalso; apply H; reflexivity | intro H; lia].
  - split; [intros _; lia | intros _ H; discriminate H].
Qed.

(** One as the lower bound follows from presence; it is not written in. *)
Theorem presence_starts_at_one : forall Ds n, counts_from_one Ds n -> 1 <= n.
Proof.
  intros Ds n [Hp Hc]. unfold counts in Hc. subst n.
  apply (proj1 (presented_iff_count_ge_one Ds)). exact Hp.
Qed.

(** zero_from_absence: zero is the count of the list in which nothing is
    presented, and of that list only. *)
Theorem zero_from_absence : forall Ds : list Distinction,
  counts Ds 0 <-> Ds = [].
Proof.
  intro Ds. unfold counts. split.
  - destruct Ds; [reflexivity | discriminate].
  - intro H. subst. reflexivity.
Qed.

(** Zero is not a count of what is present — a consequence of the two
    theorems above, with no condition on the number. *)
Theorem zero_counts_nothing_present : forall Ds, ~ counts_from_one Ds 0.
Proof.
  intros Ds [Hp Hc]. apply Hp. exact (proj1 (zero_from_absence Ds) Hc).
Qed.

(** one_is_first: one performed act — whatever the distinction is — is
    counted by one, and by one only. *)
Theorem one_is_first : forall D : Distinction,
  counts_from_one [D] 1 /\ (forall n, counts_from_one [D] n -> n = 1).
Proof.
  intro D. split.
  - split; [discriminate | reflexivity].
  - intros n [_ H]. unfold counts in H. simpl in H. lia.
Qed.

(** succ_from_distinction: the next distinction gives the next number. The
    distinction is arbitrary, and the list it is attached to may be any —
    attached to the empty list, the act gives the count one. *)
Theorem succ_from_distinction : forall Ds (D : Distinction) n,
  counts Ds n -> counts_from_one (add_distinction Ds D) (S n).
Proof.
  intros Ds D n H. unfold counts in H. split.
  - unfold presented, add_distinction. discriminate.
  - unfold counts. rewrite add_distinction_increments, H. reflexivity.
Qed.

(** A list has the count S n exactly when it is a list of the count n with
    one more act attached. *)
Theorem succ_count_iff_one_more_act : forall (n : nat) (Ds : list Distinction),
  counts Ds (S n) <->
  exists (D : Distinction) (Ds' : list Distinction),
    Ds = add_distinction Ds' D /\ counts Ds' n.
Proof.
  intros n Ds. unfold counts. split.
  - destruct Ds as [| D Ds']; simpl; intro H.
    + discriminate.
    + exists D, Ds'. split; [reflexivity | lia].
  - intros [D [Ds' [HD Hl]]]. subst Ds. rewrite add_distinction_increments.
    rewrite Hl. reflexivity.
Qed.

(** Every count of what is present begins with a single act counted by one
    (the list grows at the head, so the first performed act stands last). *)
Theorem every_count_starts_with_one : forall Ds : list Distinction,
  presented Ds ->
  exists (D : Distinction) (Ds' : list Distinction),
    Ds = Ds' ++ [D] /\ counts_from_one [D] 1.
Proof.
  intros Ds Hne. destruct (exists_last Hne) as [Ds' [D E]].
  exists D, Ds'. split; [exact E | exact (proj1 (one_is_first D))].
Qed.

(* ========================================================================= *)
(*  3. WHAT THE TWO NUMBER-PREDICATES SAY                                    *)
(* ========================================================================= *)

(** distinction_count (Distinction.v) holds for every number; no axiom is
    needed: the witness is a list of copies of the distinction True | False. *)
Theorem distinction_count_of_every_number : forall n, distinction_count n.
Proof.
  intro n. exists (repeat distinction_true_false n). apply repeat_length.
Qed.

(** distinction_count_from_one (PrimalityOfOne.v) is the condition 1 <= n. *)
Theorem count_from_one_iff_positive : forall n,
  distinction_count_from_one n <-> 1 <= n.
Proof.
  intro n. split.
  - intros [Ds [_ H]]. exact H.
  - intro H. exists (repeat distinction_true_false n).
    split; [apply repeat_length | exact H].
Qed.

(** ... and the same condition, moved from the number to the list: "some
    list with at least one presented act has this count". *)
Theorem from_one_iff_some_present_list : forall n,
  distinction_count_from_one n <-> exists Ds, counts_from_one Ds n.
Proof.
  intro n. split.
  - intros [Ds [Hlen Hge]]. exists Ds. split; [ | exact Hlen].
    apply (proj2 (presented_iff_count_ge_one Ds)). rewrite Hlen. exact Hge.
  - intros [Ds H]. exists Ds.
    split; [exact (proj2 H) | exact (presence_starts_at_one Ds n H)].
Qed.

(** Zero is not a count of anything presented — as a consequence. *)
Theorem zero_is_not_a_presented_count : ~ exists Ds, counts_from_one Ds 0.
Proof. intros [Ds H]. exact (zero_counts_nothing_present Ds H). Qed.

(** Every positive number is the count of some presented list — realizability
    without an axiom. *)
Theorem positive_number_is_presented_count : forall n,
  1 <= n -> exists Ds, counts_from_one Ds n.
Proof.
  intros n H. apply (proj1 (from_one_iff_some_present_list n)).
  apply (proj2 (count_from_one_iff_positive n)). exact H.
Qed.

(** The two predicates differ at zero only. *)
Theorem counts_differ_only_at_zero : forall n,
  n <> 0 -> (distinction_count n <-> distinction_count_from_one n).
Proof.
  intros n Hn. split.
  - intros _. apply (proj2 (count_from_one_iff_positive n)). lia.
  - intros _. apply distinction_count_of_every_number.
Qed.

(** Neither predicate depends on what is counted: the same holds for lists
    over any inhabited type. That the counted items are acts of distinction
    is expressed by the type of the list only. *)
Theorem count_predicates_ignore_what_is_counted :
  forall (A : Type) (a : A) (n : nat),
    (exists l : list A, length l = n) /\
    ((exists l : list A, length l = n /\ 1 <= n) <-> 1 <= n).
Proof.
  intros A a n. split.
  - exists (repeat a n). apply repeat_length.
  - split.
    + intros [_ [_ H]]. exact H.
    + intro H. exists (repeat a n). split; [apply repeat_length | exact H].
Qed.

(* ========================================================================= *)
(*  4. ToS_nat: A COUNT GROUNDED IN DISTINCTIONS                             *)
(* ========================================================================= *)

(** A count grounded in distinctions: a list in which at least one act is
    presented. This is not a new type of numbers — nat is not redefined; it
    is the carrier that counting counts, and tos_count reads its number. *)
Definition ToS_nat : Type := { Ds : list Distinction | presented Ds }.

Definition tos_count (c : ToS_nat) : nat := length (proj1_sig c).

Theorem tos_count_from_one : forall c : ToS_nat,
  counts_from_one (proj1_sig c) (tos_count c).
Proof. intros [Ds Hp]. split; [exact Hp | reflexivity]. Qed.

(** The count of a ToS_nat is never zero. *)
Theorem tos_count_positive : forall c : ToS_nat, 1 <= tos_count c.
Proof.
  intro c. exact (presence_starts_at_one _ _ (tos_count_from_one c)).
Qed.

Lemma presented_single : forall D : Distinction, presented [D].
Proof. intros D H. discriminate H. Qed.

Lemma presented_cons : forall (D : Distinction) Ds, presented (D :: Ds).
Proof. intros D Ds H. discriminate H. Qed.

(** One performed act, and one more act. *)
Definition tos_one (D : Distinction) : ToS_nat := exist _ [D] (presented_single D).

Definition tos_succ (D : Distinction) (c : ToS_nat) : ToS_nat :=
  exist _ (D :: proj1_sig c) (presented_cons D (proj1_sig c)).

Theorem tos_count_one : forall D, tos_count (tos_one D) = 1.
Proof. reflexivity. Qed.

Theorem tos_count_succ : forall D c, tos_count (tos_succ D c) = S (tos_count c).
Proof. reflexivity. Qed.

(** The counts of ToS_nat are exactly the positive numbers. *)
Theorem tos_count_range : forall n, (exists c : ToS_nat, tos_count c = n) <-> 1 <= n.
Proof.
  intro n. split.
  - intros [c Hc]. subst n. apply tos_count_positive.
  - intro H. destruct (positive_number_is_presented_count n H) as [Ds [Hp Hc]].
    exists (exist _ Ds Hp). exact Hc.
Qed.

(** The predicate of the cardinal path is the range of tos_count. *)
Theorem from_one_is_range_of_tos_count : forall n,
  distinction_count_from_one n <-> exists c : ToS_nat, tos_count c = n.
Proof.
  intro n. rewrite count_from_one_iff_positive. symmetry. apply tos_count_range.
Qed.

(* ========================================================================= *)
(*  5. ATTACHING AT THE END OF THE LIST (THE CHRONOLOGICAL READING)          *)
(* ========================================================================= *)

(** add_distinction attaches at the head: the head of the list is the LAST
    performed act. Attaching at the end keeps the acts in the order of their
    performance. *)
Definition snoc_distinction (Ds : list Distinction) (D : Distinction) :
  list Distinction := Ds ++ [D].

Theorem snoc_distinction_increments : forall Ds D,
  length (snoc_distinction Ds D) = S (length Ds).
Proof. intros Ds D. unfold snoc_distinction. apply last_length. Qed.

(** The count does not depend on where the new act is attached. *)
Theorem add_and_snoc_same_count : forall Ds D n,
  counts (add_distinction Ds D) n <-> counts (snoc_distinction Ds D) n.
Proof.
  intros Ds D n. unfold counts.
  rewrite add_distinction_increments, snoc_distinction_increments. tauto.
Qed.

(** The chronological reading is the stack read in reverse. *)
Theorem snoc_is_reversed_add : forall Ds D,
  rev (add_distinction Ds D) = snoc_distinction (rev Ds) D.
Proof. intros Ds D. reflexivity. Qed.

(* ========================================================================= *)
(*  6. THE PAIR OF THE ORDER OF GROUNDING AS A PAIR OF TWO COUNTS            *)
(* ========================================================================= *)

(** The pair (1, 0) of the order of grounding (PrimalityOfOne.v) read by
    counts: its first component is the count of one performed act —
    whatever the distinction is — and its second component is the count of
    the list in which nothing is presented. The pair itself stays a
    hand-written record; this theorem says what its components count. *)
Theorem conceptual_ordering_from_counts : forall D : Distinction,
  tos_conceptual_ordering = (length [D], length (@nil Distinction)).
Proof. reflexivity. Qed.
