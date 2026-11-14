(** * BitStringCount.v — The binary path counted: exactly two sides, the
      positive numbers as lengths of non-empty records, 2^K records of
      length K, and the binary record of a list of performed distinctions

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapter II.4, places 4.1-4.3, 2026-11-14):

    Elements: the two sides Marked / Unmarked (Side, Binarity.v); binary
              records — lists of bits (BitString, BitString.v); performed
              acts of distinction (Distinction).
    Roles:    a bit — one binary position, the side placed by one act; the
              length of a record — the count of bits; the number of records
              of a given length — the count of outcomes.
    Rules:    L2 (the sides are distinct), L3 (the sides exhaust the frame);
              adding a bit is S on the length and doubles the number of
              records.
    Proved:   (1) EXACTLY two sides as a count: the list of sides has no
                  repeats, and every enumeration of the sides without
                  repeats has length 2 (completeness and length alone give
                  only "at most two" — a counter-example is included);
              (2) the number-side of the binary count: every n >= 1 is the
                  length of a non-empty record, and the lengths of the
                  non-empty records are exactly the numbers n >= 1; the
                  empty record has no positive count; one is the least
                  positive count;
              (3) K bits give 2^K outcomes: the records of length K are
                  enumerated completely and without repeats by a list of
                  length two_pow K, and every such enumeration has that
                  length; one more bit doubles the number of records;
              (4) induction over non-empty records and induction over the
                  numbers from one are obtained from each other; without the
                  condition "non-empty" the principle is false;
              (5) the bridge to the record Distinction: a list of performed
                  distinctions has exactly one binary record — the list of
                  the sides placed by its acts — and the record has the same
                  count; attaching an act attaches a bit.
    P4 diagnostic ("could it be otherwise?"): finite lists only. Forced:
              (1)-(5). NOT claimed: that the type Side is derived from the
              record Distinction — it is a separate inductive type, tied to
              the record by the relation side_holds (DistinctionSideRole.v);
              a FUNCTION from a distinction to its placed side (the rule
              exhaustive is a disjunction in Prop, so the record is given as
              a relation); anything about entropy or probability.

    STATUS: 30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List Bool Lia Arith PeanoNat FinFun.
Import ListNotations.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.Binarity.
From ToS Require Import foundation.BitString.
From ToS Require Import foundation.PrimalityOfOne.
From ToS Require Import foundation.CountingPresence.
From ToS Require Import foundation.DistinctionSideRole.

(* Binarity.v leaves Q_scope open. *)
Close Scope Q_scope.
Open Scope nat_scope.

(* ========================================================================= *)
(*  1. EXACTLY TWO SIDES — AS A COUNT                                        *)
(* ========================================================================= *)

(** Completeness of a list and its length give only "at most": a type with
    ONE value also has a complete list of length 2. *)
Lemma complete_length_two_is_not_exactly_two :
  exists l : list unit, (forall u : unit, In u l) /\ length l = 2.
Proof.
  exists [tt; tt]. split.
  - intros []. left. reflexivity.
  - reflexivity.
Qed.

(** The list of the sides has no repeats — from L2. *)
Lemma all_sides_nodup : NoDup all_sides.
Proof.
  unfold all_sides. constructor.
  - intros [H | []]. exact (L2_exclusive (eq_sym H)).
  - constructor.
    + intros [].
    + constructor.
Qed.

(** Every enumeration of the sides without repeats has length exactly 2:
    the number 2 is a property of the type Side, not of the chosen list. *)
Theorem side_count_exactly_two :
  forall l : list Side, NoDup l -> (forall s : Side, In s l) -> length l = 2.
Proof.
  intros l Hnd Hall.
  assert (H1 : length l <= length all_sides).
  { apply NoDup_incl_length; [exact Hnd | intros s _; apply all_sides_complete]. }
  assert (H2 : length all_sides <= length l).
  { apply NoDup_incl_length; [exact all_sides_nodup | intros s _; apply Hall]. }
  rewrite all_sides_length in H1, H2. lia.
Qed.

(** Equality of sides is decidable. *)
Lemma Side_eq_dec : forall a b : Side, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* ========================================================================= *)
(*  2. THE NUMBER-SIDE OF THE BINARY COUNT                                   *)
(* ========================================================================= *)

Lemma repeat_marked_length : forall n : nat, bit_length (repeat Marked n) = n.
Proof. intro n. unfold bit_length. apply repeat_length. Qed.

(** For every n >= 1 there is a non-empty record of length n. *)
Theorem positive_nat_is_bit_count :
  forall n : nat, 1 <= n -> exists bs : BitString, bs <> [] /\ bit_length bs = n.
Proof.
  intros n Hn. exists (repeat Marked n). split.
  - destruct n as [| n']; [lia | simpl; discriminate].
  - apply repeat_marked_length.
Qed.

(** The empty record has no positive count. *)
Theorem empty_not_positive_count : ~ positive_bit_count [].
Proof. unfold positive_bit_count, bit_length. simpl. lia. Qed.

Theorem positive_bit_count_iff_nonempty :
  forall bs : BitString, positive_bit_count bs <-> bs <> [].
Proof.
  intro bs. split.
  - intros H E. subst bs. exact (empty_not_positive_count H).
  - apply nonempty_positive_count.
Qed.

(** Both directions: the lengths of the non-empty records are exactly the
    numbers n >= 1. *)
Theorem bit_count_iff_positive :
  forall n : nat,
    (exists bs : BitString, bs <> [] /\ bit_length bs = n) <-> 1 <= n.
Proof.
  intro n. split.
  - intros [bs [Hne Hlen]]. subst n. exact (nonempty_positive_count bs Hne).
  - apply positive_nat_is_bit_count.
Qed.

(** One is the least positive binary count. *)
Theorem one_bit_is_least_positive_count :
  forall bs : BitString, positive_bit_count bs -> bit_length one_bit <= bit_length bs.
Proof. intros bs H. rewrite one_bit_length. exact H. Qed.

(** A bit attached on the right also adds one to the length. *)
Lemma add_bit_right_increments_length :
  forall (b : Bit) (bs : BitString), bit_length (bs ++ [b]) = S (bit_length bs).
Proof. intros b bs. unfold bit_length. rewrite length_app. simpl. lia. Qed.

(* ========================================================================= *)
(*  3. K BITS GIVE 2^K OUTCOMES                                              *)
(* ========================================================================= *)

(** All records of length K. *)
Fixpoint all_bitstrings (K : nat) : list BitString :=
  match K with
  | O => [[]]
  | S K' => map (add_bit Marked) (all_bitstrings K')
            ++ map (add_bit Unmarked) (all_bitstrings K')
  end.

Lemma all_bitstrings_length : forall K : nat, length (all_bitstrings K) = two_pow K.
Proof.
  induction K as [| K IH]; simpl.
  - reflexivity.
  - rewrite length_app, !length_map, IH. lia.
Qed.

Lemma all_bitstrings_sound :
  forall (K : nat) (bs : BitString), In bs (all_bitstrings K) -> bit_length bs = K.
Proof.
  induction K as [| K IH]; simpl; intros bs H.
  - destruct H as [H | []]. subst. reflexivity.
  - apply in_app_or in H. destruct H as [H | H];
      apply in_map_iff in H; destruct H as [bs' [E Hin]]; subst bs;
      rewrite add_bit_increments_length; f_equal; apply IH; exact Hin.
Qed.

Lemma all_bitstrings_complete :
  forall bs : BitString, In bs (all_bitstrings (bit_length bs)).
Proof.
  induction bs as [| b bs IH].
  - left. reflexivity.
  - change (bit_length (b :: bs)) with (S (bit_length bs)). simpl.
    apply in_or_app. destruct (L3_exhaustive b) as [E | E]; subst b.
    + left. apply in_map_iff. exists bs. split; [reflexivity | exact IH].
    + right. apply in_map_iff. exists bs. split; [reflexivity | exact IH].
Qed.

Lemma add_bit_injective :
  forall (b : Bit) (x y : BitString), add_bit b x = add_bit b y -> x = y.
Proof. intros b x y H. unfold add_bit in H. injection H. auto. Qed.

Lemma all_bitstrings_nodup : forall K : nat, NoDup (all_bitstrings K).
Proof.
  induction K as [| K IH]; simpl.
  - constructor; [intros [] | constructor].
  - apply NoDup_app.
    + apply FinFun.Injective_map_NoDup; [intros x y; apply add_bit_injective | exact IH].
    + apply FinFun.Injective_map_NoDup; [intros x y; apply add_bit_injective | exact IH].
    + intros bs H1 H2.
      apply in_map_iff in H1. destruct H1 as [x [Ex _]].
      apply in_map_iff in H2. destruct H2 as [y [Ey _]].
      subst bs. unfold add_bit in Ey. injection Ey as Ehd _.
      exact (L2_exclusive (eq_sym Ehd)).
Qed.

(** The records of length K are enumerated completely and without repeats by
    a list of length 2^K. Both laws work here: L2 (no repeats) and L3
    (completeness). *)
Theorem bitstrings_of_length_count :
  forall K : nat,
    NoDup (all_bitstrings K) /\
    (forall bs : BitString, In bs (all_bitstrings K) <-> bit_length bs = K) /\
    length (all_bitstrings K) = microstates K.
Proof.
  intro K. split; [apply all_bitstrings_nodup | split].
  - intro bs. split.
    + apply all_bitstrings_sound.
    + intro E. subst K. apply all_bitstrings_complete.
  - unfold microstates. apply all_bitstrings_length.
Qed.

(** The number 2^K does not depend on the chosen enumeration. *)
Theorem bitstrings_count_is_forced :
  forall (K : nat) (l : list BitString),
    NoDup l -> (forall bs : BitString, In bs l <-> bit_length bs = K) ->
    length l = two_pow K.
Proof.
  intros K l Hnd Hl.
  destruct (bitstrings_of_length_count K) as [Hnd' [Hall' Hlen']].
  unfold microstates in Hlen'. rewrite <- Hlen'.
  apply Nat.le_antisymm; apply NoDup_incl_length; try assumption.
  - intros bs H. apply Hall'. apply Hl. exact H.
  - intros bs H. apply Hl. apply Hall'. exact H.
Qed.

(** One more bit doubles the number of records. *)
Theorem one_more_bit_doubles_records : forall K : nat,
  length (all_bitstrings (S K)) = 2 * length (all_bitstrings K).
Proof. intro K. rewrite !all_bitstrings_length. apply pow_double. Qed.

(* ========================================================================= *)
(*  4. INDUCTION OVER NON-EMPTY RECORDS AND OVER THE NUMBERS FROM ONE        *)
(* ========================================================================= *)

(** Without the condition "non-empty" the principle "base — one bit, step —
    one more bit" is false for ALL records: the empty record is not covered. *)
Theorem induction_from_one_bit_misses_empty :
  ~ (forall P : BitString -> Prop,
       (forall b : Bit, P [b]) ->
       (forall (b : Bit) (bs : BitString), P bs -> P (b :: bs)) ->
       forall bs : BitString, P bs).
Proof.
  intro H.
  refine (H (fun bs => bs <> []) _ _ [] eq_refl).
  - intros b. discriminate.
  - intros b bs _. discriminate.
Qed.

(** The principle of BitString.v obtained by the ordinary induction over nat
    (on the length of the record). *)
Theorem nonempty_bitstring_ind_via_nat :
  forall (P : BitString -> Prop),
    (forall b : Bit, P [b]) ->
    (forall b bs, bs <> [] -> P bs -> P (b :: bs)) ->
    forall bs, bs <> [] -> P bs.
Proof.
  intros P Hbase Hstep.
  assert (H : forall n bs, bit_length bs = S n -> P bs).
  { induction n as [| n IH]; intros bs Hlen.
    - destruct bs as [| b [| b2 bs']]; simpl in Hlen; try discriminate.
      apply Hbase.
    - destruct bs as [| b bs']; simpl in Hlen; [discriminate | ].
      apply Hstep.
      + destruct bs'; [simpl in Hlen; discriminate | discriminate].
      + apply IH. unfold bit_length. injection Hlen. auto. }
  intros bs Hne. destruct bs as [| b bs']; [contradiction | ].
  apply (H (length bs')). reflexivity.
Qed.

(** Back: induction over the numbers from one obtained from the induction
    over non-empty records. *)
Theorem nat_ind_from_one_via_bitstrings :
  forall (Q : nat -> Prop),
    Q 1 ->
    (forall n : nat, 1 <= n -> Q n -> Q (S n)) ->
    forall n : nat, 1 <= n -> Q n.
Proof.
  intros Q H1 HS n Hn.
  destruct (positive_nat_is_bit_count n Hn) as [bs [Hne Hlen]]. subst n.
  clear Hn. revert bs Hne.
  apply (nonempty_bitstring_ind (fun bs => Q (bit_length bs))).
  - intro b. exact H1.
  - intros b bs Hne IH. change (bit_length (b :: bs)) with (S (bit_length bs)).
    apply HS; [exact (nonempty_positive_count bs Hne) | exact IH].
Qed.

(* ========================================================================= *)
(*  5. THE BINARY RECORD OF A LIST OF PERFORMED DISTINCTIONS                 *)
(* ========================================================================= *)

(** bs is the binary record of the list Ds: its bits are the sides placed by
    the acts of the list, one bit per act, in the same order.
    (side_holds D s — the side s holds in D — is DistinctionSideRole.v.) *)
Definition binary_record (Ds : list Distinction) (bs : BitString) : Prop :=
  Forall2 side_holds Ds bs.

(** The side placed by one act is unique. *)
Lemma placed_side_unique : forall (D : Distinction) (s1 s2 : Side),
  side_holds D s1 -> side_holds D s2 -> s1 = s2.
Proof.
  intros D s1 s2 H1 H2.
  destruct (exactly_one_side_holds D) as [s [_ Hu]].
  rewrite (Hu s1 H1), (Hu s2 H2). reflexivity.
Qed.

(** The record has the same count as the list. *)
Theorem record_keeps_count : forall Ds bs,
  binary_record Ds bs -> bit_length bs = length Ds.
Proof.
  intros Ds bs H. unfold bit_length. induction H as [| D s Ds' bs' _ _ IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** A list of performed distinctions has a binary record ... *)
Lemma record_exists : forall Ds : list Distinction, exists bs, binary_record Ds bs.
Proof.
  induction Ds as [| D Ds [bs IH]].
  - exists []. constructor.
  - destruct (exactly_one_side_holds D) as [s [Hs _]].
    exists (s :: bs). constructor; [exact Hs | exact IH].
Qed.

(** ... and only one. *)
Lemma record_unique : forall Ds bs1 bs2,
  binary_record Ds bs1 -> binary_record Ds bs2 -> bs1 = bs2.
Proof.
  intros Ds bs1 bs2 H1. revert bs2.
  induction H1 as [| D s Ds' bs' Hs _ IH]; intros bs2 H2.
  - inversion H2. reflexivity.
  - inversion H2 as [| D' s' Ds'' bs'' Hs' Hrest]; subst.
    rewrite (placed_side_unique D s s' Hs Hs'). f_equal. apply IH. exact Hrest.
Qed.

(** Every list of performed distinctions has exactly one binary record, and
    the record has the count of the list. *)
Theorem every_list_has_exactly_one_record : forall Ds : list Distinction,
  exists bs : BitString,
    binary_record Ds bs /\ bit_length bs = length Ds /\
    (forall bs', binary_record Ds bs' -> bs' = bs).
Proof.
  intro Ds. destruct (record_exists Ds) as [bs H].
  exists bs. split; [exact H | split].
  - exact (record_keeps_count Ds bs H).
  - intros bs' H'. exact (record_unique Ds bs' bs H' H).
Qed.

(** Attaching one more act attaches one more bit — the side that act places. *)
Theorem record_of_one_more_act : forall Ds bs (D : Distinction) (s : Side),
  binary_record Ds bs -> side_holds D s ->
  binary_record (add_distinction Ds D) (add_bit s bs).
Proof.
  intros Ds bs D s H Hs. unfold add_distinction, add_bit, binary_record.
  constructor; [exact Hs | exact H].
Qed.

(** The record is non-empty exactly when at least one act is presented. *)
Theorem record_nonempty_iff_presented : forall Ds bs,
  binary_record Ds bs -> (bs <> [] <-> presented Ds).
Proof.
  intros Ds bs H. unfold presented. split; intros Hne E; apply Hne; subst.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
Qed.

(** The cardinal count and the binary count of one and the same list
    coincide: a list with the count n from one has a non-empty record of
    length n. *)
Theorem count_from_one_is_bit_count : forall Ds n,
  counts_from_one Ds n ->
  exists bs : BitString, binary_record Ds bs /\ bs <> [] /\ bit_length bs = n.
Proof.
  intros Ds n [Hp Hc]. destruct (record_exists Ds) as [bs H].
  exists bs. split; [exact H | split].
  - exact (proj2 (record_nonempty_iff_presented Ds bs H) Hp).
  - rewrite (record_keeps_count Ds bs H). exact Hc.
Qed.

(** The numbers reached by the cardinal count and by the binary count are
    the same numbers. *)
Theorem cardinal_and_binary_counts_coincide : forall n : nat,
  distinction_count_from_one n <->
  (exists bs : BitString, bs <> [] /\ bit_length bs = n).
Proof.
  intro n. rewrite bit_count_iff_positive. apply count_from_one_iff_positive.
Qed.
