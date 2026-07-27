(** * ComparisonLevels.v — Data-Level Hierarchy in Comparison (ToS System)

    Formalizes the adjudicated Domain-4 derivation (working journal
    AR4-V1..V9, 2026-07-27): the D1 ladder data -> information -> qualities
    -> characteristics acting inside comparison.  Comparison is defined
    only on a common floor (category mistake = applying the measure to a
    floor one side lacks); the ladder is irreversible (a characteristic
    requires its quality, a quality its information, information its
    data); the measure must not change mid-course — a switched measure
    invalidates the collected list of relations.

    Elements: data levels (four floors); side profiles (which floors a
              side actually has); collected relations tagged by the
              measure that produced them.
    Roles:    the measure (taken frame) applied at a floor; sides of the
              relation; the comparison list (composed per the frame's
              assignment, AR4-V8).
    Rules:    comparable_at l = both sides have floor l; well-formed
              profiles descend the ladder; uniformity of the measure tag
              across the whole list = validity; a mid-course switch of
              measure makes the list invalid (moving the goalposts).
    Status:   all proved; self-contained (no ToS imports).
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(* ================================================================ *)
(** ** 1. The ladder of data levels                                 *)
(* ================================================================ *)

(** Four floors of the D1 hierarchy. *)
Inductive DataLevel : Type :=
  | LData            (** something IS                       *)
  | LInfo            (** WHAT it is                         *)
  | LQuality         (** which categories apply (color...)  *)
  | LCharacteristic. (** concrete values in them (red...)   *)

Definition rank (l : DataLevel) : nat :=
  match l with
  | LData => 0 | LInfo => 1 | LQuality => 2 | LCharacteristic => 3
  end.

(** A side's profile: which floors it actually has. *)
Definition Profile : Type := DataLevel -> bool.

(** The ladder is irreversible: having a floor requires all lower ones. *)
Definition wellformed (a : Profile) : Prop :=
  forall l l' : DataLevel,
    rank l' <= rank l -> a l = true -> a l' = true.

Theorem char_needs_quality :
  forall a : Profile, wellformed a ->
    a LCharacteristic = true -> a LQuality = true.
Proof.
  intros a W H. apply (W LCharacteristic LQuality); [simpl; lia | exact H].
Qed.

Theorem quality_needs_info :
  forall a : Profile, wellformed a ->
    a LQuality = true -> a LInfo = true.
Proof.
  intros a W H. apply (W LQuality LInfo); [simpl; lia | exact H].
Qed.

Theorem info_needs_data :
  forall a : Profile, wellformed a ->
    a LInfo = true -> a LData = true.
Proof.
  intros a W H. apply (W LInfo LData); [simpl; lia | exact H].
Qed.

(* ================================================================ *)
(** ** 2. Comparability on a common floor                           *)
(* ================================================================ *)

(** The measure is applied at floor l: both sides must have the floor. *)
Definition comparable_at (l : DataLevel) (a b : Profile) : bool :=
  andb (a l) (b l).

(** The category mistake, exactly: the measure meets a floor one of the
    sides does not have. *)
Theorem category_mistake_iff :
  forall (l : DataLevel) (a b : Profile),
    comparable_at l a b = false <-> a l = false \/ b l = false.
Proof.
  intros l a b. unfold comparable_at.
  destruct (a l), (b l); simpl; split; intro H;
    try discriminate; intuition discriminate.
Qed.

(** Comparability does not depend on the order of sides. *)
Theorem comparable_symmetric :
  forall (l : DataLevel) (a b : Profile),
    comparable_at l a b = comparable_at l b a.
Proof.
  intros l a b. unfold comparable_at. apply andb_comm.
Qed.

(** Checking descends the ladder: sides comparable at a floor are
    comparable at every floor below it (for well-formed sides) —
    the top-down order of the operation is sound. *)
Theorem comparable_downward :
  forall (a b : Profile),
    wellformed a -> wellformed b ->
    forall l l' : DataLevel,
      rank l' <= rank l ->
      comparable_at l a b = true -> comparable_at l' a b = true.
Proof.
  intros a b Wa Wb l l' Hr H.
  unfold comparable_at in *. apply andb_prop in H as [Ha Hb].
  apply andb_true_intro. split.
  - exact (Wa l l' Hr Ha).
  - exact (Wb l l' Hr Hb).
Qed.

(* ================================================================ *)
(** ** 3. One measure over the whole course                         *)
(* ================================================================ *)

(** A collected relation is tagged by the measure that produced it. *)
Definition Rel : Type := (nat * nat)%type.

(** Uniformity: every record in the list carries the same measure tag. *)
Definition uniform (m : nat) (l : list Rel) : bool :=
  forallb (fun r => Nat.eqb (fst r) m) l.

(** Validity of a collected list: all records share the tag of the first. *)
Definition valid (l : list Rel) : bool :=
  match l with
  | [] => true
  | r :: _ => uniform (fst r) l
  end.

Lemma uniform_map :
  forall (m : nat) (rs : list nat),
    uniform m (map (fun r => (m, r)) rs) = true.
Proof.
  intros m rs. induction rs as [| r rs IH]; simpl; [reflexivity |].
  rewrite Nat.eqb_refl. simpl. exact IH.
Qed.

(** One measure over the whole course — the list is valid. *)
Theorem uniform_valid :
  forall (m : nat) (rs : list nat),
    valid (map (fun r => (m, r)) rs) = true.
Proof.
  intros m rs. destruct rs as [| r rs]; simpl; [reflexivity |].
  rewrite Nat.eqb_refl. simpl. apply uniform_map.
Qed.

(** A measure switched mid-course invalidates the collected list:
    moving the goalposts nullifies the course, whatever else it holds. *)
Theorem switch_invalidates :
  forall (m1 m2 r1 r2 : nat) (l : list Rel),
    m1 <> m2 ->
    valid ((m1, r1) :: (m2, r2) :: l) = false.
Proof.
  intros m1 m2 r1 r2 l Hne. simpl.
  rewrite Nat.eqb_refl. simpl.
  destruct (Nat.eqb m2 m1) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hne. auto.
  - reflexivity.
Qed.

(* ================================================================ *)
(** ** 4. Capstone                                                  *)
(* ================================================================ *)

(** The canon of AR4: comparison lives on a common floor of an
    irreversible ladder, under one unchanged measure. *)
Theorem comparison_canon :
  (forall a : Profile, wellformed a ->
     a LCharacteristic = true -> a LData = true)
  /\ (forall (l : DataLevel) (a b : Profile),
        comparable_at l a b = false <-> a l = false \/ b l = false)
  /\ (forall (m1 m2 r1 r2 : nat) (l : list Rel),
        m1 <> m2 -> valid ((m1, r1) :: (m2, r2) :: l) = false).
Proof.
  split; [| split].
  - intros a W H. apply info_needs_data; auto.
    apply quality_needs_info; auto.
    apply char_needs_quality; auto.
  - exact category_mistake_iff.
  - exact switch_invalidates.
Qed.

Print Assumptions comparison_canon.
