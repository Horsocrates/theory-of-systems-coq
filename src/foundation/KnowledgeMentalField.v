(** * KnowledgeMentalField.v — the mental field: two fields, channels, the will as potential
      (formalization of MP-4/MP-5/MP-11/MP-12, the mental-field working record,
       Knigi/Volya/01; sibling of KnowledgeQuestion.v / KnowledgeGap.v)

    Elements: modal layers of the objective field; ladder rungs (data/information/record);
              channels of the witness; the will-potential counter.
    Roles:    data = the objective-field rung (source-borne, witness-free);
              information and record = subjective-field rungs (witness-borne);
              channel = the path of data at the seam; will = the potential between
              the known and the knowable, selecting the next patch.
    Rules:    perception = the transition objective -> subjective, possible ONLY through
              a channel (no channel - no transition); designation (info -> record) is an
              inner act and needs no channel; the ladder has no skips and ends at the
              record; every record opens no less new knowable than it closes (the gap
              canon) - hence the will-potential never falls below its start and never
              exhausts: the pull of cognition is structurally eternal.
    Status:   "cannot be" is outside the field (no witnessing of the impossible);
              the three-layer field (necessary / actual / potential) exhausts what
              is witnessable; the necessary has no generating step and no time -
              given BEFORE the first act, which is what produces time (MP-14/15);
              the modal square closes: non-being swaps its corners.
    STATUS: 27 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules (generative first): the will-potential (difference of the two fields)
      creates the pull and selects the patch; attention is its vector; perception
      crosses the seam by a channel; designation records within the subjective
      field.  Generative order: will -> attention -> perception -> act of
      distinction (MP-9), here compressed to the ladder discipline.
    Roles (L4): data / information / record are ROLES of content relative to the
      act, not substances (MP-4): the same content is data for every
      not-yet-perceiving witness.
    Elements (L1+P4): finitely many rungs and layers; the potential is a nat
      counter - no completed totality anywhere; inexhaustibility is a statement
      about EVERY step, not about an actual infinite.
    P4 diagnostic (could it be otherwise?): a channel-free transition would make
      the subjective field grow without meetings - perception without encounter,
      against the meeting-necessity canon; a skipping ladder would mint records
      out of unperceived data - information without a witness; an exhaustible
      potential would need a record that closes more than it opens - against the
      gap theorem's premise. *)

From Stdlib Require Import Arith Lia.

(* ---------- modal layers of the objective field (MP-5/MP-14) ----------
   Replicated in spirit from KnowledgeQuestion.v to keep this file self-contained. *)

Inductive Modality := MNecessary | MActual | MPotential | MImpossible.
(* "cannot not be" | "can be - and is" | "can be, but is not" | "cannot be" *)

Definition in_field (m : Modality) : bool :=
  match m with MImpossible => false | _ => true end.

Definition witnessable (m : Modality) : bool := in_field m.

Theorem impossible_not_witnessable : witnessable MImpossible = false.
Proof. reflexivity. Qed.

(* what is witnessed is always inside the field: to perceive is to distinguish,
   the distinguished is data, data is logical structure - field-borne (MP-12) *)
Theorem witnessable_three_layers :
  forall m, witnessable m = true ->
    m = MNecessary \/ m = MActual \/ m = MPotential.
Proof.
  intro m; destruct m; intro H;
  [ left; reflexivity | right; left; reflexivity
  | right; right; reflexivity | discriminate H ].
Qed.

(* ---------- the necessary: no generating step, no time (MP-14/MP-15) ---------- *)

(* only the actualized has a history of actualization; the necessary is given
   together with its parent system as required by the sufficient ground of
   existence itself; the potential is not yet actualized *)
Definition has_generating_step (m : Modality) : bool :=
  match m with MActual => true | _ => false end.

Theorem necessary_in_field : in_field MNecessary = true.
Proof. reflexivity. Qed.

Theorem necessary_no_generating_step : has_generating_step MNecessary = false.
Proof. reflexivity. Qed.

(* the discriminator of the upper layers: exactly the actualized is generated *)
Theorem generated_iff_actual :
  forall m, has_generating_step m = true <-> m = MActual.
Proof. intro m; destruct m; split; intro H; try reflexivity; discriminate H. Qed.

(* what is present in being: the necessary and the actualized *)
Definition is_present (m : Modality) : bool :=
  match m with MNecessary | MActual => true | _ => false end.

Theorem present_dichotomy :
  forall m, is_present m = true -> m = MNecessary \/ m = MActual.
Proof.
  intro m; destruct m; intro H;
  [ left; reflexivity | right; reflexivity | discriminate H | discriminate H ].
Qed.

(* the modal square: the negation of being swaps its corners *)
Definition non_being (m : Modality) : Modality :=
  match m with
  | MNecessary  => MImpossible   (* cannot not be  <->  cannot be *)
  | MImpossible => MNecessary
  | MActual     => MPotential    (* is  <->  is not: the contingent middles *)
  | MPotential  => MActual
  end.

Theorem non_being_involutive : forall m, non_being (non_being m) = m.
Proof. intro m; destruct m; reflexivity. Qed.

Theorem square_extremes : non_being MNecessary = MImpossible.
Proof. reflexivity. Qed.

(* time is produced by the first act of distinction; the necessary is given
   BEFORE that act - time is categorially inapplicable to it (MP-15).
   Extensionally: time applies exactly to the generated. *)
Definition in_time (m : Modality) : bool :=
  match m with MActual => true | _ => false end.

Theorem necessary_timeless : in_time MNecessary = false.
Proof. reflexivity. Qed.

Theorem timed_iff_generated : forall m, in_time m = has_generating_step m.
Proof. intro m; destruct m; reflexivity. Qed.

(* ---------- the ladder: data -> information -> record (MP-4) ---------- *)

Inductive Rung := RData | RInfo | RRecord.

Inductive Location := LObjective | LSubjective.

Definition rung_field (r : Rung) : Location :=
  match r with RData => LObjective | _ => LSubjective end.

Theorem data_is_objective : rung_field RData = LObjective.
Proof. reflexivity. Qed.

Theorem info_is_subjective : rung_field RInfo = LSubjective.
Proof. reflexivity. Qed.

Theorem record_is_subjective : rung_field RRecord = LSubjective.
Proof. reflexivity. Qed.

(* ---------- channels: the path of data at the seam (MP-11/MP-12) ---------- *)

Record Witness := mkW { channels : nat }.

Definition has_channel (w : Witness) : bool :=
  match channels w with O => false | _ => true end.

(* one ladder step; perception (the seam) requires a channel,
   designation (info -> record) is an inner act and does not *)
Definition ladder_step (w : Witness) (r : Rung) : option Rung :=
  match r with
  | RData   => if has_channel w then Some RInfo else None
  | RInfo   => Some RRecord
  | RRecord => None
  end.

Theorem no_channel_no_transition :
  forall w, channels w = O -> ladder_step w RData = None.
Proof. intros [c] H; simpl in *; rewrite H; reflexivity. Qed.

Theorem channel_enables_transition :
  forall w, channels w <> O -> ladder_step w RData = Some RInfo.
Proof. intros [c] H; simpl in *; destruct c; [contradiction | reflexivity]. Qed.

Theorem designation_needs_no_channel :
  forall w, ladder_step w RInfo = Some RRecord.
Proof. intro w; reflexivity. Qed.

(* the ladder has no skips: only data->info and info->record *)
Theorem ladder_no_skip :
  forall w r r', ladder_step w r = Some r' ->
    (r = RData /\ r' = RInfo) \/ (r = RInfo /\ r' = RRecord).
Proof.
  intros w r r' H; destruct r; simpl in H.
  - destruct (has_channel w); inversion H; left; split; reflexivity.
  - inversion H; right; split; reflexivity.
  - discriminate H.
Qed.

(* the record is the top rung: the ladder ends, no completed svod grows out of it *)
Theorem ladder_ends_at_record : forall w, ladder_step w RRecord = None.
Proof. intro w; reflexivity. Qed.

(* the seam is crossed exactly once, and only by perception *)
Theorem seam_crossing_unique :
  forall w r r', ladder_step w r = Some r' ->
    (rung_field r = LObjective /\ rung_field r' = LSubjective) \/
    (rung_field r = LSubjective /\ rung_field r' = LSubjective).
Proof.
  intros w r r' H; destruct (ladder_no_skip w r r' H) as [[-> ->] | [-> ->]];
  [ left | right ]; split; reflexivity.
Qed.

(* ---------- the will as potential (MP-12) ----------
   The potential between the known and the knowable: the difference of the two
   fields.  The gap canon (KnowledgeGap): every record opens no less new knowable
   than it closes - so the potential never falls below its start. *)

Section WillPotential.

Variable opened closed : nat -> nat.
(* at step k the record closes (closed k) of the knowable and opens (opened k) new *)

Hypothesis opens_no_less : forall k, closed k <= opened k.

Fixpoint potential (p0 : nat) (n : nat) : nat :=
  match n with
  | O => p0
  | S k => potential p0 k + opened k - closed k
  end.

Lemma potential_monotone : forall p0 n, potential p0 n <= potential p0 (S n).
Proof. intros p0 n; simpl; specialize (opens_no_less n); lia. Qed.

Theorem potential_never_below_start : forall p0 n, p0 <= potential p0 n.
Proof.
  intros p0 n; induction n as [| k IH]; [ reflexivity | ].
  eapply Nat.le_trans; [ exact IH | apply potential_monotone ].
Qed.

(* the will never discharges: the pull of cognition is structurally eternal *)
Theorem will_inexhaustible : forall p0 n, 0 < p0 -> 0 < potential p0 n.
Proof.
  intros p0 n H; eapply Nat.lt_le_trans;
  [ exact H | apply potential_never_below_start ].
Qed.

(* the pull works: a patch of the knowable can be selected at EVERY step *)
Definition can_select (p : nat) : bool :=
  match p with O => false | _ => true end.

Theorem selection_always_possible :
  forall p0 n, 0 < p0 -> can_select (potential p0 n) = true.
Proof.
  intros p0 n H; assert (Hp : 0 < potential p0 n) by (apply will_inexhaustible; exact H).
  destruct (potential p0 n); [ lia | reflexivity ].
Qed.

(* honesty: with a dead start (no gap at all) there is nothing to select *)
Theorem no_gap_no_pull : can_select 0 = false.
Proof. reflexivity. Qed.

End WillPotential.

(* ---------- the seam needs both: channel AND pull ---------- *)

Definition perception_fires (w : Witness) (p : nat) : bool :=
  has_channel w && can_select p.

Theorem perception_needs_channel :
  forall w p, channels w = O -> perception_fires w p = false.
Proof. intros [c] p H; unfold perception_fires; simpl in *; rewrite H; reflexivity. Qed.

Theorem perception_needs_pull :
  forall w, perception_fires w 0 = false.
Proof.
  intros [c]; unfold perception_fires; simpl; destruct c; reflexivity.
Qed.

Theorem perception_fires_iff :
  forall w p, perception_fires w p = true <->
    has_channel w = true /\ can_select p = true.
Proof.
  intros w p; unfold perception_fires; split;
  [ intro H; apply andb_prop; exact H
  | intros [H1 H2]; rewrite H1, H2; reflexivity ].
Qed.
