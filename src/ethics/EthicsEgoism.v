(** * EthicsEgoism.v — Egoism: the standing attunement to the ego-zone — the ego-thread tail closed into Ethics
    Canon (R-119..R-121, working journal Knigi/Etika/00, 2026-07-24; ego thread MP-37..41):
    egoism = the STANDING attunement (ustanovka) to one's ego-zone as the goal — the
    same goal a lie has, but a lie is an ACT and egoism the stance acts grow from; in
    the intent matrix egoism is the ORIENTATION of the interest axis, not a cell — by
    itself not evil (exchange is lawful), evil arises only joined with trampling the
    Other's will; the boundary with self-care is DISPLACEMENT: care keeps truth in the
    center, egoism puts the ego-zone INSTEAD of truth; egoism serves the RECORD (the
    image), not the witness — records never will, so the will is spent on what cannot
    will back; the classical antipode "altruism" is the SAME displacement onto the
    other's record — the true antipode is the attunement to truth; the egoist operator
    assigns by zone-favor, not by fit — the root of operator injustice; and egoism
    freezes the self-record while the living truth moves — epistemic blindness.

    Elements: centers of attention (truth / own zone / other's zone); acts with a
              center and a beneficiary; entities (witness / record); candidates
              (fit x zone-favor); the frozen and the tracking self-record.
    Roles:    Stance = the chronicle of centers (nat -> Center); the standing
              attunement; the interest-axis orientation; the served entity; the
              operator's pick.
    Rules:    egoism = own-zone center at EVERY step (one act is not a stance);
              evil = conjunction (against the will AND own interest); the
              care/egoism boundary is the center, not the beneficiary; records do
              not will; the third center defeats the egoism/altruism dichotomy;
              a frozen record misses the moving truth unboundedly.
    Status:   all proved; self-contained (Entity/can_will replicated in spirit from
              KnowledgeEgoZone.v per the house convention; the intent matrix is the
              bool shadow of EthicsIntentDeep.v).
    STATUS: 19 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(* ================================================================ *)
(** ** 1. The center of attention; act vs stance                     *)
(* ================================================================ *)

(** What stands in the center of attention. Three values — the third
    center is what defeats the classical binary (section 5). *)
Inductive Center : Type := CTruth | COwnZone | COtherZone.

(** A stance is the CHRONICLE of centers: what the attunement holds at
    every step. The "-ism" of the etymology: not one act but a standing. *)
Definition Stance : Type := nat -> Center.

(** A self-serving act: at step n the own zone stands in the center —
    the lie's attunement (its goal is personal interest, not truth). *)
Definition self_serving_act (s : Stance) (n : nat) : Prop := s n = COwnZone.

(** EGOISM: the standing attunement — the own zone in the center at
    every step. *)
Definition egoism (s : Stance) : Prop := forall n, s n = COwnZone.

(** The mirror stances. *)
Definition altruism (s : Stance) : Prop := forall n, s n = COtherZone.
Definition truth_stance (s : Stance) : Prop := forall n, s n = CTruth.

(** ★ The stance births the acts: an egoist stance makes every step a
    self-serving act (the lie is an act; egoism is where acts grow from). *)
Theorem egoism_births_acts : forall s, egoism s -> forall n, self_serving_act s n.
Proof. intros s H n. exact (H n). Qed.

(** ★ One act is NOT the stance: a single self-serving act does not
    make the chronicle egoist. *)
Definition one_act : Stance := fun n => match n with O => COwnZone | _ => CTruth end.

Theorem act_is_not_stance : self_serving_act one_act 0 /\ ~ egoism one_act.
Proof.
  split; [ reflexivity | intros H; specialize (H 1); discriminate H ].
Qed.

(* ================================================================ *)
(** ** 2. The intent matrix: orientation, not a cell                 *)
(* ================================================================ *)

(** The bool shadow of the intent matrix (EthicsIntentDeep): a cell is
    (against the Other's will?, own interest?); evil is the conjunction. *)
Definition evil_cell (against_will own_interest : bool) : bool :=
  against_will && own_interest.

(** ★ The orientation alone is not evil: own interest WITH the Other's
    will is the lawful exchange. *)
Theorem orientation_alone_not_evil : evil_cell false true = false.
Proof. reflexivity. Qed.

(** Evil needs BOTH factors. *)
Theorem evil_needs_both : forall a o,
  evil_cell a o = true <-> a = true /\ o = true.
Proof.
  intros a o; destruct a, o; simpl; split; intro H.
  - split; reflexivity.
  - reflexivity.
  - discriminate H.
  - destruct H as [_ H2]; discriminate H2.
  - discriminate H.
  - destruct H as [H1 _]; discriminate H1.
  - discriminate H.
  - destruct H as [H1 _]; discriminate H1.
Qed.

(** ★ Egoism supplies the orientation; joined with trampling the will
    it lands exactly on the evil pole. *)
Theorem egoism_plus_trampling_is_evil : forall o, o = true -> evil_cell true o = true.
Proof. intros o H. rewrite H. reflexivity. Qed.

(* ================================================================ *)
(** ** 3. The boundary with self-care: displacement                  *)
(* ================================================================ *)

Record Act : Type := mkAct { center : Center; benefits_self : bool }.

(** Care: truth stays in the center AND the act benefits the self —
    the self as a part of the order. Lawful. *)
Definition care_act (a : Act) : Prop := center a = CTruth /\ benefits_self a = true.

(** An egoist act: the own zone stands in the center. *)
Definition egoism_act (a : Act) : Prop := center a = COwnZone.

(** ★ Care is not egoism — by the CENTER, whatever the beneficiary. *)
Theorem care_is_not_egoism : forall a, care_act a -> ~ egoism_act a.
Proof.
  intros a [Hc _] He. unfold egoism_act in He. rewrite Hc in He. discriminate He.
Qed.

(** ★★ The boundary is the center, not the beneficiary: two acts with
    the SAME beneficiary (the self), one care, one egoism. *)
Theorem boundary_is_center_not_beneficiary :
  exists a b, benefits_self a = benefits_self b /\ care_act a /\ egoism_act b.
Proof.
  exists (mkAct CTruth true), (mkAct COwnZone true).
  split; [ reflexivity | split; [ split; reflexivity | reflexivity ] ].
Qed.

(* ================================================================ *)
(** ** 4. Serving the record: the will spent on what cannot will      *)
(* ================================================================ *)

(** Replicated in spirit from KnowledgeEgoZone.v: only the witness
    wills; a record of self never does. *)
Inductive Entity : Type := Witness | RecordOfSelf.

Definition can_will (e : Entity) : bool :=
  match e with Witness => true | RecordOfSelf => false end.

(** A zone-centered stance serves records (own or the other's). *)
Definition serves_record (s : Stance) : Prop :=
  forall n, s n = COwnZone \/ s n = COtherZone.

(** ★ Egoism serves the record — the image, not the witness. *)
Theorem egoism_serves_record : forall s, egoism s -> serves_record s.
Proof. intros s H n. left. exact (H n). Qed.

(** ★ And the record never wills back: the will is spent on what
    cannot will — the reification of the impossibility registry. *)
Theorem record_returns_no_will : can_will RecordOfSelf = false.
Proof. reflexivity. Qed.

(* ================================================================ *)
(** ** 5. The false dichotomy: the antipode is truth, not altruism    *)
(* ================================================================ *)

(** Displacement: at some step truth is NOT in the center. *)
Definition displaced (s : Stance) : Prop := exists n, s n <> CTruth.

Theorem egoism_displaces : forall s, egoism s -> displaced s.
Proof. intros s H. exists 0. rewrite H. discriminate. Qed.

(** ★ Altruism displaces truth the SAME way — the other's record in
    the center is still a record instead of truth. *)
Theorem altruism_displaces : forall s, altruism s -> displaced s.
Proof. intros s H. exists 0. rewrite H. discriminate. Qed.

(** The third center exists — the binary egoism/altruism is not a
    dichotomy of the center. *)
Theorem third_center_exists :
  CTruth <> COwnZone /\ CTruth <> COtherZone /\ COwnZone <> COtherZone.
Proof. split; [ discriminate | split; discriminate ]. Qed.

(** ★★ The true antipode: the truth-stance never displaces — and an
    altruist stance both exists and displaces. *)
Theorem antipode_is_truth_not_altruism :
  (forall s, truth_stance s -> ~ displaced s) /\
  (exists s, altruism s /\ displaced s).
Proof.
  split.
  - intros s Ht [n Hn]. apply Hn. exact (Ht n).
  - exists (fun _ => COtherZone). split.
    + intro n. reflexivity.
    + exists 0. discriminate.
Qed.

(* ================================================================ *)
(** ** 6. The egoist operator: assignment by zone, not by fit         *)
(* ================================================================ *)

Record Candidate : Type := mkCand { fits : bool; favors_zone : bool }.

(** The fair pick reads the fit; the egoist pick reads the zone-favor. *)
Definition fair_pick (c : Candidate) : bool := fits c.
Definition egoist_pick (c : Candidate) : bool := favors_zone c.

(** ★ The egoist assignment is unjust: an unfit candidate picked for
    favoring the zone. *)
Theorem egoist_assignment_unjust :
  exists c, fair_pick c = false /\ egoist_pick c = true.
Proof. exists (mkCand false true). split; reflexivity. Qed.

(** The injustice is witnessed: the two picks genuinely differ. *)
Theorem injustice_witnessed : exists c, egoist_pick c <> fair_pick c.
Proof. exists (mkCand false true). simpl. discriminate. Qed.

(* ================================================================ *)
(** ** 7. Epistemic blindness: the frozen record misses moving truth  *)
(* ================================================================ *)

(** The living truth about the self moves with the steps. *)
Fixpoint alt (n : nat) : bool :=
  match n with O => false | S k => negb (alt k) end.

(** Egoism freezes the record: the image must stand. *)
Definition frozen_record : nat -> bool := fun _ => false.

(** A tracking record follows the truth. *)
Definition updated_record : nat -> bool := alt.

(** ★★ The frozen record misses the truth UNBOUNDEDLY often: past any
    step there is a step where record and truth disagree. *)
Theorem frozen_misses_unboundedly :
  forall n, exists m, n <= m /\ frozen_record m <> alt m.
Proof.
  intro n. destruct (alt n) eqn:E.
  - exists n. split; [ lia | ]. unfold frozen_record. rewrite E. discriminate.
  - exists (S n). split; [ lia | ]. unfold frozen_record. simpl. rewrite E.
    simpl. discriminate.
Qed.

(** The tracking record never misses. *)
Theorem updated_never_misses : forall n, updated_record n = alt n.
Proof. intro n. reflexivity. Qed.

(** ★ The illusion of self-knowledge: the frozen record stands as
    knowledge while disagreeing with the truth. *)
Definition illusion_of_self_knowledge (r : nat -> bool) (n : nat) : Prop :=
  r n <> alt n.

Theorem egoism_breeds_illusion : exists n, illusion_of_self_knowledge frozen_record n.
Proof.
  destruct (frozen_misses_unboundedly 0) as [m [_ Hm]]. exists m. exact Hm.
Qed.

(* ================================================================ *)
(** ** 8. Capstone: the canon of egoism in one statement              *)
(* ================================================================ *)

Theorem egoism_canon :
  (forall s, egoism s -> forall n, self_serving_act s n) /\
  (evil_cell false true = false /\ (forall o, o = true -> evil_cell true o = true)) /\
  (forall a, care_act a -> ~ egoism_act a) /\
  ((forall s, egoism s -> serves_record s) /\ can_will RecordOfSelf = false) /\
  ((forall s, truth_stance s -> ~ displaced s) /\ (exists s, altruism s /\ displaced s)) /\
  (exists c, egoist_pick c <> fair_pick c) /\
  (forall n, exists m, n <= m /\ frozen_record m <> alt m).
Proof.
  split; [ exact egoism_births_acts | ].
  split; [ split; [ exact orientation_alone_not_evil
                  | exact egoism_plus_trampling_is_evil ] | ].
  split; [ exact care_is_not_egoism | ].
  split; [ split; [ exact egoism_serves_record | exact record_returns_no_will ] | ].
  split; [ exact antipode_is_truth_not_altruism | ].
  split; [ exact injustice_witnessed | exact frozen_misses_unboundedly ].
Qed.

Print Assumptions egoism_canon.

(* ========================================================================= *)
(*  SUMMARY: 19 Qed, 0 Admitted, 0 axioms.                                    *)
(*  Egoism = the standing attunement to the ego-zone (stance, not act);       *)
(*  orientation of the interest axis (evil only WITH trampling the will);     *)
(*  boundary with care = displacement of truth from the center;               *)
(*  serves the record which never wills back; the antipode is the             *)
(*  truth-stance, not altruism (third center); the egoist operator assigns    *)
(*  by zone-favor against fit (injustice witnessed); the frozen self-record   *)
(*  misses the moving truth unboundedly (epistemic blindness).                *)
(*  Capstone: egoism_canon.                                                   *)
(* ========================================================================= *)
