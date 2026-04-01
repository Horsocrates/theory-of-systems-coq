(** * L5CausalOrder.v — L5 order constitutes a causal partial order on events
    Elements: CausalEvent, causally_precedes
    Roles:    L5 ORDER → partial order → causal structure
    Rules:    reflexive, antisymmetric, transitive = partial order
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    KEY CLAIM: L5 order IS the causal structure.
    Events = (site, stage) pairs. Causal precedence requires:
    (1) stage e1 ≤ stage e2 (time flows forward, L5 arrow)
    (2) |site e2 - site e1| ≤ stage e2 - stage e1 (finite propagation, P4)

    This IS a partial order (reflexive, antisymmetric, transitive).
    Spacelike-separated events are incomparable → no total order.
*)

From Stdlib Require Import PeanoNat Lia ZArith.

(* ================================================================ *)
(*  CAUSAL EVENTS                                                    *)
(* ================================================================ *)

Record CausalEvent := mkCE {
  ce_site : nat;
  ce_stage : nat;
}.

(** Causal precedence: stage monotone + spatial distance ≤ temporal distance *)
Definition causally_precedes (e1 e2 : CausalEvent) : Prop :=
  (ce_stage e1 <= ce_stage e2)%nat /\
  (Z.abs (Z.of_nat (ce_site e2) - Z.of_nat (ce_site e1))
   <= Z.of_nat (ce_stage e2 - ce_stage e1))%Z.

(* ================================================================ *)
(*  PARTIAL ORDER PROPERTIES                                         *)
(* ================================================================ *)

Lemma causal_reflexive : forall e, causally_precedes e e.
Proof.
  intro e. unfold causally_precedes. split.
  - lia.
  - rewrite Nat.sub_diag. simpl. lia.
Qed.

Lemma causal_antisymmetric : forall e1 e2,
  causally_precedes e1 e2 -> causally_precedes e2 e1 ->
  ce_stage e1 = ce_stage e2 /\ ce_site e1 = ce_site e2.
Proof.
  intros e1 e2 [Hs1 Hd1] [Hs2 Hd2].
  assert (ce_stage e1 = ce_stage e2) as Heq by lia.
  split; [exact Heq |].
  rewrite Heq in Hd1. rewrite Nat.sub_diag in Hd1. simpl in Hd1.
  rewrite Heq in Hd2. rewrite Nat.sub_diag in Hd2. simpl in Hd2.
  lia.
Qed.

Lemma causal_transitive : forall e1 e2 e3,
  causally_precedes e1 e2 -> causally_precedes e2 e3 ->
  causally_precedes e1 e3.
Proof.
  intros e1 e2 e3 [Hs12 Hd12] [Hs23 Hd23].
  unfold causally_precedes. split.
  - lia.
  - (* Triangle inequality on Z: |x3-x1| ≤ |x2-x1| + |x3-x2| *)
    (* And (s2-s1) + (s3-s2) = s3-s1 *)
    assert (Z.of_nat (ce_stage e3 - ce_stage e1) =
            Z.of_nat (ce_stage e2 - ce_stage e1) +
            Z.of_nat (ce_stage e3 - ce_stage e2))%Z as Hstage.
    { lia. }
    rewrite Hstage.
    assert (Z.abs (Z.of_nat (ce_site e3) - Z.of_nat (ce_site e1)) <=
            Z.abs (Z.of_nat (ce_site e2) - Z.of_nat (ce_site e1)) +
            Z.abs (Z.of_nat (ce_site e3) - Z.of_nat (ce_site e2)))%Z as Htri.
    { lia. }
    lia.
Qed.

Theorem causal_is_partial_order :
  (forall e, causally_precedes e e) /\
  (forall e1 e2, causally_precedes e1 e2 -> causally_precedes e2 e1 ->
    ce_stage e1 = ce_stage e2 /\ ce_site e1 = ce_site e2) /\
  (forall e1 e2 e3, causally_precedes e1 e2 -> causally_precedes e2 e3 ->
    causally_precedes e1 e3).
Proof.
  split; [exact causal_reflexive |
  split; [exact causal_antisymmetric |
  exact causal_transitive]].
Qed.

(* ================================================================ *)
(*  NO BACKWARD CAUSATION                                            *)
(* ================================================================ *)

Lemma no_backward : forall e1 e2,
  (ce_stage e2 < ce_stage e1)%nat -> ~ causally_precedes e1 e2.
Proof.
  intros e1 e2 Hlt [Hs _]. lia.
Qed.

(* ================================================================ *)
(*  SPACELIKE SEPARATION = INCOMPARABILITY                           *)
(* ================================================================ *)

(** Concrete witness: events at (0,0) and (5,1) are spacelike *)
Definition origin := mkCE 0 0.
Definition far_event := mkCE 5 1.

Lemma spacelike_not_causal : ~ causally_precedes origin far_event.
Proof.
  unfold causally_precedes, origin, far_event. simpl.
  intros [_ H]. lia.
Qed.

Lemma spacelike_not_causal_rev : ~ causally_precedes far_event origin.
Proof.
  unfold causally_precedes, far_event, origin. simpl.
  intros [H _]. lia.
Qed.

(** These events are INCOMPARABLE in the partial order *)
Theorem spacelike_incomparable :
  ~ causally_precedes origin far_event /\
  ~ causally_precedes far_event origin.
Proof.
  split; [exact spacelike_not_causal | exact spacelike_not_causal_rev].
Qed.

(* ================================================================ *)
(*  TIMELIKE = COMPARABLE                                            *)
(* ================================================================ *)

Definition next_event := mkCE 0 1.

Lemma timelike_causal : causally_precedes origin next_event.
Proof.
  unfold causally_precedes, origin, next_event. simpl. lia.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem l5_causal_synthesis :
  (* Partial order *)
  (forall e, causally_precedes e e) /\
  (forall e1 e2, causally_precedes e1 e2 -> causally_precedes e2 e1 ->
    ce_stage e1 = ce_stage e2 /\ ce_site e1 = ce_site e2) /\
  (forall e1 e2 e3, causally_precedes e1 e2 -> causally_precedes e2 e3 ->
    causally_precedes e1 e3) /\
  (* No backward causation *)
  (forall e1 e2, (ce_stage e2 < ce_stage e1)%nat ->
    ~ causally_precedes e1 e2) /\
  (* Spacelike incomparability exists *)
  ~ causally_precedes origin far_event /\
  ~ causally_precedes far_event origin.
Proof.
  split; [exact causal_reflexive |
  split; [exact causal_antisymmetric |
  split; [exact causal_transitive |
  split; [exact no_backward |
  split; [exact spacelike_not_causal |
  exact spacelike_not_causal_rev]]]]].
Qed.
