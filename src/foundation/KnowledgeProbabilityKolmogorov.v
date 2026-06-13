(** * KnowledgeProbabilityKolmogorov.v — the FORCED Kolmogorov skeleton (deepening of
      KnowledgeProbability's honest stop): non-negativity, normalization, additivity, [0,1],
      complement are STRUCTURALLY forced; only the FORM of the weights (|psi|^2) is physics

    Direction C (honest deepening).  KnowledgeProbability.v proved that probability lives on the
    boundary and measures unclampedness, and STOPPED honestly at weight_form_underdetermined (the
    |psi|^2 form is not structurally fixed).  That stop can be SHARPENED: what is NOT forced is the
    FORM; what IS forced is the Kolmogorov SKELETON.  Once ЗДО distributes the ground as a
    non-negative weight on each admissible outcome, normalized to the total, the structure forces:

      K1 non-negativity   — every event has probability >= 0          (qsum_nonneg);
      K2 normalization     — the whole has probability 1               (hypothesis, used);
      K3 additivity        — disjoint events add                       (qsum_app);
      bounded             — every event lies in [0,1]                 (event_in_unit);
      complement          — P(A) + P(not A) = 1                       (complement_rule).

    What stays free (the wall, now sharper): the WEIGHTS themselves.  Two distinct non-negative
    normalized distributions on the same admissible set satisfy ALL of the above
    (form_underdetermined_normalized) — the skeleton is forced, the form is physics (Born |psi|^2).
    Bridges: a determined (full-clamp) transition forces the point mass = certainty
    (determined_is_certainty, on KnowledgeProbability.determined); a free transition admits a
    distribution (free_admits_distribution) — ЗДО is satisfiable, just not uniquely.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) ЗДО distributes the ground => a NON-NEGATIVE weight on each admissible outcome;
      (2) the total ground is normalizable to 1;
      (3) probability is ADDITIVE over disjoint events (sum over concatenation);
      (4) the FORM of the weights is NOT forced — physics-tier content.
    Roles (L4): the distribution = the load-bearing role (ground spread by ЗДО); an event = a
      selection of outcomes; probability = the weight-sum; normalization = total ground = 1; the
      weight form = physics.
    Elements (L1+P4): admissible outcomes (adm); weights p : O -> Q; events (sublists).
    P4 diagnostic (could it be otherwise?):
      The Kolmogorov skeleton (non-neg / normalization / additivity / [0,1] / complement) is FORCED
      by "a non-negative normalized weight over the admissible"; the FORM (which weights — the Born
      |psi|^2) is FREE (physics).  This sharpens KnowledgeProbability.weight_form_underdetermined:
      not "no probability structure", but "the structure = the Kolmogorov skeleton is forced, the
      form is free".
    Honesty wall:
      |psi|^2 stays behind the wall (physics — BornRule.v cited there, not appropriated); the
      deepening only makes the wall SHARPER — what is in front of it (the skeleton) vs behind it
      (the form).  Q weights are the structural proxy for the distributed ground.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa List Lia.
Import ListNotations.
From ToS Require Import foundation.KnowledgeProbability.   (* determined, free, unclampedness *)
Open Scope Q_scope.

(** A probability assignment: a weight on each outcome.  Its sum over a (finite) list of outcomes. *)
Definition qsum {O : Type} (p : O -> Q) (l : list O) : Q :=
  fold_right (fun o acc => p o + acc) 0 l.

(* ===================================================================== *)
(*  K3 — additivity over disjoint events (concatenation)                   *)
(* ===================================================================== *)

(** ★ K3: probability is additive — disjoint events (concatenated) add their weight-sums. *)
Lemma qsum_app : forall {O} (p : O -> Q) (l1 l2 : list O),
  qsum p (l1 ++ l2) == qsum p l1 + qsum p l2.
Proof.
  intros O p l1 l2. induction l1 as [|a l1 IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  K1 — non-negativity                                                    *)
(* ===================================================================== *)

(** ★ K1: a non-negative weight gives every event a non-negative probability. *)
Lemma qsum_nonneg : forall {O} (p : O -> Q) (l : list O),
  (forall o, In o l -> 0 <= p o) -> 0 <= qsum p l.
Proof.
  intros O p l. induction l as [|a l IH]; intro H; simpl.
  - lra.
  - assert (Ha : 0 <= p a) by (apply H; left; reflexivity).
    assert (Hl : 0 <= qsum p l) by (apply IH; intros o Ho; apply H; right; exact Ho).
    lra.
Qed.

(* ===================================================================== *)
(*  bounded — every event lies in [0,1]; complement                        *)
(* ===================================================================== *)

(** ★ Bounded: under normalization, an event's probability lies in [0,1] (its complement carries
    the rest). *)
Theorem event_in_unit : forall {O} (p : O -> Q) (ev co : list O),
  (forall o, In o (ev ++ co) -> 0 <= p o) ->
  qsum p (ev ++ co) == 1 ->
  0 <= qsum p ev /\ qsum p ev <= 1.
Proof.
  intros O p ev co Hnn Hnorm.
  assert (Hev : 0 <= qsum p ev)
    by (apply qsum_nonneg; intros o Ho; apply Hnn; apply in_or_app; left; exact Ho).
  assert (Hco : 0 <= qsum p co)
    by (apply qsum_nonneg; intros o Ho; apply Hnn; apply in_or_app; right; exact Ho).
  rewrite qsum_app in Hnorm.
  split; [ exact Hev | lra ].
Qed.

(** ★ Complement: P(A) + P(not A) = 1 (the event and its complement partition the whole). *)
Theorem complement_rule : forall {O} (p : O -> Q) (ev co : list O),
  qsum p (ev ++ co) == 1 -> qsum p ev + qsum p co == 1.
Proof. intros O p ev co H. rewrite <- qsum_app. exact H. Qed.

(* ===================================================================== *)
(*  Bridges to KnowledgeProbability — full clamp / free transition         *)
(* ===================================================================== *)

(** ★ Full clamp = certainty: a DETERMINED transition (one admissible outcome) forces the point
    mass — the whole ground sits on the one outcome, weight 1.  (Bridge to
    KnowledgeProbability.determined / full_clamp_is_determinism.) *)
Theorem determined_is_certainty : forall {O} (p : O -> Q) (adm : list O),
  determined adm -> qsum p adm == 1 -> exists o, adm = [o] /\ p o == 1.
Proof.
  intros O p adm [o ->] Hnorm. exists o. split; [ reflexivity | ].
  simpl in Hnorm. rewrite Qplus_0_r in Hnorm. exact Hnorm.
Qed.

(** ★ A FREE transition admits a distribution: ЗДО is satisfiable (here the uniform 1/2 on two
    admissible outcomes) — non-negative and normalized.  (Bridge to KnowledgeProbability.free:
    [a;b] is free.)  So a distribution is FORCED to exist; its form is not unique (next). *)
Theorem free_admits_distribution : forall {O} (a b : O),
  a <> b ->
  exists p : O -> Q, (forall o, In o [a; b] -> 0 <= p o) /\ qsum p [a; b] == 1.
Proof.
  intros O a b _. exists (fun _ => 1 # 2). split.
  - intros o _. unfold Qle; simpl; lia.
  - simpl. ring.
Qed.

(* ===================================================================== *)
(*  THE WALL (sharper) — the FORM of the weights is free                   *)
(* ===================================================================== *)

(** ★★ THE HONEST WALL, sharpened: two DISTINCT non-negative NORMALIZED distributions on the same
    admissible set satisfy the entire Kolmogorov skeleton — so the skeleton is forced, but the FORM
    (the actual weights, the Born |psi|^2) is NOT.  (Lifts KnowledgeProbability.
    weight_form_underdetermined to the normalized probability layer.) *)
Theorem form_underdetermined_normalized :
  exists (O : Type) (a b : O) (adm : list O) (p1 p2 : O -> Q),
    a <> b /\ adm = [a; b]
    /\ (forall o, In o adm -> 0 <= p1 o) /\ qsum p1 adm == 1
    /\ (forall o, In o adm -> 0 <= p2 o) /\ qsum p2 adm == 1
    /\ (exists o, In o adm /\ ~ p1 o == p2 o).
Proof.
  exists bool, true, false, [true; false],
    (fun o : bool => if o then 1 # 2 else 1 # 2),
    (fun o : bool => if o then 1 # 3 else 2 # 3).
  split; [ discriminate | ].
  split; [ reflexivity | ].
  split; [ intros o _; destruct o; (unfold Qle; simpl; lia) | ].
  split; [ simpl; ring | ].
  split; [ intros o _; destruct o; (unfold Qle; simpl; lia) | ].
  split; [ simpl; ring | ].
  exists true. split; [ simpl; left; reflexivity | ].
  intro H. unfold Qeq in H. simpl in H. discriminate H.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The Kolmogorov skeleton is FORCED (additivity, non-negativity, bounded in [0,1]); the FORM
    of the weights is FREE.  Probability's STRUCTURE is derived; its |psi|^2 FORM is physics. *)
Theorem kolmogorov_skeleton_capstone :
  (forall (O : Type) (p : O -> Q) (e1 e2 : list O), qsum p (e1 ++ e2) == qsum p e1 + qsum p e2)
  /\ (forall (O : Type) (p : O -> Q) (l : list O), (forall o, In o l -> 0 <= p o) -> 0 <= qsum p l)
  /\ (forall (O : Type) (p : O -> Q) (ev co : list O),
        (forall o, In o (ev ++ co) -> 0 <= p o) -> qsum p (ev ++ co) == 1 ->
        0 <= qsum p ev /\ qsum p ev <= 1)
  /\ (exists (O : Type) (a b : O) (adm : list O) (p1 p2 : O -> Q),
        a <> b /\ adm = [a; b]
        /\ (forall o, In o adm -> 0 <= p1 o) /\ qsum p1 adm == 1
        /\ (forall o, In o adm -> 0 <= p2 o) /\ qsum p2 adm == 1
        /\ (exists o, In o adm /\ ~ p1 o == p2 o)).
Proof.
  split; [ exact @qsum_app | ].
  split; [ exact @qsum_nonneg | ].
  split; [ exact @event_in_unit | exact form_underdetermined_normalized ].
Qed.

Print Assumptions kolmogorov_skeleton_capstone.
Print Assumptions form_underdetermined_normalized.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The Kolmogorov SKELETON is structurally FORCED: additivity (qsum_app, K3),*)
(*  non-negativity (qsum_nonneg, K1), bounded in [0,1] (event_in_unit),       *)
(*  complement (complement_rule); a full clamp forces certainty               *)
(*  (determined_is_certainty), a free transition admits a distribution        *)
(*  (free_admits_distribution).  The FORM of the weights stays FREE           *)
(*  (form_underdetermined_normalized — two normalized non-negative            *)
(*  distributions on the same set).  Deepens KnowledgeProbability's honest    *)
(*  stop: the structure = the Kolmogorov skeleton is derived; the |psi|^2     *)
(*  form is physics (cited, not appropriated).                               *)
(* ========================================================================= *)
