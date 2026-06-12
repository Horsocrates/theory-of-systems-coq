(** * KnowledgeInsight.v — F-39 branch «Усмотрение»: insight (усмотрение) as the WHOLE-channel of
      knowledge-THAT; intuition is a channel of information, NOT presence

    Formalizes the structural core of the derivation "Усмотрение" (Книги/Теория Знания/Усмотрение.md),
    the last unit of the Теория Знания branch.  It carries the AUTHOR'S CORRECTION (2026-06-12):

      the identification "intuition / insight = a channel of knowledge-PRESENCE" is REMOVED.
      Canon: INTUITION (усмотрение) is a method/channel for obtaining INFORMATION — it carries only
      knowledge-THAT, grasped as a whole.  PRESENCE (присутствие) is the DIRECT observation by
      consciousness of the knowable object — the meeting itself — and is NOT a channel-method.
      Intuitive knowledge can arrive DURING presence, but they are different things.

    THE TRIAD OF FULFILLMENT (§2), dictated by the knowledge type's ground:
      - присутствие  <- the MEETING (встреча): direct observation; NOT a channel.
      - знание-о     <- TWO channels: УСМОТРЕНИЕ (by the whole, the vertical-up channel) and
                        ДИСКУРСИЯ (by details, along the tier — unfolded in speech, transferable).
      - знание-как   <- ПРОХОЖДЕНИЕ (passing through the process's stages, in its own time).

    WHAT IS PROVED (structural):
      §2  the modes are dictated by the type; знание-о has exactly TWO channels; the meeting is NOT
          a channel; усмотрение serves знание-о, NOT присутствие (the correction, as a theorem).
      §3  усмотрение is the unique UPWARD channel (reads the encompassing whole) — closing the
          "forest for trees" up-failure of «Глубина».
      §4  the riddle: GRASP (one act) precedes UNDERSTANDING (which follows the in-order ladder,
          KnowledgeDepth.tiers_mastered_in_order) — Order governs understanding, not grasping, so
          усмотрение crowns the order, it does not violate it (Poincaré).
      §5  the three conditions of intuition = the two depth limiters (threshold, channel) PLUS a
          third the passive limiters lack — the REQUEST (activation, will-in-the-gap).
      §6  усмотрение and its articulation (дискурсия) are DISTINCT channels of знание-о; the grasped
          whole must be articulated to become transferable.

    ============================== E/R/R разбор ==============================
    Elements: the ways of fulfilling grounds (the meeting; the information channels усмотрение /
              дискурсия; прохождение); the request; the whole-gestalt; beginnings; purity obstacles.
    Roles:    the meeting = the ground of PRESENCE (direct observation, NOT a channel); усмотрение =
              channel of information by-the-whole and up the vertical (знание-о); дискурсия = channel
              of information by-details (along the tier, transferable; знание-о); прохождение = the
              path of знание-как; request = activation (will-in-the-gap); articulation = unfolding
              the whole into details; verification = the filter of false insights.
    Rules:    (1) the mode of fulfillment is dictated by the type's ground; (2) усмотрение passes the
              ladder in whole-mode, not skipping steps; (3) Order limits understanding by tiers, not
              the meeting — усмотрение after preparation is the fruit of the threshold, not a jump;
              (4) the beginnings of дискурсия are supplied by усмотрение; (5) transmitting the insight
              requires unfolding the whole into details; (6) channel purity — verification mandatory.
    P4 diagnostic: the co-presence mechanism is not asserted (open node, borders «Связь ярусов»);
              ranks "higher/lower" are not asserted — these are TYPES and ROLES; the convergence of
              the intuition conditions with the depth limiters is exact in two of three (threshold,
              channel), the request being an activation addition.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia Bool.
Import ListNotations.
From ToS Require Import foundation.KnowledgeInformation.   (* KnowType = KPresence | KThat | KHow (§5) *)
From ToS Require Import foundation.KnowledgeDepth.          (* tiers_mastered_in_order — the in-order ladder *)

(* ===================================================================== *)
(*  §2 — the triad of fulfillment, and the author's correction            *)
(* ===================================================================== *)

(** The ways a ground is fulfilled: the MEETING (presence, not a channel), and the channels/path
    of information — усмотрение (whole), дискурсия (details), прохождение (the знание-как path). *)
Inductive Mode := Meeting | Usmotrenie | Discursion | Passing.

(** The meeting is NOT a channel; the other three are channels/paths of obtaining content. *)
Definition is_channel (m : Mode) : bool :=
  match m with Meeting => false | _ => true end.

(** Which modes fulfill which knowledge type (§2): presence by the meeting; знание-о by its two
    channels (усмотрение / дискурсия); знание-как by прохождение. *)
Definition fulfills (t : KnowType) (m : Mode) : Prop :=
  match t, m with
  | KPresence, Meeting   => True
  | KThat, Usmotrenie    => True
  | KThat, Discursion    => True
  | KHow, Passing        => True
  | _, _                 => False
  end.

(** ★★ THE AUTHOR'S CORRECTION (2026-06-12), as a theorem: усмотрение is a channel of knowledge-
    THAT, NOT of presence.  Intuition carries information (знание-о grasped whole); it is not the
    presence-channel. *)
Theorem usmotrenie_is_a_that_channel :
  fulfills KThat Usmotrenie /\ ~ fulfills KPresence Usmotrenie.
Proof. split; [ exact I | intro H; exact H ]. Qed.

(** ★ Presence is the MEETING — direct observation, NOT a channel.  Everything that fulfills
    presence is the meeting, which carries no channel. *)
Theorem presence_is_the_meeting_not_a_channel :
  fulfills KPresence Meeting
  /\ is_channel Meeting = false
  /\ (forall m, fulfills KPresence m -> is_channel m = false).
Proof.
  split; [ exact I | split; [ reflexivity | ] ].
  intros m H. destruct m; simpl in H; try contradiction; reflexivity.
Qed.

(** ★ Knowledge-THAT has exactly TWO channels — усмотрение (whole) and дискурсия (details) —
    distinct, and both genuine channels. *)
Theorem that_has_two_channels :
  fulfills KThat Usmotrenie /\ fulfills KThat Discursion
  /\ Usmotrenie <> Discursion
  /\ is_channel Usmotrenie = true /\ is_channel Discursion = true.
Proof.
  split; [ exact I | ].
  split; [ exact I | ].
  split; [ discriminate | ].
  split; [ reflexivity | reflexivity ].
Qed.

(** Each type has its mode of access (каков способ исполнения основания, таков и доступ). *)
Theorem each_type_fulfilled : forall t : KnowType, exists m, fulfills t m.
Proof.
  intro t. destruct t.
  - exists Meeting. exact I.
  - exists Usmotrenie. exact I.
  - exists Passing. exact I.
Qed.

(* ===================================================================== *)
(*  §3 — усмотрение is the UPWARD channel; the three directions           *)
(* ===================================================================== *)

(** The direction each channel moves: усмотрение UP (to the encompassing whole), дискурсия ALONG
    the tier (detail by detail), прохождение IN the process's TIME.  The meeting has no channel
    direction. *)
Inductive Direction := Up | Along | InTime.

Definition channel_direction (m : Mode) : option Direction :=
  match m with
  | Usmotrenie => Some Up
  | Discursion => Some Along
  | Passing    => Some InTime
  | Meeting    => None
  end.

Theorem usmotrenie_reads_up : channel_direction Usmotrenie = Some Up.
Proof. reflexivity. Qed.

(** ★ Усмотрение is the UNIQUE upward channel — the one by which the whole (the "forest", the
    encompassing tier) is read; it closes the up-failure of «Глубина» (reaches_up). *)
Theorem usmotrenie_unique_up : forall m, channel_direction m = Some Up -> m = Usmotrenie.
Proof. intros m H. destruct m; simpl in H; try discriminate; reflexivity. Qed.

(* ===================================================================== *)
(*  §4 — the riddle: GRASP (one act) precedes UNDERSTANDING (in order)     *)
(* ===================================================================== *)

(** Grasping the whole is ONE act (whole-mode); understanding it scales with its parts (discursive,
    detail by detail). *)
Definition grasp_cost : nat := 1.
Definition understand_cost (parts : list nat) : nat := length parts.

(** ★ A whole with >= 2 parts is GRASPED before it is UNDERSTOOD: grasp is one act, understanding
    is many.  Sch-vatit' tseloe mozhno srazu; ponimanie tselogo — tol'ko po poryadku. *)
Theorem grasp_cheaper_than_understanding : forall parts,
  (2 <= length parts)%nat -> (grasp_cost < understand_cost parts)%nat.
Proof. intros parts H. unfold grasp_cost, understand_cost. lia. Qed.

(** ★★ The riddle resolved: усмотрение gives GRASP (one act), while UNDERSTANDING follows the
    in-order ladder (KnowledgeDepth.tiers_mastered_in_order — the threshold climbs tier by tier, no
    skipping).  Order governs understanding, not grasping — so усмотрение crowns the order, it does
    not violate it (Poincaré: the whole that comes "by itself" is the fruit of the traversed path). *)
Theorem usmotrenie_resolves_riddle :
  (forall parts, (2 <= length parts)%nat -> (grasp_cost < understand_cost parts)%nat)
  /\ (forall (thr : nat -> nat), thr 0 = 0 -> (forall n, thr (S n) <= S (thr n)) ->
        forall n k, (k <= thr n)%nat -> exists m, (m <= n)%nat /\ thr m = k).
Proof. split; [ exact grasp_cheaper_than_understanding | exact tiers_mastered_in_order ]. Qed.

(* ===================================================================== *)
(*  §5 — the three conditions = two depth limiters + the request           *)
(* ===================================================================== *)

(** Intuition fires given: the threshold (= complexity, a depth limiter), an open channel (= the
    channel limiter), AND the request (= activation, the will-in-the-gap the passive limiters lack). *)
Definition usmotrenie_fires (threshold_ok channel_ok requested : bool) : bool :=
  threshold_ok && channel_ok && requested.

(** ★ All three conditions are needed.  Two are the depth limiters (KnowledgeDepth); the third —
    the request — is the activation addition. *)
Theorem usmotrenie_needs_all_three : forall t c r,
  usmotrenie_fires t c r = true <-> (t = true /\ c = true /\ r = true).
Proof. intros t c r. unfold usmotrenie_fires. rewrite !andb_true_iff. tauto. Qed.

(** ★ The request is the genuine extra: a sufficient threshold and an open channel do NOT fire
    усмотрение without the request — intuition responds, it does not run on schedule. *)
Theorem request_is_the_extra : usmotrenie_fires true true false = false.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  §6 — articulation: the grasped whole becomes transferable via дискурсия *)
(* ===================================================================== *)

(** ★ §6 Усмотрение (the whole) and ДИСКУРСИЯ (its articulation into details) are DISTINCT channels
    of знание-о.  The grasped whole is not yet a detail-sequence; ARTICULATION (Usmotrenie ->
    Discursion) unfolds it into the transferable, verifiable form.  intellectus sees whole, ratio
    unfolds it. *)
Theorem articulation_changes_channel :
  fulfills KThat Usmotrenie /\ fulfills KThat Discursion /\ Usmotrenie <> Discursion.
Proof. split; [ exact I | split; [ exact I | discriminate ] ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ Усмотрение is the WHOLE-channel of knowledge-THAT (the correction: NOT a presence-channel);
    presence is the meeting, not a channel; усмотрение is the unique upward channel; and grasping
    the whole (one act) precedes understanding it (the in-order ladder). *)
Theorem insight_capstone :
  (fulfills KThat Usmotrenie /\ ~ fulfills KPresence Usmotrenie)             (* correction *)
  /\ (fulfills KPresence Meeting /\ is_channel Meeting = false)               (* presence = meeting, not a channel *)
  /\ (forall m, channel_direction m = Some Up -> m = Usmotrenie)              (* unique upward channel *)
  /\ (forall parts, (2 <= length parts)%nat -> (grasp_cost < understand_cost parts)%nat). (* grasp before understanding *)
Proof.
  split; [ exact usmotrenie_is_a_that_channel | ].
  split; [ split; [ exact I | reflexivity ] | ].
  split; [ exact usmotrenie_unique_up | exact grasp_cheaper_than_understanding ].
Qed.

Print Assumptions insight_capstone.
Print Assumptions usmotrenie_is_a_that_channel.
Print Assumptions usmotrenie_resolves_riddle.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  12 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Усмотрение (insight/intuition) is the WHOLE-channel of knowledge-THAT —    *)
(*  the author's 2026-06-12 correction made a theorem (usmotrenie_is_a_that_   *)
(*  channel: NOT a presence-channel; presence = the meeting, not a channel).  *)
(*  знание-о has two channels (whole / details); усмотрение is the unique      *)
(*  UPWARD channel (usmotrenie_unique_up — closes the "forest for trees" of    *)
(*  «Глубина»).  The riddle resolves: GRASP is one act, UNDERSTANDING follows  *)
(*  the in-order ladder (usmotrenie_resolves_riddle, via                       *)
(*  KnowledgeDepth.tiers_mastered_in_order) — Order governs understanding, not *)
(*  grasping.  Intuition's three conditions = two depth limiters + the request *)
(*  (usmotrenie_needs_all_three, request_is_the_extra).  Last unit of the      *)
(*  Теория Знания branch; reuses KnowType (§5) and KnowledgeDepth.            *)
(* ========================================================================= *)
