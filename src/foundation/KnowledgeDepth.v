(** * KnowledgeDepth.v — F-39 branch «Глубина»: the vertical of knowing, effective depth = min of
      three limiters (object / channel / threshold)

    Formalizes the derivation "Глубина" (Книги/Теория Знания/Глубина.md), the vertical companion of
    KnowledgeInformation.v's horizontal ladder.  The derivation (§8) explicitly invites this:
    "Формализация трёх ограничителей и эффективной глубины как минимума — естественное продолжение."

    THE THREE LIMITERS (§3) of read depth, all on the SAME vertical (one object's tower of tiers):
      obj  = the object's AVAILABLE depth   (how many tiers are presentable; finite at the moment, P4)
      chan = the CHANNEL depth              (the meeting cuts a layer: eye/screwdriver/X-ray)
      thr  = the witness's THRESHOLD        (capacity to assemble the read into a whole image)
    EFFECTIVE DEPTH = min(obj, chan, thr): you cannot know deeper than is presented, than the
    channel passes, or than the threshold holds — and it is useless to raise one limiter where the
    other two hold the minimum (the bottleneck / weakest link).

    STRUCTURAL CORE proved here (NOT the growth mechanisms — those are §4 prose):
      - eff = the greatest lower bound of the three (eff_is_min) and IS one of them (eff_is_a_limiter);
      - the bottleneck: raising a non-binding limiter is useless (raise_nonbinding_obj_useless);
      - monotonicity: effective depth never falls when a limiter rises (eff_mono);
      - bidirectional vertical: the threshold fails BOTH ways (gears-behind-clock = forest-for-trees);
      - the VERTICAL Law of Order (Rule 3): the threshold rises only IN ORDER, tiers are not skipped
        (a discrete intermediate-value property — the same no-skip shape as the horizontal ladder);
      - bridge: eff (3 limiters) <= min(obj, thr) (the 2-limiter bound KnowledgeInformation.readable
        used) — the channel is the third constraint that file omitted.

    ============================== E/R/R разбор ==============================
    Elements: tiers of the object (down = composition, up = the encompassing); the channel of the
              meeting; the witness's threshold; instruments; the read depth.
    Roles:    obj = what is OFFERED (presentable); chan = the CUT (which layer this meeting shows);
              thr = the CAPACITY (what assembles into a whole); effective depth = the MINIMUM of the
              three (the binding/weakest link).
    Rules:    (1) depth-at-the-moment is finite (P4);  (2) deepening = continued distinction (a tier
              is ACTUALIZED, not generated);  (3) tiers are mastered IN ORDER (understanding builds
              on the understood — the vertical Law of Order, no skipping);  (4) limiters grow
              independently — effective depth grows only where the MINIMUM grows;  (5) the vertical
              is BIDIRECTIONAL, the threshold fails both ways.
    P4 diagnostic: the "bottom" is not predetermined (obj is any nat, no maximal tier assumed); NO
              numerical depth measure ACROSS verticals — nat here is the within-one-vertical Level
              counter (§8), and only the partial order "deeper/shallower" along ONE vertical is used
              (tiers of one vertical are comparable; different verticals are not).  "Science deepens"
              is an ORGANIZATIONAL reading, NOT a theorem — only the structural facts are proved; the
              growth mechanisms (distinction / instrument / practice) stay in prose.

    Honest scope: elementary nat arithmetic (Nat.min / lia).  The value is the structural core of the
    vertical — the bottleneck (min), the no-skip order — exactly per §3–§5, with no forbidden claim
    (no cross-vertical scale, no predetermined bottom, no "science as theorem").

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.

(** Effective read depth = the minimum of the three limiters (§3). *)
Definition eff (obj chan thr : nat) : nat := Nat.min obj (Nat.min chan thr).

(* ===================================================================== *)
(*  PART I — effective depth is the greatest lower bound of the three      *)
(* ===================================================================== *)

Lemma eff_le_obj : forall obj chan thr, eff obj chan thr <= obj.
Proof. intros. unfold eff. apply Nat.le_min_l. Qed.

Lemma eff_le_chan : forall obj chan thr, eff obj chan thr <= chan.
Proof.
  intros. unfold eff.
  apply Nat.le_trans with (Nat.min chan thr); [ apply Nat.le_min_r | apply Nat.le_min_l ].
Qed.

Lemma eff_le_thr : forall obj chan thr, eff obj chan thr <= thr.
Proof.
  intros. unfold eff.
  apply Nat.le_trans with (Nat.min chan thr); [ apply Nat.le_min_r | apply Nat.le_min_r ].
Qed.

(** ★ eff is the GREATEST lower bound: anything within all three limiters is within eff.
    (You can know to depth d exactly when d is offered, passed, and held.) *)
Lemma eff_is_min : forall obj chan thr d,
  d <= obj -> d <= chan -> d <= thr -> d <= eff obj chan thr.
Proof.
  intros obj chan thr d Hobj Hchan Hthr. unfold eff.
  apply Nat.min_glb; [ exact Hobj | apply Nat.min_glb; [ exact Hchan | exact Hthr ] ].
Qed.

(** ★ eff IS one of the three — the binding (weakest) limiter is attained. *)
Lemma eff_is_a_limiter : forall obj chan thr,
  eff obj chan thr = obj \/ eff obj chan thr = chan \/ eff obj chan thr = thr.
Proof.
  intros obj chan thr. unfold eff.
  destruct (Nat.min_dec obj (Nat.min chan thr)) as [H|H]; rewrite H.
  - left. reflexivity.
  - destruct (Nat.min_dec chan thr) as [H2|H2]; rewrite H2.
    + right; left; reflexivity.
    + right; right; reflexivity.
Qed.

(* ===================================================================== *)
(*  PART II — the bottleneck (Rule 4): raise the binding limiter or nothing *)
(* ===================================================================== *)

(** ★★ The bottleneck (§3): raising a NON-binding limiter is useless.  If the channel-and-threshold
    pair already holds the minimum (min chan thr <= obj), then increasing the object's available
    depth does not change the effective depth at all. *)
Theorem raise_nonbinding_obj_useless : forall obj obj' chan thr,
  Nat.min chan thr <= obj -> obj <= obj' -> eff obj' chan thr = eff obj chan thr.
Proof.
  intros obj obj' chan thr Hbind Hle. unfold eff.
  assert (Hbind' : Nat.min chan thr <= obj') by (apply Nat.le_trans with obj; assumption).
  rewrite (Nat.min_r obj (Nat.min chan thr) Hbind).
  rewrite (Nat.min_r obj' (Nat.min chan thr) Hbind').
  reflexivity.
Qed.

(** ★ Monotonicity: effective depth never falls when a limiter rises (and rises only where the
    minimum rises — the positive face of Rule 4). *)
Theorem eff_mono : forall obj obj' chan chan' thr thr',
  obj <= obj' -> chan <= chan' -> thr <= thr' -> eff obj chan thr <= eff obj' chan' thr'.
Proof.
  intros obj obj' chan chan' thr thr' Ho Hc Ht. unfold eff. apply Nat.min_glb.
  - apply Nat.le_trans with obj; [ apply Nat.le_min_l | exact Ho ].
  - apply Nat.min_glb.
    + apply Nat.le_trans with chan; [ | exact Hc ].
      apply Nat.le_trans with (Nat.min chan thr); [ apply Nat.le_min_r | apply Nat.le_min_l ].
    + apply Nat.le_trans with thr; [ | exact Ht ].
      apply Nat.le_trans with (Nat.min chan thr); [ apply Nat.le_min_r | apply Nat.le_min_r ].
Qed.

(* ===================================================================== *)
(*  PART III — the bidirectional vertical (Rule 5)                         *)
(* ===================================================================== *)

(** the witness reaches a tier (down toward composition, OR up toward the encompassing) iff it is
    within the threshold — the SAME bound both ways. *)
Definition reaches_down (thr k : nat) : Prop := (k <= thr)%nat.
Definition reaches_up   (thr k : nat) : Prop := (k <= thr)%nat.

(** ★ The vertical is bidirectional: the threshold bounds the reach by the SAME amount up and down,
    and fails at the next tier in BOTH directions.  "Не видеть леса за деревьями" (up) is the same
    capacity-failure as "не видеть шестерёнок за часами" (down). *)
Lemma vertical_bidirectional : forall thr,
  (forall k, reaches_down thr k <-> reaches_up thr k)
  /\ ~ reaches_down thr (S thr)
  /\ ~ reaches_up thr (S thr).
Proof.
  intro thr. unfold reaches_down, reaches_up. split; [ | split ].
  - intro k. tauto.
  - lia.
  - lia.
Qed.

(* ===================================================================== *)
(*  PART IV — the vertical Law of Order (Rule 3): tiers are not skipped    *)
(* ===================================================================== *)

(** ★★ The vertical Law of Order: the threshold rises only IN ORDER.  If the threshold grows by at
    most one tier per practice-step (no jumps — "ярусы не перескакиваются"), starting from 0, then
    every tier below the current threshold was the threshold at some earlier step — no tier is
    skipped.  (A discrete intermediate-value property; the same no-skip shape as the horizontal
    ladder, stood vertical.) *)
Theorem tiers_mastered_in_order :
  forall (thr : nat -> nat),
    thr 0 = 0 ->
    (forall n, thr (S n) <= S (thr n)) ->            (* no jumps: at most one tier per step *)
    forall n k, k <= thr n -> exists m, (m <= n)%nat /\ thr m = k.
Proof.
  intros thr H0 Hstep n. induction n as [|n IH]; intros k Hk.
  - rewrite H0 in Hk. assert (k = 0) as Hk0 by lia. subst k.
    exists 0. split; [ lia | exact H0 ].
  - destruct (Nat.le_gt_cases k (thr n)) as [Hle | Hgt].
    + destruct (IH k Hle) as [m [Hm Hthm]]. exists m. split; [ lia | exact Hthm ].
    + pose proof (Hstep n) as Hs. exists (S n). split; [ lia | lia ].
Qed.

(* ===================================================================== *)
(*  PART V — bridge to KnowledgeInformation's 2-limiter read bound         *)
(* ===================================================================== *)

(** ★ KnowledgeInformation.readable used TWO limiters (object depth vs witness threshold).  The
    true effective depth with the CHANNEL is no greater: eff(obj,chan,thr) <= min(obj,thr).  The
    channel is the third constraint that file omitted — it can only lower the effective depth. *)
Lemma eff_refines_two_limiter : forall obj chan thr,
  eff obj chan thr <= Nat.min obj thr.
Proof.
  intros obj chan thr. unfold eff. apply Nat.min_glb.
  - apply Nat.le_min_l.
  - apply Nat.le_trans with (Nat.min chan thr); [ apply Nat.le_min_r | apply Nat.le_min_r ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The vertical of knowing: effective depth is the greatest lower bound of the three limiters
    (the binding/weakest link), raising a non-binding limiter is useless, and effective depth is
    monotone — rising only where the minimum rises. *)
Theorem effective_depth_capstone :
  (forall obj chan thr, eff obj chan thr <= obj /\ eff obj chan thr <= chan /\ eff obj chan thr <= thr)
  /\ (forall obj chan thr d, d <= obj -> d <= chan -> d <= thr -> d <= eff obj chan thr)
  /\ (forall obj obj' chan thr, Nat.min chan thr <= obj -> obj <= obj' -> eff obj' chan thr = eff obj chan thr)
  /\ (forall obj obj' chan chan' thr thr', obj <= obj' -> chan <= chan' -> thr <= thr' ->
        eff obj chan thr <= eff obj' chan' thr').
Proof.
  split; [ | split; [ | split ] ].
  - intros obj chan thr. split; [ apply eff_le_obj | split; [ apply eff_le_chan | apply eff_le_thr ] ].
  - exact eff_is_min.
  - exact raise_nonbinding_obj_useless.
  - exact eff_mono.
Qed.

Print Assumptions effective_depth_capstone.
Print Assumptions tiers_mastered_in_order.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The vertical of knowing (derivation «Глубина»): effective read depth =    *)
(*  min(object, channel, threshold) — the binding/weakest link (eff_is_min,   *)
(*  eff_is_a_limiter); raising a non-binding limiter is useless               *)
(*  (raise_nonbinding_obj_useless), depth is monotone (eff_mono); the         *)
(*  threshold fails both ways (vertical_bidirectional); and it rises only IN  *)
(*  ORDER — no tier skipped (tiers_mastered_in_order, the vertical Law of     *)
(*  Order).  eff <= min(obj,thr) refines KnowledgeInformation's 2-limiter     *)
(*  read bound by the channel.  No cross-vertical scale, no predetermined     *)
(*  bottom, no "science as theorem" (P4).  Vertical companion to the          *)
(*  horizontal data->information->knowledge ladder. *)
(* ========================================================================= *)
