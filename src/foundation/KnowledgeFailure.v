(** * KnowledgeFailure.v — T-typology: the FIVE structurally distinct modes in which knowing a
      system A can fail, each with its own cause and its own (ir)recoverability

    The grand synthesis of the Theory-of-Knowledge branch.  Across the nine prior files the branch
    derived several DIFFERENT ways knowledge falls short; scattered, they look alike ("you didn't
    learn it").  Here they are separated into five modes that differ in KIND — in what blocks them
    and in what (if anything) lifts the block:

      (1) BOTTLENECK   (soft, CAPACITY): effective depth = min(object, channel, threshold); the
                       binding (weakest) limiter caps the read.  RECOVERABLE: raise the binding
                       limiter to the object's depth and the read is full again (eff = obj).
                       [KnowledgeDepth.eff]
      (2) MISMATCH     (hard, TYPE/MODE): the ground dictates the mode; PRESENCE is had only through
                       the meeting, never through ANY information channel.  NO remedy within the
                       wrong mode — a type wall, not a capacity shortfall (no budget even appears).
                       [KnowledgeInsight.fulfills]
      (3) ROLE-LIMIT   (asymptotic, GROWTH): the knowable field outruns acquisition (growth g >
                       rate r); the deficit DIVERGES; no amount of TIME suffices — the field is
                       infinite.  [KnowledgeGap / KnowledgeMutability.variant_diverges, Species II]
      (4) DEADLINE     (temporal, FINITE): A changes (A1 -> A2) at the end of its stability window W;
                       if rate*W < amount you finish short AT THE DEADLINE — yet the amount IS
                       learnable given more time.  You ran out of WINDOW, not capacity.
                       [KnowledgeMutability.stable_window]
      (5) DESTRUCTION  (terminal, IDENTITY): the ESSENCE changes (A -> not-A); the source ceases and
                       every mode of knowing A ends.  [KnowledgeMutability.essence_change]

    The pairwise contrasts are the point: 1 vs 2 = recoverable vs categorical; 3 vs 4 = infinite
    field vs finite-but-too-late; 4 vs 5 = A persists vs A ceases.

    ============================== E/R/R разбор ==============================
    Rules (each mode = failure of a DIFFERENT rule):
      (1) R3 width/attention — the read is capped by the weakest of three limiters (eff = min).
      (2) the ground-dictates-the-mode rule — presence's ground is the meeting, not a channel;
          substituting a channel cannot fulfil it.
      (3) R4 field-growth outruns R3 acquisition — the chase diverges (g > r).
      (4) the window rule — A's non-fixed config holds only for W steps (A1 -> A2 then fires).
      (5) R-identity (A=A) — a critical/essence change breaks A=A: the system is no longer A.
    Roles (L4): bottleneck = capacity limiter; mismatch = type/mode wall; role-limit = infinite
      chase; deadline = finite clock; destruction = loss of the source.
    Elements (L1+P4): eff(obj,chan,thr); the modes and fulfills; field/known/r/g; rate/W/amount;
      inv_of and essence_change.
    P4 diagnostic (could the failure be otherwise — is there a remedy?):
      Each mode answers differently, and the answers are PROVED to differ: (1) raising the binding
      limiter restores eff = obj (recoverable); (2) presence stays unfulfilled through every channel
      (no remedy); (3) the deficit is unbounded (no time suffices); (4) the amount is still learnable
      with more steps (only the window failed); (5) A=A is broken (the system ceases).  So the five
      are genuinely distinct in kind.
    Honesty wall:
      This file CLASSIFIES; the load-bearing theorems are CITED (proved in KnowledgeDepth /
      KnowledgeInsight / KnowledgeGap / KnowledgeMutability), not re-proved.  Genuinely new here:
      the TAXONOMY (five distinct kinds with distinct remedies) and the mode-4 DEADLINE result
      (time-not-capacity, rate*W vs amount).  NOT claimed: that these are ALL possible failures
      (no completeness claim).  "Destruction / the source ceases" is the interpretation; the formal
      shadow is "A=A is broken at the step".

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia Bool.
Import ListNotations.
From ToS Require Import foundation.KnowledgeProcess.      (* GenProcess, observe *)
From ToS Require Import foundation.KnowledgeDepth.        (* eff, eff_le_obj, raise_nonbinding_obj_useless *)
From ToS Require Import foundation.KnowledgeInformation.  (* KnowType = KPresence | KThat | KHow *)
From ToS Require Import foundation.KnowledgeInsight.      (* Mode, is_channel, fulfills, usmotrenie_is_a_that_channel *)
From ToS Require Import foundation.KnowledgeMutability.   (* stable_window, essence_change, same_system, variant_change, variant_diverges *)

(* ===================================================================== *)
(*  MODE 1 — BOTTLENECK (soft, capacity): the weakest limiter caps; but   *)
(*           the wall LIFTS when the binding limiter is raised             *)
(* ===================================================================== *)

(** ★ MODE 1: effective depth is capped at the object's offered depth (and, more sharply, at the
    binding/weakest of the three limiters) — a CAPACITY shortfall. *)
Theorem mode1_bottleneck_caps : forall obj chan thr, eff obj chan thr <= obj.
Proof. exact eff_le_obj. Qed.

(** ★★ MODE 1 is RECOVERABLE: raise the limiters to the object's depth and the read is FULL again
    (eff = obj).  The soft wall lifts.  (Contrast mode 2, which never lifts.) *)
Theorem mode1_recoverable :
  forall obj chan thr, obj <= chan -> obj <= thr -> eff obj chan thr = obj.
Proof.
  intros obj chan thr Hc Ht. unfold eff.
  assert (Hm : obj <= Nat.min chan thr) by (apply Nat.min_glb; assumption).
  apply Nat.min_l. exact Hm.
Qed.

(** ★ MODE 1 diagnostic (the bottleneck): raising a NON-binding limiter (the object's offered
    depth) is useless — only raising the binding limiter helps. *)
Theorem mode1_wrong_lever_useless :
  forall obj obj' chan thr, Nat.min chan thr <= obj -> obj <= obj' ->
    eff obj' chan thr = eff obj chan thr.
Proof. exact raise_nonbinding_obj_useless. Qed.

(* ===================================================================== *)
(*  MODE 2 — MISMATCH (hard, type): the wrong mode never fulfils, ever     *)
(* ===================================================================== *)

(** ★★ MODE 2: PRESENCE cannot be had through ANY information channel — only through the meeting.
    No effort within the wrong mode helps; it is a TYPE wall, not a capacity shortfall (no budget
    parameter even appears).  (Contrast mode 1's graded, recoverable cap.) *)
Theorem mode2_mismatch_categorical :
  forall m, is_channel m = true -> ~ fulfills KPresence m.
Proof.
  intros m Hch Hf. destruct m.
  - simpl in Hch. discriminate.
  - simpl in Hf. exact Hf.
  - simpl in Hf. exact Hf.
  - simpl in Hf. exact Hf.
Qed.

(** MODE 2 witness (the author's correction): even усмотрение (a genuine channel) cannot deliver
    PRESENCE — KnowledgeInsight.usmotrenie_is_a_that_channel. *)
Theorem mode2_insight_not_presence : ~ fulfills KPresence Usmotrenie.
Proof. exact (proj2 usmotrenie_is_a_that_channel). Qed.

(** MODE 2 witness: knowledge-HOW is not had by insight — a process must be PASSED THROUGH, not
    grasped whole. *)
Theorem mode2_how_needs_passing : ~ fulfills KHow Usmotrenie.
Proof. simpl. intro H. exact H. Qed.

(* ===================================================================== *)
(*  MODE 3 — ROLE-LIMIT (asymptotic, growth): the field outruns the chase  *)
(* ===================================================================== *)

(** ★★ MODE 3: when the knowable field outruns acquisition (growth g > rate r), the deficit
    DIVERGES — knowledge never completes, and no amount of TIME suffices (the field is infinite).
    KnowledgeMutability.variant_diverges (= KnowledgeGap.deficit_diverges, Species II). *)
Theorem mode3_role_limit :
  forall (vfield vknown : nat -> nat) (r g : nat),
    (forall n, vknown (S n) <= vknown n + r) ->
    (forall n, vfield n + g <= vfield (S n)) ->
    r < g -> vknown 0 <= vfield 0 ->
    forall B, exists n, vknown n + B < vfield n.
Proof. exact variant_diverges. Qed.

(* ===================================================================== *)
(*  MODE 4 — DEADLINE (temporal, finite): the window closes before you do  *)
(* ===================================================================== *)

(** Steady acquisition: rate items per step. *)
Definition learned (rate n : nat) : nat := rate * n.

(** ★ MODE 4: within the stability window W you acquire learned rate W = rate*W; if rate*W >= amount
    you finish in time. *)
Theorem mode4_window_meets_deadline :
  forall rate W amount, amount <= rate * W -> amount <= learned rate W.
Proof. intros rate W amount H. unfold learned. exact H. Qed.

(** A FIXED amount is ALWAYS eventually learnable given enough steps (rate >= 1) — capacity is never
    the obstacle for a finite knowable. *)
Theorem fixed_amount_eventually_learnable :
  forall rate amount, 1 <= rate -> exists N, amount <= learned rate N.
Proof. intros rate amount Hr. exists amount. unfold learned. nia. Qed.

(** ★★ MODE 4 is TEMPORAL, not capacity: if the window is too short (rate*W < amount) you are short
    AT THE DEADLINE, YET the amount IS learnable given more time.  You ran out of WINDOW (A1->A2
    fires), not capacity.  (Contrast mode 3: there the field is infinite and no time suffices.) *)
Theorem mode4_deadline_is_time_not_capacity :
  forall rate W amount, 1 <= rate -> rate * W < amount ->
    learned rate W < amount /\ (exists N, amount <= learned rate N).
Proof.
  intros rate W amount Hr Hshort. split.
  - unfold learned. exact Hshort.
  - apply fixed_amount_eventually_learnable. exact Hr.
Qed.

(** The deadline W is the DERIVED stability window: while no essence-change fires, A=A holds across
    [0,W] (KnowledgeMutability.stable_window_keeps_identity) — so what is gathered within W is valid
    of one and the same A. *)
Theorem mode4_window_is_derived :
  forall {Inv} (inv_of : GenProcess Inv) (W : nat),
    stable_window inv_of W -> forall t, t <= W -> same_system inv_of 0 t.
Proof. intros Inv inv_of W. exact (stable_window_keeps_identity inv_of W). Qed.

(* ===================================================================== *)
(*  MODE 5 — DESTRUCTION (terminal, identity): the source ceases to be A   *)
(* ===================================================================== *)

(** ★★ MODE 5: if the ESSENCE changes, the system is no longer A — A is destroyed/replaced
    (A -> not-A), and every mode of knowing A ends because the source ceases.
    KnowledgeMutability.essence_change_breaks_identity. *)
Theorem mode5_destruction_terminal :
  forall {Inv} (inv_of : GenProcess Inv) t,
    essence_change inv_of t -> ~ same_system inv_of t (S t).
Proof. intros Inv inv_of t. exact (essence_change_breaks_identity inv_of t). Qed.

(** ★ MODES 4 vs 5 — the two faces of mutability: in MODE 4 A PERSISTS (a variant change keeps A=A)
    and only the window closed; in MODE 5 A CEASES (an essence change breaks A=A).  Same transition
    step, opposite consequence for the system's existence. *)
Theorem mode4_persists_mode5_ceases :
  forall {Inv Var} (inv_of : GenProcess Inv) (var_of : GenProcess Var) t,
    (variant_change inv_of var_of t -> same_system inv_of t (S t))
    /\ (essence_change inv_of t -> ~ same_system inv_of t (S t)).
Proof.
  intros Inv Var inv_of var_of t. split.
  - exact (variant_change_keeps_identity inv_of var_of t).
  - exact (essence_change_breaks_identity inv_of t).
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the five modes, distinct in cause and remedy                *)
(* ===================================================================== *)

(** ★★★ THE FIVE FAILURE MODES of knowing a system A — structurally DISTINCT:
    (1) BOTTLENECK — capacity; RECOVERABLE (raise the binding limiter to obj => eff = obj);
    (2) MISMATCH — wrong mode; categorical; NO remedy (presence not via any channel);
    (3) ROLE-LIMIT — field outruns acquisition; NEVER completes (no time suffices);
    (4) DEADLINE — window closes (A1->A2); capacity was fine (amount still learnable);
    (5) DESTRUCTION — essence changes (A->not-A); the source ceases.
    1 vs 2: recoverable vs categorical.  3 vs 4: infinite field vs finite-but-late.
    4 vs 5: A persists vs A ceases.  (No completeness claim — these are five distinct modes.) *)
Theorem five_failure_modes :
  (forall obj chan thr, obj <= chan -> obj <= thr -> eff obj chan thr = obj)
  /\ (forall m, is_channel m = true -> ~ fulfills KPresence m)
  /\ (forall (vfield vknown : nat -> nat) (r g : nat),
        (forall n, vknown (S n) <= vknown n + r) ->
        (forall n, vfield n + g <= vfield (S n)) ->
        r < g -> vknown 0 <= vfield 0 ->
        forall B, exists n, vknown n + B < vfield n)
  /\ (forall rate W amount, 1 <= rate -> rate * W < amount ->
        learned rate W < amount /\ (exists N, amount <= learned rate N))
  /\ (forall (Inv : Type) (inv_of : GenProcess Inv) t,
        essence_change inv_of t -> ~ same_system inv_of t (S t)).
Proof.
  split; [ exact mode1_recoverable | ].
  split; [ exact mode2_mismatch_categorical | ].
  split; [ exact mode3_role_limit | ].
  split.
  - exact mode4_deadline_is_time_not_capacity.
  - intros Inv inv_of t. exact (mode5_destruction_terminal inv_of t).
Qed.

Print Assumptions five_failure_modes.
Print Assumptions mode4_deadline_is_time_not_capacity.
Print Assumptions mode2_mismatch_categorical.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  14 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The five distinct failure modes of knowing a system A: BOTTLENECK         *)
(*  (mode1_recoverable — capacity, recoverable), MISMATCH                     *)
(*  (mode2_mismatch_categorical — type wall, no remedy), ROLE-LIMIT           *)
(*  (mode3_role_limit — infinite field, never completes), DEADLINE            *)
(*  (mode4_deadline_is_time_not_capacity — window closes, capacity fine),     *)
(*  DESTRUCTION (mode5_destruction_terminal — source ceases).  The pairwise   *)
(*  contrasts (1 recoverable vs 2 categorical; 3 infinite vs 4 finite-late;   *)
(*  4 persists vs 5 ceases) make the taxonomy genuine.  New here: the         *)
(*  taxonomy + the mode-4 deadline (time-not-capacity); the rest CITED from   *)
(*  KnowledgeDepth / KnowledgeInsight / KnowledgeGap / KnowledgeMutability.   *)
(*  No completeness claim.  Grand synthesis of the F-39 branch.              *)
(* ========================================================================= *)
