(** * KnowledgeGap.v — F-39 companion: the зазор (§8) as a quantitative RACE with a phase transition

    KnowledgeProcess.v proved the QUALITATIVE anti-omniscience (forall-exists holds, exists-forall
    fails) and I flagged it honestly as "the unboundedness of nat in epistemic dress".  This file
    delivers the QUANTITATIVE strengthening the author asked for (derivation "Знание", §8 «Зазор,
    стремление, мудрость»): build the actual functions
        field n  = the knowable AVAILABLE about a system by step n     (R4: grows),
        known n  = the knowledge RECORDED by step n                    (the accumulator),
        r        = the MAX gained per step                             (R3: attention, one/step),
        gap n    = field n - known n                                  (the зазор; voля-в-действии)
    and race them.  The result is NOT automatic: there is a PHASE TRANSITION at the threshold
    g = r (field-growth rate vs acquisition rate).

      - SUBCRITICAL (bounded knowable, acquisition wins): knowledge COMPLETES — exists N, field N
        <= known N.  Knowledge-THAT is absolute BY ITS (finite) FACT (§5).  Species I.
      - CRITICAL/SUPERCRITICAL (g >= r): the deficit NEVER vanishes (known n <= field n always);
        for g > r it DIVERGES (forall B, exists n, known n + B < field n).  Knowledge-HOW of an
        unbounded knowable never completes (§7).  Species II.
      - RATE-INDEPENDENT (self-deepening, R4-depth + R5): when each new record opens at least as
        much new knowable as it closes, the gap is NON-DECREASING for ANY rate r — "догнать нельзя
        по построению" (§8) in its purest form.

    ============================== E/R/R разбор ==============================
    Elements: field, known : nat -> nat; the rates r (acquisition cap) and g (field-growth
              floor); gap n := field n - known n.
    Roles:    field = the chased (R4 growing knowable); known = the finite-speed chaser; r = the
              width-limiter (R3: one object per step); gap = воля-в-действии (§8, the engine).
    Rules:    R3 known (S n) <= known n + r;  R4 field n + g <= field (S n) (and, in depth, each
              new record opens >=1 new knowable);  R5 known monotone (= knowledge_irrevocable).
              The race: does known reach field?  Decided by the dial g vs r.
    P4 diagnostic: the CRITICAL THRESHOLD g = r.  Subcritical (bounded field) completes (знание-о,
              §5, Species I); supercritical (g >= r) the gap persists, (g > r) diverges (знание-как,
              §7, Species II).  Anti-omniscience is now a CONSEQUENCE of the field outrunning
              acquisition — not of bare nat-unboundedness.  Self-deepening makes it rate-independent.

    Cross-links (in prose, to keep this file stdlib-only and robust):
      - known monotone here = R5 = KnowledgeProcess.knowledge_irrevocable = L5_Arrow.cannot_unmake_distinction.
      - the Species I / Species II split is exactly foundation/RoleLimitSpecies.v
        (RegularLimit vs SingularLimit), here instantiated for KNOWLEDGE, with the critical
        dial g = r mirroring that file's critical ratio.
      - bounded field = знание-о of a completed fact (§5); unbounded self-deepening field =
        знание-как of an unbounded process (§7).

    Honest scope: every proof is elementary nat arithmetic (lia/nia) — not analysis.  The value is
    the upgrade QUALITATIVE -> QUANTITATIVE: a phase transition at g = r, the same Species I/II
    split as RoleLimitSpecies, realizing §8's "shag konechen (R3), pole rastyot (R4) — dognat'
    nel'zya po postroeniyu" as a counted race rather than a bare existential.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.

(* ===================================================================== *)
(*  PART I — the two linear envelopes of the race                         *)
(* ===================================================================== *)

(** R3: acquisition capped at r/step => known grows at most linearly (rate r). *)
Lemma known_le_linear : forall (known : nat -> nat) (r : nat),
  (forall n, known (S n) <= known n + r) ->
  forall n, known n <= known 0 + r * n.
Proof.
  intros known r Hacq n. induction n as [|n IH].
  - simpl. lia.
  - pose proof (Hacq n). rewrite Nat.mul_succ_r. lia.
Qed.

(** R4: field grows by at least g/step => field grows at least linearly (rate g). *)
Lemma field_ge_linear : forall (field : nat -> nat) (g : nat),
  (forall n, field n + g <= field (S n)) ->
  forall n, field 0 + g * n <= field n.
Proof.
  intros field g Hfg n. induction n as [|n IH].
  - simpl. lia.
  - pose proof (Hfg n). rewrite Nat.mul_succ_r. lia.
Qed.

(* ===================================================================== *)
(*  PART II — supercritical: the field outruns acquisition (g >= r)        *)
(* ===================================================================== *)

(** ★ The known NEVER overtakes a field that grows at least as fast (g >= r): there is a
    permanent deficit.  (If field 0 > known 0, the deficit is strictly positive forever.) *)
Theorem deficit_never_vanishes :
  forall (field known : nat -> nat) (r g : nat),
    (forall n, known (S n) <= known n + r) ->
    (forall n, field n + g <= field (S n)) ->
    r <= g -> known 0 <= field 0 ->
    forall n, known n <= field n.
Proof.
  intros field known r g Hacq Hfg Hrg H0 n.
  pose proof (known_le_linear known r Hacq n) as Hk.
  pose proof (field_ge_linear field g Hfg n) as Hf.
  assert (r * n <= g * n) by nia.
  lia.
Qed.

(** ★★ Strict outrun (g > r): the deficit DIVERGES — for any bound B some step's knowable
    exceeds the known by more than B.  Knowledge-HOW of an unbounded knowable never completes. *)
Theorem deficit_diverges :
  forall (field known : nat -> nat) (r g : nat),
    (forall n, known (S n) <= known n + r) ->
    (forall n, field n + g <= field (S n)) ->
    r < g -> known 0 <= field 0 ->
    forall B, exists n, known n + B < field n.
Proof.
  intros field known r g Hacq Hfg Hrg H0 B. exists (S B).
  pose proof (known_le_linear known r Hacq (S B)) as Hk.
  pose proof (field_ge_linear field g Hfg (S B)) as Hf.
  assert (r * S B + B < g * S B) by nia.
  lia.
Qed.

(** The зазор itself (with nat truncation): in the divergent regime it is unbounded. *)
Definition gap (field known : nat -> nat) (n : nat) : nat := field n - known n.

Corollary gap_unbounded :
  forall (field known : nat -> nat) (r g : nat),
    (forall n, known (S n) <= known n + r) ->
    (forall n, field n + g <= field (S n)) ->
    r < g -> known 0 <= field 0 ->
    forall B, exists n, B < gap field known n.
Proof.
  intros field known r g Hacq Hfg Hrg H0 B.
  destruct (deficit_diverges field known r g Hacq Hfg Hrg H0 B) as [n Hn].
  exists n. unfold gap. lia.
Qed.

(* ===================================================================== *)
(*  PART III — subcritical: a bounded knowable CAN be fully known (§5)     *)
(* ===================================================================== *)

(** ★ A FINITE knowable (field bounded by Fcap) with steady acquisition (>= 1 new/step) is
    COMPLETED: knowledge reaches the whole field.  This is знание-о absolute by its fact (§5),
    Species I — the field does NOT outrun, so the race is won. *)
Theorem knowledge_completes_when_bounded :
  forall (field known : nat -> nat) (Fcap : nat),
    (forall n, field n <= Fcap) ->     (* finite knowable: a completed fact *)
    (forall n, n <= known n) ->        (* steady acquisition: >= 1 new record per step *)
    exists N, field N <= known N.
Proof.
  intros field known Fcap Hb Hs. exists Fcap.
  pose proof (Hb Fcap). pose proof (Hs Fcap). lia.
Qed.

(* ===================================================================== *)
(*  PART IV — rate-INDEPENDENT: self-deepening keeps the gap from shrinking *)
(* ===================================================================== *)

(** ★★ The deepest form of §8 ("dognat' nel'zya po postroeniyu"): if every new record opens at
    least as much NEW knowable as it closes (R4 in depth: each element opens as a system), and
    knowledge is irrevocable (R5: known monotone), then the gap is NON-DECREASING — for ANY
    acquisition rate.  The frontier recedes by at least your step; the race cannot be won. *)
Theorem self_deepening_gap_nondecreasing :
  forall (field known : nat -> nat),
    (forall n, known n <= field n) ->                                 (* P4: cannot know beyond the knowable *)
    (forall n, known n <= known (S n)) ->                             (* R5: knowledge is irrevocable/monotone *)
    (forall n, field n + (known (S n) - known n) <= field (S n)) ->   (* R4-depth: each new record opens >=1 new knowable *)
    forall n, field 0 - known 0 <= field n - known n.
Proof.
  intros field known Hle Hmono Hdepth n. induction n as [|n IH].
  - lia.
  - pose proof (Hle n). pose proof (Hle (S n)).
    pose proof (Hmono n). pose proof (Hdepth n). lia.
Qed.

(* ===================================================================== *)
(*  CAPSTONES                                                              *)
(* ===================================================================== *)

(** ★★★ The phase transition at the threshold g = r. *)
Theorem knowledge_race_phase_transition :
  (* SUPERCRITICAL (field grows faster than acquisition): no completion, deficit diverges *)
  (forall (field known : nat -> nat) (r g : nat),
     (forall n, known (S n) <= known n + r) -> (forall n, field n + g <= field (S n)) ->
     r < g -> known 0 <= field 0 ->
     (forall n, known n <= field n) /\ (forall B, exists n, known n + B < field n))
  /\ (* SUBCRITICAL (bounded knowable): completion *)
  (forall (field known : nat -> nat) (Fcap : nat),
     (forall n, field n <= Fcap) -> (forall n, n <= known n) -> exists N, field N <= known N).
Proof.
  split.
  - intros field known r g Hacq Hfg Hrg H0. split.
    + apply (deficit_never_vanishes field known r g Hacq Hfg); [ lia | exact H0 ].
    + apply (deficit_diverges field known r g Hacq Hfg Hrg H0).
  - exact knowledge_completes_when_bounded.
Qed.

(** ★★★ The full §8 picture: rate-independent non-shrinking (self-deepening) + the g>r divergence
    (знание-как never completes) + the bounded completion (знание-о absolute by its fact). *)
Theorem knowledge_gap_synthesis :
  (forall (field known : nat -> nat),
     (forall n, known n <= field n) -> (forall n, known n <= known (S n)) ->
     (forall n, field n + (known (S n) - known n) <= field (S n)) ->
     forall n, field 0 - known 0 <= field n - known n)
  /\ (forall (field known : nat -> nat) (r g : nat),
     (forall n, known (S n) <= known n + r) -> (forall n, field n + g <= field (S n)) ->
     r < g -> known 0 <= field 0 -> forall B, exists n, known n + B < field n)
  /\ (forall (field known : nat -> nat) (Fcap : nat),
     (forall n, field n <= Fcap) -> (forall n, n <= known n) -> exists N, field N <= known N).
Proof.
  split; [ exact self_deepening_gap_nondecreasing | split ].
  - intros field known r g Hacq Hfg Hrg H0. apply (deficit_diverges field known r g Hacq Hfg Hrg H0).
  - exact knowledge_completes_when_bounded.
Qed.

Print Assumptions knowledge_race_phase_transition.
Print Assumptions knowledge_gap_synthesis.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The зазор (§8) as a counted RACE: known grows <= r/step (R3), field grows  *)
(*  >= g/step (R4); a PHASE TRANSITION at g = r decides it — bounded knowable  *)
(*  COMPLETES (знание-о, §5, Species I), g > r DIVERGES (знание-как, §7,       *)
(*  Species II), and self-deepening (R4-depth + R5) keeps the gap from         *)
(*  shrinking for ANY rate.  Anti-omniscience becomes a consequence of the     *)
(*  field outrunning acquisition, not of bare nat-unboundedness.  Quantitative *)
(*  companion to KnowledgeProcess.v (F-39); same Species I/II as RoleLimitSpecies. *)
(* ========================================================================= *)
