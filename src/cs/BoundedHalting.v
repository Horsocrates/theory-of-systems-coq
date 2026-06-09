(* ========================================================================= *)
(*           BOUNDED HALTING IS L5-DECIDABLE                                *)
(*                                                                          *)
(*  THESIS:  For any deterministic machine (abstract step function +        *)
(*  initial state), the question "does this machine halt within N steps"   *)
(*  is L5-decidable via [mu_le] applied to the halted-state predicate.    *)
(*                                                                          *)
(*  THIS IS THE FORMAL BOUNDARY:                                            *)
(*                                                                          *)
(*    bounded_halting  →  L5-tractable (decidable, constructive witness)   *)
(*    unbounded_halting  →  role-limit (diagonal blocks decidability)     *)
(*                                                                          *)
(*  The L5 / μ-operator IS the boundary: bounded = inside, unbounded =     *)
(*  outside. This is the precise CONTENT of H1 (finitization boundary =    *)
(*  constructivity boundary) for the computability domain.                  *)
(*                                                                          *)
(*  KEY RESULTS:                                                            *)
(*    [halts_within_decidable]  — halting is bool-decidable                *)
(*    [first_halt_step_some_iff] — μ gives the smallest halt step         *)
(*    [first_halt_step_monotone] — found witness is stable across bounds  *)
(*    [bounded_halting_observable] — halting at any bound ⟺ halting        *)
(*                                  observable as a P4 process.            *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1):  State type, initial state q0.                        *)
(*    Roles (L1):     halted (None) vs running (Some _).                  *)
(*    Rules (L2):     step : State → option State (deterministic).        *)
(*    Order (L5):     smallest step number at which halting occurs.       *)
(*    Process (P4):   N-indexed family of bounded queries.                *)
(*                                                                          *)
(*  CONTENT: 0 Admitted, 0 axioms.                                          *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From ToS Require Import cs.MuRecursion.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: ABSTRACT DETERMINISTIC MACHINE                     *)
(* ========================================================================= *)

(** State after k steps starting from q. [None] indicates the machine
    halted at some step ≤ k. *)
Fixpoint state_at {State : Type} (step : State -> option State)
                  (q : State) (k : nat) : option State :=
  match k with
  | 0 => Some q
  | S k' =>
      match state_at step q k' with
      | None => None
      | Some q' => step q'
      end
  end.

(** Once halted, stays halted: None propagates forward. *)
Lemma state_at_halted_monotone : forall {State} (step : State -> option State) q k k',
  state_at step q k = None -> k <= k' -> state_at step q k' = None.
Proof.
  intros State step q k k' Heq Hle.
  induction Hle as [|k'' Hle' IH].
  - exact Heq.
  - cbn. rewrite IH. reflexivity.
Qed.

(** Contrapositive: if running at step k', running at all earlier steps. *)
Lemma state_at_running_backward : forall {State} (step : State -> option State) q k k' q',
  state_at step q k' = Some q' -> k <= k' ->
  exists q'', state_at step q k = Some q''.
Proof.
  intros State step q k k' q' Hsome Hle.
  destruct (state_at step q k) as [q''|] eqn:Hk.
  - exists q''. reflexivity.
  - exfalso.
    pose proof (state_at_halted_monotone step q k k' Hk Hle) as Hcontra.
    rewrite Hsome in Hcontra. discriminate.
Qed.

(* ========================================================================= *)
(*               PART II: BOUNDED HALTING IS DECIDABLE                      *)
(* ========================================================================= *)

(** halts_within step q N = true iff the machine halts within N steps. *)
Definition halts_within {State} (step : State -> option State)
                        (q : State) (N : nat) : bool :=
  match state_at step q N with
  | None => true
  | Some _ => false
  end.

(** halts_within is monotone in the bound. *)
Lemma halts_within_monotone : forall {State} (step : State -> option State) q N N',
  N <= N' -> halts_within step q N = true -> halts_within step q N' = true.
Proof.
  intros State step q N N' Hle Heq.
  unfold halts_within in *.
  destruct (state_at step q N) eqn:HN; [discriminate|].
  rewrite (state_at_halted_monotone step q N N' HN Hle). reflexivity.
Qed.

(** Decidability is immediate (already a bool function). *)
Theorem halts_within_decidable : forall {State} (step : State -> option State) q N,
  {halts_within step q N = true} + {halts_within step q N = false}.
Proof.
  intros. destruct (halts_within step q N); [left|right]; reflexivity.
Qed.

(* ========================================================================= *)
(*               PART III: FIRST HALT STEP VIA μ-OPERATOR                  *)
(* ========================================================================= *)

(** Auxiliary: is the option-state halted? *)
Definition is_halted_opt {State} (s : option State) : bool :=
  match s with None => true | Some _ => false end.

(** The smallest step k ≤ N at which the machine has halted (if any).
    This is the canonical L5/μ-application to bounded halting. *)
Definition first_halt_step {State} (step : State -> option State)
                           (q : State) (N : nat) : option nat :=
  mu_le (fun k => is_halted_opt (state_at step q k)) N.

(** first_halt_step characterizes the FIRST halt step. *)
Theorem first_halt_step_some_iff : forall {State} (step : State -> option State) q N k,
  first_halt_step step q N = Some k <->
  k <= N /\ state_at step q k = None /\
  (forall j, j < k -> exists q', state_at step q j = Some q').
Proof.
  intros State step q N k. unfold first_halt_step.
  rewrite mu_le_some_iff.
  split.
  - intros [Hle [Hp Hno]]. repeat split; try assumption.
    + unfold is_halted_opt in Hp. destruct (state_at step q k) eqn:Hs.
      * discriminate.
      * reflexivity.
    + intros j Hj. specialize (Hno j Hj).
      unfold is_halted_opt in Hno.
      destruct (state_at step q j) eqn:Hs.
      * exists s. reflexivity.
      * discriminate.
  - intros [Hle [HNone HSome]]. repeat split; try assumption.
    + unfold is_halted_opt. rewrite HNone. reflexivity.
    + intros j Hj. specialize (HSome j Hj).
      destruct HSome as [q' Hq'].
      unfold is_halted_opt. rewrite Hq'. reflexivity.
Qed.

(** first_halt_step returns None iff the machine never halts within N. *)
Theorem first_halt_step_none_iff : forall {State} (step : State -> option State) q N,
  first_halt_step step q N = None <->
  (forall k, k <= N -> exists q', state_at step q k = Some q').
Proof.
  intros State step q N. unfold first_halt_step.
  rewrite mu_le_none_iff.
  split.
  - intros Hall k Hk. specialize (Hall k Hk).
    unfold is_halted_opt in Hall.
    destruct (state_at step q k) eqn:Hs.
    + exists s. reflexivity.
    + discriminate.
  - intros Hall k Hk. specialize (Hall k Hk).
    destruct Hall as [q' Hq'].
    unfold is_halted_opt. rewrite Hq'. reflexivity.
Qed.

(** Monotonicity: a found first-halt-step is stable across larger bounds. *)
Theorem first_halt_step_monotone : forall {State} (step : State -> option State) q N N' k,
  N <= N' -> first_halt_step step q N = Some k ->
  first_halt_step step q N' = Some k.
Proof.
  intros State step q N N' k Hle Heq.
  unfold first_halt_step in *. eapply mu_le_monotone; eauto.
Qed.

(* ========================================================================= *)
(*               PART IV: halts_within ↔ first_halt_step                    *)
(* ========================================================================= *)

(** The bool predicate and the option predicate agree on existence. *)
Theorem halts_within_iff_first_halt_some : forall {State} (step : State -> option State) q N,
  halts_within step q N = true <-> exists k, first_halt_step step q N = Some k.
Proof.
  intros State step q N. split.
  - intros Heq. unfold halts_within in Heq.
    destruct (state_at step q N) eqn:HN; [discriminate|].
    (* state_at q N = None, so N itself is a halt witness. mu_process_finds_smallest gives smallest k ≤ N. *)
    pose proof (mu_process_finds_smallest
                  (fun k => is_halted_opt (state_at step q k)) N) as Hproc.
    assert (Hp : is_halted_opt (state_at step q N) = true).
    { unfold is_halted_opt. rewrite HN. reflexivity. }
    specialize (Hproc Hp).
    destruct Hproc as [k0 [_ [Hmu _]]].
    exists k0. exact Hmu.
  - intros [k Hk].
    apply first_halt_step_some_iff in Hk.
    destruct Hk as [Hle [HNone _]].
    pose proof (state_at_halted_monotone step q k N HNone Hle) as Hh.
    unfold halts_within. rewrite Hh. reflexivity.
Qed.

(** Dually: not halts_within ⟺ first_halt_step = None. *)
Theorem halts_within_false_iff_first_halt_none : forall {State} (step : State -> option State) q N,
  halts_within step q N = false <-> first_halt_step step q N = None.
Proof.
  intros State step q N. split.
  - intros Heq.
    destruct (first_halt_step step q N) eqn:Hf; [|reflexivity].
    exfalso.
    assert (Hin : exists k, first_halt_step step q N = Some k) by (exists n; exact Hf).
    apply halts_within_iff_first_halt_some in Hin. congruence.
  - intros Hnone.
    pose proof (first_halt_step_none_iff step q N) as [Hfwd _].
    specialize (Hfwd Hnone N (Nat.le_refl N)).
    destruct Hfwd as [q' Hq'].
    unfold halts_within. rewrite Hq'. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART V: BOUNDED HALTING AS P4-PROCESS                      *)
(* ========================================================================= *)

(** "Eventually halts" = exists N at which bounded halting succeeds.
    This is the P4-canonical presentation of unbounded halting:
    NOT a single decidable predicate, but a PROCESS indexed by N. *)
Definition eventually_halts {State} (step : State -> option State) (q : State) : Prop :=
  exists N, halts_within step q N = true.

(** Equivalently, exists a step at which the machine has halted. *)
Theorem eventually_halts_iff_some_halt_step : forall {State} (step : State -> option State) q,
  eventually_halts step q <-> exists k, state_at step q k = None.
Proof.
  intros State step q. split.
  - intros [N HN]. unfold halts_within in HN.
    destruct (state_at step q N) eqn:Hs; [discriminate|].
    exists N. exact Hs.
  - intros [k Hk]. exists k. unfold halts_within. rewrite Hk. reflexivity.
Qed.

(** OBSERVATIONAL CONSEQUENCE: existence of a halt step is reachable
    through the bounded halting process. NO actual ∞ required. *)
Theorem bounded_halting_observable : forall {State} (step : State -> option State) q,
  eventually_halts step q <->
  exists N k, first_halt_step step q N = Some k.
Proof.
  intros State step q. split.
  - intros [N HN]. apply halts_within_iff_first_halt_some in HN.
    destruct HN as [k Hk]. exists N, k. exact Hk.
  - intros [N [k Hk]].
    apply first_halt_step_some_iff in Hk.
    destruct Hk as [_ [HNone _]].
    apply eventually_halts_iff_some_halt_step. exists k. exact HNone.
Qed.

(* ========================================================================= *)
(*               PART VI: NUMERICAL VERIFICATION                            *)
(* ========================================================================= *)

(** Example: the always-halt machine (halts at step 1 always). *)
Definition immediate_halt_step (q : nat) : option nat := None.

Example immediate_halt_witness :
  first_halt_step immediate_halt_step 0 5 = Some 1.
Proof. reflexivity. Qed.

(** Example: the never-halt machine. *)
Definition never_halt_step (q : nat) : option nat := Some (S q).

Example never_halt_no_witness :
  first_halt_step never_halt_step 0 5 = None.
Proof. reflexivity. Qed.

(** Example: machine that halts at step 3 (counts down). *)
Definition countdown_step (q : nat) : option nat :=
  match q with 0 => None | S k => Some k end.

Example countdown_halt_at_3 :
  first_halt_step countdown_step 2 5 = Some 3.
Proof. reflexivity. Qed.

Example countdown_no_witness_low_bound :
  first_halt_step countdown_step 2 2 = None.
Proof. reflexivity. Qed.

Example countdown_witness_high_bound :
  first_halt_step countdown_step 2 10 = Some 3.
Proof. reflexivity. Qed.

(** Demonstration of monotonicity: same answer at any sufficient bound. *)
Example countdown_stable :
  forall N, N >= 3 -> first_halt_step countdown_step 2 N = Some 3.
Proof.
  intros N HN.
  apply (first_halt_step_monotone countdown_step 2 3 N 3 HN).
  reflexivity.
Qed.

(* ========================================================================= *)
(*               PART VII: ERR + PHILOSOPHICAL COMMENTARY                   *)
(* ========================================================================= *)

(**
  THE FORMAL BOUNDARY (precise statement of where L5/μ becomes role-limit):

  BOUNDED HALTING (here):
    halts_within step q N : bool
    first_halt_step step q N : option nat
    Both are TOTAL FUNCTIONS, computed in O(N · step_cost).
    Decidability is constructive: NO LEM, NO classical reasoning.

  UNBOUNDED HALTING (HaltingRoleLimit.v, CS branch):
    halts step q : Prop   (∃k, state_at step q k = None)
    NOT recursively enumerable in the negation.
    The classical diagonal argument (TM that asks "do I halt?" and does the
    opposite) makes this UNDECIDABLE — i.e., NOT L5-tractable.

  THE BOUNDARY IS:
    L5-applicable predicates over bounded N: decidable, constructive.
    L5-applicable over unbounded ℕ AS COMPLETED INFINITY: role-limit,
      requires classical choice principles, blocked by diagonals.

  The PROJECT'S ANSWER: don't take ℕ as a completed infinity. Take it as
  a PROCESS — that is, work with the family {first_halt_step step q N}_{N}
  rather than the limit. Inside each N, L5 succeeds. The "limit" is the
  observation pattern, not a completed set.

  CONSEQUENCE FOR THE THESIS:

  The H1 finitization boundary (constructivity boundary) is now
  formalized AT the L5/μ operator's domain:
    inside the boundary: L5 succeeds (bounded halting, this file).
    outside the boundary: role-limit (unbounded halting, future file).

  This file demonstrates the INSIDE direction in maximum generality:
  for ANY deterministic machine over ANY state type, bounded halting
  is L5-decidable. The state type can be arbitrary — including Turing
  machine tapes, recursive function configurations, lattice cellular
  automata, finite physical state spaces, etc. The result is uniformly
  L5/μ-tractable.

  WHY THIS MATTERS FOR THE BOOK:

  Volume II Part XV (Computability) gets its CENTRAL DEFINITION here:
  COMPUTABILITY = L5-tractability at bounded depth, with halting as
  P4-process. The "halting problem is undecidable" classical theorem
  is RELABELED: halting question over a completed infinity is role-limit;
  halting over P4-process is exactly L5/μ.
*)
