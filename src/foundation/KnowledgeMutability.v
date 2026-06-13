(** * KnowledgeMutability.v — T-core: the knowable system A = invariant (+) variant,
      and the learnability split it FORCES (essence = a completed object / variant = a role-limit)

    Closes fork (3b) of the Theory-of-Knowledge development: "what governs A's change, and what does
    that imply for knowing A?"  The answer is read straight off Theory of Systems + E/R/R, with NO
    imported foreign theory (project rule: everything is derived ontologically).

    By A=A (L1) a system is itself THROUGH its critical-and-fixed core (the essence / invariant);
    formally, A=A is the CONSTANCY of the invariant component across stages.  Change lives in the
    NON-fixed part (elements within roles, non-critical roles) and is FIRED by external interaction
    (gate 3).  This file decomposes the observed system into two component-processes —
      inv_of : the invariant (essence-bearer),
      var_of : the variant (changeable manifestation)
    — and proves the split they force:

      * ESSENCE is knowledge-THAT: a fixed essence is a COMPLETED OBJECT (exists v, forall t) — one
        value at every stage; it transfers as a value (KnowledgeProcess.knowledge_that_transfers);
        its knowable is BOUNDED, so acquisition COMPLETES (KnowledgeGap, Species I).
      * VARIANT is knowledge-HOW: once it moves it is NOT a completed object (exists v, forall t
        FAILS), no finite record pins it (the project's diagonal, KnowledgeProcess), and an
        outrunning variant field DIVERGES (KnowledgeGap, Species II).
      * The STABILITY WINDOW W is DERIVED, not postulated: while no essence-change fires, A=A holds
        across the whole window (so the presence-deadline follows from WHEN a critical change fires).
      * ISOLATED A is FULLY learnable (fork a): no interaction => the variant is frozen => the whole
        system is one completed object; and INTERACTION is exactly what OPENS the variant — the same
        mechanism that grows the knowable field (gate 3) branches A (3b).  One cause, two effects.

    ============================== E/R/R разбор ==============================
    Rules (L5, the generative rule first):
      R-identity (L1, A=A): A is itself through its critical-fixed core => invariant_fixed
                 (inv_of constant); A=A across stages = same_system.
      R-change:  the non-fixed part changes by two rules — (i) element-within-role (essence-
                 PRESERVING: the local copy rule => essence_transfers) and (ii) role-change
                 (essence-BREAKING). Change is fired by interaction (variant_driven): no interaction
                 => frozen variant.
      R-order (L5 arrow): the witnessed variant record only appends (cited, KnowledgeProcess R5).
    Roles (L4):
      invariant = the essence-bearer (critical (^) fixed): carries knowledge-THAT (a completed value,
                 transfers). variant = the changeable manifestation (elements-in-roles + non-critical
                 roles): carries knowledge-HOW (a process, does not transfer). interaction = the
                 change-driver (= the growing-field driver of gate 3). window W = "how long the
                 essence holds" — sets the presence-deadline.
    Elements (L1+P4):
      two component-processes inv_of, var_of : GenProcess; the interaction signal iota : nat->bool; a
      stage t : nat.
    P4 diagnostic (could it be otherwise under the same rules?):
      NO. A=A forces the essence to be a SINGLE value at every stage => a completed object
      (exists v, forall t HOLDS) => Element-learnable / Species I (bounded field completes). A moving
      variant has NO single value (exists v, forall t FAILS) and no finite record pins it (the
      diagonal) => role-limit / Species II (diverges). The split is FORCED by the critical/non-
      critical structure, not chosen. The window W is DERIVED (= the no-essence-change span). Isolated
      A collapses the variant to a constant => the WHOLE A is learnable (fork a); so de-isolation
      (interaction) is exactly what opens the role-limit (gate 3 = engine of 3b).
    Honesty wall:
      "essence / identity / destruction" is the INTERPRETATION; the formal shadow is "the invariant
      component is constant under A=A" — machine-checked, no claim to the true суть. The anti-
      omniscience / Species I-II / transfer machinery is CITED (imported from KnowledgeProcess.v and
      KnowledgeGap.v), NOT re-proved. The genuinely new content is the SPLIT (A's own structure
      decomposed into that/how), the DERIVED window, and the interaction-unification (one cause grows
      the field AND branches A).

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia Bool.
Import ListNotations.
From ToS Require Import foundation.KnowledgeProcess.   (* GenProcess, observe, knowledge_how, knowledge_that_transfers, record_underdetermines_bool *)
From ToS Require Import foundation.KnowledgeGap.        (* knowledge_completes_when_bounded (Species I), deficit_diverges (Species II) *)

(* ===================================================================== *)
(*  PART I — the system A = invariant (+) variant; A=A as essence constancy *)
(* ===================================================================== *)

(** A=A (L1): the essence (critical (^) fixed core) is CONSTANT across stages — what makes every
    stage "still A". *)
Definition invariant_fixed {Inv : Type} (inv_of : GenProcess Inv) : Prop :=
  forall t, observe inv_of t = observe inv_of 0.

(** Identity preserved between two stages = same essence = the SAME system A. *)
Definition same_system {Inv : Type} (inv_of : GenProcess Inv) (t1 t2 : nat) : Prop :=
  observe inv_of t1 = observe inv_of t2.

Lemma same_system_refl : forall {Inv} (inv_of : GenProcess Inv) t, same_system inv_of t t.
Proof. intros. reflexivity. Qed.

(** ★ A=A throughout: a fixed essence makes every pair of stages the SAME system A. *)
Theorem invariant_fixed_is_one_system :
  forall {Inv} (inv_of : GenProcess Inv),
    invariant_fixed inv_of -> forall t1 t2, same_system inv_of t1 t2.
Proof.
  intros Inv inv_of H t1 t2. unfold same_system. rewrite (H t1), (H t2). reflexivity.
Qed.

(* ===================================================================== *)
(*  PART II — the two change-kinds: A1->A2 (variant) vs A->not-A (essence)  *)
(* ===================================================================== *)

(** A1 -> A2: the essence is unchanged, the variant differs — A PERSISTS (same A, new state). *)
Definition variant_change {Inv Var : Type}
  (inv_of : GenProcess Inv) (var_of : GenProcess Var) (t : nat) : Prop :=
  observe inv_of t = observe inv_of (S t) /\ observe var_of t <> observe var_of (S t).

(** A -> not-A: the essence itself changes — A is DESTROYED / replaced (a different system). *)
Definition essence_change {Inv : Type} (inv_of : GenProcess Inv) (t : nat) : Prop :=
  observe inv_of t <> observe inv_of (S t).

(** ★ Variant change keeps identity: A1->A2 is still A=A. *)
Theorem variant_change_keeps_identity :
  forall {Inv Var} (inv_of : GenProcess Inv) (var_of : GenProcess Var) t,
    variant_change inv_of var_of t -> same_system inv_of t (S t).
Proof. intros Inv Var inv_of var_of t [Hinv _]. exact Hinv. Qed.

(** ★ Essence change breaks identity: a critical change is the destruction of A (A->not-A). *)
Theorem essence_change_breaks_identity :
  forall {Inv} (inv_of : GenProcess Inv) t,
    essence_change inv_of t -> ~ same_system inv_of t (S t).
Proof. intros Inv inv_of t H. exact H. Qed.

(** The two change-kinds are mutually exclusive: a step cannot both keep and break A. *)
Theorem change_kinds_exclusive :
  forall {Inv Var} (inv_of : GenProcess Inv) (var_of : GenProcess Var) t,
    variant_change inv_of var_of t -> ~ essence_change inv_of t.
Proof. intros Inv Var inv_of var_of t [Hinv _] Hess. exact (Hess Hinv). Qed.

(* ===================================================================== *)
(*  PART III — the learnability split: essence = object, variant = process  *)
(* ===================================================================== *)

(** ★★ ESSENCE = knowledge-THAT: a fixed essence IS a completed object — a SINGLE value holds at
    every stage.  (exists v, forall t) HOLDS. *)
Theorem essence_known_as_object :
  forall {Inv} (inv_of : GenProcess Inv),
    invariant_fixed inv_of -> exists v, forall t, observe inv_of t = v.
Proof. intros Inv inv_of H. exists (observe inv_of 0). exact H. Qed.

(** ★★ VARIANT = knowledge-HOW: once it MOVES it is NOT a completed object — no single value fits
    every stage.  (exists v, forall t) FAILS. *)
Theorem variant_not_an_object :
  forall {Var} (var_of : GenProcess Var),
    (exists t, observe var_of (S t) <> observe var_of t) ->
    ~ exists v, forall t, observe var_of t = v.
Proof.
  intros Var var_of [t Ht] [v Hv]. apply Ht. rewrite (Hv (S t)), (Hv t). reflexivity.
Qed.

(** GENUINE BRIDGE (that): the change-rule "element-within-role" PRESERVES the essence — if each
    step keeps the invariant (the local copy rule), the essence value is the SAME at every stage.
    This is knowledge-THAT transferring, an instance of KnowledgeProcess.knowledge_that_transfers. *)
Theorem essence_transfers :
  forall {Inv} (inv_of : GenProcess Inv),
    (forall n, observe inv_of (S n) = observe inv_of n) ->
    forall t, observe inv_of t = observe inv_of 0.
Proof.
  intros Inv inv_of Hstep.
  apply (knowledge_that_transfers Inv inv_of (observe inv_of 0)).
  - exact Hstep.
  - reflexivity.
Qed.

(** GENUINE BRIDGE (how): the variant does NOT transfer — any finite record of it is
    underdetermined (the project's diagonal negb b <> b), an instance of
    KnowledgeProcess.record_underdetermines_bool. *)
Theorem variant_underdetermined :
  forall (var_of : GenProcess bool) (N : nat),
    exists var', knowledge_how var_of N = knowledge_how var' N
              /\ observe var_of N <> observe var' N.
Proof. intros var_of N. apply record_underdetermines_bool. Qed.

(** ★★ The essence/variant split IS the knowledge-THAT / knowledge-HOW split applied to the
    system's OWN structure: essence transfers as a completed value, variant does not. *)
Theorem essence_variant_is_that_how :
  (forall {Inv} (inv_of : GenProcess Inv), invariant_fixed inv_of ->
     exists v, forall t, observe inv_of t = v)
  /\ (forall (var_of : GenProcess bool) (N : nat),
        exists var', knowledge_how var_of N = knowledge_how var' N
                  /\ observe var_of N <> observe var' N).
Proof.
  split.
  - intros Inv inv_of H. exact (essence_known_as_object inv_of H).
  - exact variant_underdetermined.
Qed.

(* ===================================================================== *)
(*  PART IV — Species I / II inherited (KnowledgeGap): essence completes,   *)
(*            an open variant diverges                                      *)
(* ===================================================================== *)

(** GENUINE BRIDGE (Species I): the essence is a BOUNDED knowable (a single fixed fact of size c),
    so steady acquisition COMPLETES it by step c — KnowledgeGap.knowledge_completes_when_bounded.
    Knowledge of the essence is Element-learnable. *)
Theorem constant_essence_completes :
  forall (c : nat) (eknown : nat -> nat),
    (forall n, n <= eknown n) -> exists N, c <= eknown N.
Proof.
  intros c eknown Hs.
  assert (Hb : forall n, (fun _ : nat => c) n <= c) by (intro n; simpl; lia).
  destruct (knowledge_completes_when_bounded (fun _ : nat => c) eknown c Hb Hs) as [N HN].
  exists N. simpl in HN. exact HN.
Qed.

(** GENUINE BRIDGE (Species II): an outrunning variant field (acquisition r < growth g) DIVERGES —
    KnowledgeGap.deficit_diverges.  Knowledge of an open variant never completes. *)
Theorem variant_diverges :
  forall (vfield vknown : nat -> nat) (r g : nat),
    (forall n, vknown (S n) <= vknown n + r) ->
    (forall n, vfield n + g <= vfield (S n)) ->
    r < g -> vknown 0 <= vfield 0 ->
    forall B, exists n, vknown n + B < vfield n.
Proof. exact deficit_diverges. Qed.

(* ===================================================================== *)
(*  PART V — the DERIVED stability window W(A)                              *)
(* ===================================================================== *)

(** While no essence-change fires before W, the essence holds. *)
Definition stable_window {Inv : Type} (inv_of : GenProcess Inv) (W : nat) : Prop :=
  forall t, t < W -> observe inv_of t = observe inv_of (S t).

(** ★★ The stability window is DERIVED, not postulated: if no essence-change fires in [0,W], then
    A=A holds throughout — A stays the SAME system across the whole window.  The presence-deadline
    (gather knowledge of A's variant before A1->A2) follows from WHEN the first critical change
    fires. *)
Theorem stable_window_keeps_identity :
  forall {Inv} (inv_of : GenProcess Inv) (W : nat),
    stable_window inv_of W -> forall t, t <= W -> same_system inv_of 0 t.
Proof.
  intros Inv inv_of W Hwin t. induction t as [|t IH]; intro Ht.
  - apply same_system_refl.
  - assert (Hprev : same_system inv_of 0 t) by (apply IH; lia).
    unfold same_system in *. rewrite Hprev. apply Hwin. lia.
Qed.

(* ===================================================================== *)
(*  PART VI — isolated A is fully learnable (a); interaction opens A (3b)   *)
(* ===================================================================== *)

(** The variant changes ONLY when an external interaction fires (the change-rule is triggered by
    interaction — gate 3).  iota t = true: a significant interaction at stage t. *)
Definition variant_driven {Var : Type} (iota : nat -> bool) (var_of : GenProcess Var) : Prop :=
  forall t, iota t = false -> observe var_of (S t) = observe var_of t.

Definition isolated (iota : nat -> bool) : Prop := forall t, iota t = false.

(** ISOLATED A: with no interaction the variant is FROZEN — it never moves. *)
Theorem isolated_keeps_variant_fixed :
  forall {Var} (iota : nat -> bool) (var_of : GenProcess Var),
    variant_driven iota var_of -> isolated iota ->
    forall t, observe var_of t = observe var_of 0.
Proof.
  intros Var iota var_of Hdr Hiso t. induction t as [|t IH].
  - reflexivity.
  - rewrite (Hdr t (Hiso t)). exact IH.
Qed.

(** ★★ ISOLATED A IS FULLY LEARNABLE (fork a): if A is isolated and its essence is fixed, BOTH
    components are constant — the WHOLE system is a single completed object of knowledge. *)
Theorem isolated_system_fully_learnable :
  forall {Inv Var} (iota : nat -> bool) (inv_of : GenProcess Inv) (var_of : GenProcess Var),
    invariant_fixed inv_of -> variant_driven iota var_of -> isolated iota ->
    (exists vi, forall t, observe inv_of t = vi) /\ (exists vv, forall t, observe var_of t = vv).
Proof.
  intros Inv Var iota inv_of var_of Hinv Hdr Hiso. split.
  - exists (observe inv_of 0). exact Hinv.
  - exists (observe var_of 0). exact (isolated_keeps_variant_fixed iota var_of Hdr Hiso).
Qed.

(** ★★ INTERACTION OPENS THE VARIANT (gate 3 = the engine of mutability 3b): if the variant ever
    moves, an external interaction MUST have fired.  De-isolation is NECESSARY for A to have
    variants — the SAME interaction that grows the knowable field (gate 3) is what branches A (3b).
    One cause, two effects. *)
Theorem interaction_opens_the_variant :
  forall {Var} (iota : nat -> bool) (var_of : GenProcess Var),
    variant_driven iota var_of ->
    (exists t, observe var_of (S t) <> observe var_of t) ->
    exists t, iota t = true.
Proof.
  intros Var iota var_of Hdr [t Ht]. destruct (iota t) eqn:E.
  - exists t. exact E.
  - exfalso. apply Ht. exact (Hdr t E).
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ T-core: the knowable system A = invariant (+) variant.
    (1) A=A — a fixed essence makes every stage the same system;
    (2) essence = knowledge-THAT — a completed object (exists v, forall t);
    (3) variant = knowledge-HOW — never a completed object once it moves;
    (4) no finite record pins the variant (the diagonal);
    (5) interaction is exactly what opens the variant (gate 3 = engine of 3b). *)
Theorem knowledge_mutability_capstone :
  (forall (Inv : Type) (inv_of : GenProcess Inv), invariant_fixed inv_of ->
     forall t1 t2, same_system inv_of t1 t2)
  /\ (forall (Inv : Type) (inv_of : GenProcess Inv), invariant_fixed inv_of ->
        exists v, forall t, observe inv_of t = v)
  /\ (forall (var_of : GenProcess bool),
        (exists t, observe var_of (S t) <> observe var_of t) ->
        ~ exists v, forall t, observe var_of t = v)
  /\ (forall (var_of : GenProcess bool) (N : nat),
        exists var', knowledge_how var_of N = knowledge_how var' N
                  /\ observe var_of N <> observe var' N)
  /\ (forall (Var : Type) (iota : nat -> bool) (var_of : GenProcess Var),
        variant_driven iota var_of ->
        (exists t, observe var_of (S t) <> observe var_of t) ->
        exists t, iota t = true).
Proof.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros Inv inv_of H t1 t2. exact (invariant_fixed_is_one_system inv_of H t1 t2).
  - intros Inv inv_of H. exact (essence_known_as_object inv_of H).
  - intros var_of H. exact (variant_not_an_object var_of H).
  - exact variant_underdetermined.
  - intros Var iota var_of Hdr H. exact (interaction_opens_the_variant iota var_of Hdr H).
Qed.

Print Assumptions knowledge_mutability_capstone.
Print Assumptions essence_variant_is_that_how.
Print Assumptions stable_window_keeps_identity.
Print Assumptions isolated_system_fully_learnable.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  17 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The knowable system A = invariant (+) variant.  A=A = essence constancy   *)
(*  (invariant_fixed_is_one_system).  ESSENCE = knowledge-THAT: a completed   *)
(*  object (essence_known_as_object), transfers as a value (essence_transfers *)
(*  = knowledge_that_transfers), bounded field completes (constant_essence_   *)
(*  completes = Species I).  VARIANT = knowledge-HOW: not an object once it    *)
(*  moves (variant_not_an_object), no finite record pins it                   *)
(*  (variant_underdetermined = the diagonal), outrunning field diverges       *)
(*  (variant_diverges = Species II).  The stability window is DERIVED         *)
(*  (stable_window_keeps_identity).  Isolated A is fully learnable            *)
(*  (isolated_system_fully_learnable, fork a); interaction opens the variant  *)
(*  (interaction_opens_the_variant, gate 3 = engine of 3b).  Companion to     *)
(*  KnowledgeProcess.v / KnowledgeGap.v (F-39); machinery cited, not re-proved.*)
(* ========================================================================= *)
