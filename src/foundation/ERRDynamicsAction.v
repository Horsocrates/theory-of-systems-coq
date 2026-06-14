(** * ERRDynamicsAction.v — deepening the dynamics (thread ②, synthesis): TIME acts on a system as the
      monoid (nat, +, 0); a point's RETURN-TIMES form a SUBMONOID that classifies its dynamics.

    ERRDynamics/Arrow/GroupBasin/Conjugacy developed evolution, arrows, reversibility, conjugacy.  This
    file gives evolution its proper algebraic home and a new invariant:

      ★ MONOID ACTION.  Evolution is an action of the time-monoid (nat, +, 0): evolve f x 0 = x
        (action_zero) and evolve f x (m+n) = evolve f (evolve f x n) m (action_compose).  Time composes.

      ★ RETURN-TIME SUBMONOID.  The set of return-times of a point, {n : evolve f x n = x}, is a
        SUBMONOID of (nat, +): it contains 0 (return_times_zero) and is closed under + (closed).  Hence
        every multiple of a period is a return-time (return_times_multiples).

      ★ IT CLASSIFIES THE POINT.  equilibrium <=> the FULL submonoid (every time returns,
        equilibrium_all_return; return at time 1 already forces equilibrium, return_one_equilibrium).
        The three strata are realized:
          shift (aperiodic) — return-times = {0} only (shift_return_only_zero);
          flip (period 2)   — return-times contain 2*nat but NOT 1 (proper, nontrivial);
          collapse (equilibrium) — return-times = ALL of nat.

      ★ NATURAL.  The action is equivariant under conjugacy (conjugacy_evolve, reused): a relabeling
        intertwines the whole action.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      evolution is a MONOID ACTION of time (nat,+,0); the return-times of a point form a SUBMONOID
      (contain 0, closed under +); WHICH submonoid classifies the point — {0} (aperiodic) < p*nat
      (period p) < nat (equilibrium); the action is NATURAL (equivariant under conjugacy).
    Roles (L4): evolve (the action); return_times (the submonoid); shift/flip/collapse (the three
      strata); conjugacy_evolve (naturality).
    Elements (L1+P4): time (nat); the states; the operator.
    P4 diagnostic (could it be otherwise?):
      the submonoid laws (0 + closure) are FORCED by the action laws; but WHICH submonoid a point has
      is contingent on its dynamics — {0}, p*nat, and nat are ALL realized (shift/flip/collapse), so
      the classification is genuine, not collapsed to one.
    Honesty wall:
      the action is the discrete MONOID (nat,+) — NOT a group (no negative time unless reversible, cf.
      ERRDynamicsGroupBasin); return-times is a SUBMONOID (0 + closure); for flip we show it contains
      2*nat and excludes 1 (proper, nontrivial) WITHOUT claiming it equals 2*nat exactly; naturality =
      conjugacy_evolve (reused).  Synthesizes thread ②.  0 axioms.

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.       (* err_map *)
From ToS Require Import foundation.ERRDynamics.           (* evolve, iterate, equilibrium, equilibrium_stays, collapse *)
From ToS Require Import foundation.ERRDynamicsArrow.      (* flip, flip_period2 *)
From ToS Require Import foundation.ERRDynamicsGroupBasin. (* shift, shift_aperiodic *)
From ToS Require Import foundation.ERRDynamicsConjugacy.  (* conjugacy, conjugacy_evolve, collapse_has_fixed_point *)
From Stdlib Require Import ZArith Lia.

Open Scope nat_scope.

(* ===================================================================== *)
(*  EVOLUTION IS A MONOID ACTION OF TIME (nat, +, 0)                       *)
(* ===================================================================== *)

(** Time composes: evolving (m+n) steps = evolving n then m. *)
Lemma evolve_add : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) (m n : nat),
  evolve f x (m + n) = evolve f (evolve f x n) m.
Proof.
  intros L S f x m n. induction m as [|k IH].
  - reflexivity.
  - change (evolve f x (Datatypes.S k + n)) with (err_map f (evolve f x (k + n))).
    change (evolve f (evolve f x n) (Datatypes.S k)) with (err_map f (evolve f (evolve f x n) k)).
    rewrite IH. reflexivity.
Qed.

(** ★ action of the identity element: 0 steps do nothing. *)
Lemma action_zero : forall {L} {S : FunctionalSystem L} (f : InsideOperator S) (x : get_Elements S),
  evolve f x 0 = x.
Proof. reflexivity. Qed.

(** ★★ action compatibility (the monoid law): evolve respects +. *)
Lemma action_compose : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) (m n : nat),
  evolve f x (m + n) = evolve f (evolve f x n) m.
Proof. intros. apply evolve_add. Qed.

(* ===================================================================== *)
(*  THE RETURN-TIME SUBMONOID                                              *)
(* ===================================================================== *)

(** The return-times of a point: the times at which the evolution comes back to x. *)
Definition return_times {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) (n : nat) : Prop := evolve f x n = x.

(** ★ 0 is a return-time (the submonoid contains the identity). *)
Lemma return_times_zero : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S), return_times f x 0.
Proof. intros. unfold return_times. reflexivity. Qed.

(** ★★ return-times are closed under + (the submonoid law). *)
Lemma return_times_closed : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) (m n : nat),
  return_times f x m -> return_times f x n -> return_times f x (m + n).
Proof.
  intros L S f x m n Hm Hn. unfold return_times in *.
  rewrite evolve_add, Hn. exact Hm.
Qed.

(** ★★ Every multiple of a return-time is a return-time (from the submonoid laws). *)
Lemma return_times_multiples : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) (p : nat),
  return_times f x p -> forall k, return_times f x (k * p).
Proof.
  intros L S f x p Hp k. induction k as [|k IH].
  - simpl. apply return_times_zero.
  - replace (Datatypes.S k * p) with (p + k * p) by lia.
    apply return_times_closed; [ exact Hp | exact IH ].
Qed.

(* ===================================================================== *)
(*  THE SUBMONOID CLASSIFIES THE POINT                                     *)
(* ===================================================================== *)

(** ★ Return at time 1 already forces an equilibrium. *)
Lemma return_one_equilibrium : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S), return_times f x 1 -> equilibrium f x.
Proof.
  intros L S f x H. unfold return_times in H. unfold equilibrium.
  change (evolve f x 1) with (err_map f x) in H. exact H.
Qed.

(** ★ An equilibrium has the FULL submonoid: every time is a return-time. *)
Lemma equilibrium_all_return : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S), equilibrium f x -> forall n, return_times f x n.
Proof.
  intros L S f x Heq n. unfold return_times. apply equilibrium_stays. exact Heq.
Qed.

(** ★★ shift (aperiodic) — the TRIVIAL submonoid: only 0 returns. *)
Lemma shift_return_only_zero : forall (x0 : Z) n, return_times ERRDynamicsGroupBasin.shift x0 n -> n = 0.
Proof.
  intros x0 n H. destruct n as [|k]; [ reflexivity | ].
  exfalso. apply (shift_aperiodic x0 (Datatypes.S k)); [ lia | exact H ].
Qed.

(** ★★ flip (period 2) — a PROPER NONTRIVIAL submonoid: contains 2*nat ... *)
Lemma flip_return_even : forall k, return_times flip true (k * 2).
Proof. apply return_times_multiples. unfold return_times. apply flip_period2. Qed.

(** ... but NOT 1. *)
Lemma flip_not_return_one : ~ return_times flip true 1.
Proof. unfold return_times. intro H. cbn [evolve iterate err_map] in H. discriminate H. Qed.

(** ★★ collapse (equilibrium) — the FULL submonoid: all times return. *)
Lemma collapse_return_all : forall n, return_times collapse true n.
Proof. apply equilibrium_all_return. exact collapse_has_fixed_point. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE TIME-MONOID ACTION:
      (action)      evolution is a monoid action of (nat,+,0): evolve_zero + evolve respects +;
      (submonoid)   return-times contain 0 and are closed under + (a submonoid of (nat,+));
      (classifies)  shift = {0} (aperiodic), flip ⊇ 2*nat but ∌ 1 (period 2), collapse = nat (equil.);
      (natural)     the action is equivariant under conjugacy.
    Time acts as a monoid; the return-time submonoid of a point classifies its dynamics; the action is
    natural. *)
Theorem err_dynamics_action :
  (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x : get_Elements S),
     evolve f x 0 = x)
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x : get_Elements S) (m n : nat),
        evolve f x (m + n) = evolve f (evolve f x n) m)
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x : get_Elements S),
        return_times f x 0)
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x : get_Elements S) (m n : nat),
        return_times f x m -> return_times f x n -> return_times f x (m + n))
  /\ ((forall (x0 : Z) n, return_times ERRDynamicsGroupBasin.shift x0 n -> n = 0)
      /\ (forall k, return_times flip true (k * 2))
      /\ (~ return_times flip true 1)
      /\ (forall n, return_times collapse true n))
  /\ (forall (L : Level) (S S' : FunctionalSystem L)
            (phi : get_Elements S -> get_Elements S') (psi : get_Elements S' -> get_Elements S)
            (f : InsideOperator S) (f' : InsideOperator S'),
        conjugacy phi psi f f' -> forall n x, phi (evolve f x n) = evolve f' (phi x) n).
Proof.
  split; [ exact @action_zero | ].
  split; [ exact @action_compose | ].
  split; [ exact @return_times_zero | ].
  split; [ exact @return_times_closed | ].
  split; [ split; [ exact shift_return_only_zero
                  | split; [ exact flip_return_even
                           | split; [ exact flip_not_return_one | exact collapse_return_all ] ] ] | ].
  exact @conjugacy_evolve.
Qed.

Print Assumptions err_dynamics_action.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  13 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Synthesis of thread ②: TIME acts on a system as the monoid (nat,+,0).      *)
(*  evolve_add / action_zero / action_compose (the monoid action laws).        *)
(*  return_times (the return-time set), return_times_zero + return_times_closed *)
(*  (it is a SUBMONOID), return_times_multiples (every multiple of a period).   *)
(*  CLASSIFICATION: return_one_equilibrium + equilibrium_all_return (equilibrium *)
(*  = full submonoid); shift_return_only_zero ({0}, aperiodic), flip_return_even *)
(*  + flip_not_return_one (⊇2*nat, ∌1; period 2), collapse_return_all (nat;      *)
(*  equilibrium).  Naturality = conjugacy_evolve (reused).  Capstone             *)
(*  err_dynamics_action.  HONEST: discrete monoid (not a group — cf. GroupBasin);*)
(*  return-times = submonoid (0+closure), flip shown proper-nontrivial not       *)
(*  exactly 2*nat; naturality reused from ERRDynamicsConjugacy.                  *)
(* ========================================================================= *)
