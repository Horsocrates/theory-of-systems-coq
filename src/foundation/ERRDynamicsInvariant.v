(** * ERRDynamicsInvariant.v — deepening the dynamics (thread ②, further): INVARIANT SETS and the
      SUB-DYNAMICS they carry (the dynamical analog of a subsystem).

    A subset of the state space closed under the step is INVARIANT; the dynamics RESTRICTS to it.

      ★ invariant f A — A is closed under the step (f maps A into A).  The orbit of any point in A
        STAYS in A (invariant_trajectory_stays): an invariant set is a confinement region.
      ★ Invariant sets form a LATTICE: the whole space (invariant_full) and the empty set
        (invariant_empty) are invariant, and invariance is closed under ∩ (invariant_inter) and ∪
        (invariant_union) — a sublattice of the powerset.
      ★ A fixed point gives the minimal invariant SINGLETON (equilibrium_invariant_singleton).
      ★ The forward-REACHABLE set {y : exists n, evolve f x n = y} is invariant (reachable_invariant),
        contains the start (reachable_contains_start), and is the SMALLEST invariant set containing the
        start (reachable_smallest) — the forward orbit.
      ★ SUB-DYNAMICS: f restricted to an invariant set A is a genuine endo of {x | A x}; it PROJECTS
        DOWN to f (restrict_commutes) — the sub-dynamics is literally f confined to A.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      a subset closed under the step (invariant, f(A)⊆A) is a SUB-DYNAMICS; the orbit never leaves it;
      invariant sets form a LATTICE; the forward-reachable set is the SMALLEST invariant set containing
      the start; restriction to an invariant set is a well-defined endo that projects down to f.
    Roles (L4): invariant (the closure predicate); restrict (the sub-dynamics); reachable (the forward
      orbit); the lattice operations (∩/∪/⊤/⊥).
    Elements (L1+P4): the states; subsets (predicates); the operator.
    P4 diagnostic (could it be otherwise?):
      many invariant sets exist (⊤, ⊥, singletons, reachable sets) — the orbit is CONFINED to whichever
      one holds the start; the smallest is the reachable set, the actual forward orbit (each stage
      finite/actual, P4).
    Honesty wall:
      subsets = predicates (Prop); invariance = FORWARD closure f(A)⊆A (not two-sided); the sub-dynamics
      is the restricted MAP on the subtype {x | A x} — NOT a full sub-FunctionalSystem (the constitution
      need not restrict to A), so we give the restricted map + restrict_commutes (it projects to f); the
      lattice is ∩/∪/⊤/⊥ (a sublattice of the powerset), completeness not claimed.  Reuses ERRDynamics
      (evolve / equilibrium).  0 axioms.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* err_map *)
From ToS Require Import foundation.ERRDynamics.       (* InsideOperator, evolve, equilibrium *)

Open Scope nat_scope.

(* ===================================================================== *)
(*  INVARIANT SETS — closed under the step                                 *)
(* ===================================================================== *)

(** A subset (predicate) A is INVARIANT if the step keeps A inside A. *)
Definition invariant {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (A : get_Elements S -> Prop) : Prop := forall x, A x -> A (err_map f x).

(** ★★ The orbit STAYS in an invariant set: a point in A never leaves A. *)
Lemma invariant_trajectory_stays : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (A : get_Elements S -> Prop),
  invariant f A -> forall x, A x -> forall n, A (evolve f x n).
Proof.
  intros L S f A Hinv x Hx n. induction n as [|k IH].
  - change (evolve f x 0) with x. exact Hx.
  - change (evolve f x (Datatypes.S k)) with (err_map f (evolve f x k)).
    apply Hinv. exact IH.
Qed.

(* ===================================================================== *)
(*  INVARIANT SETS FORM A LATTICE                                          *)
(* ===================================================================== *)

(** ★ The whole space is invariant (the top). *)
Lemma invariant_full : forall {L} {S : FunctionalSystem L} (f : InsideOperator S),
  invariant f (fun _ => True).
Proof. intros L S f x _. exact I. Qed.

(** ★ The empty set is invariant (the bottom, vacuously). *)
Lemma invariant_empty : forall {L} {S : FunctionalSystem L} (f : InsideOperator S),
  invariant f (fun _ => False).
Proof. intros L S f x H. exact H. Qed.

(** ★ Invariance is closed under intersection. *)
Lemma invariant_inter : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (A B : get_Elements S -> Prop),
  invariant f A -> invariant f B -> invariant f (fun x => A x /\ B x).
Proof. intros L S f A B HA HB x [Hxa Hxb]. split; [ apply HA | apply HB ]; assumption. Qed.

(** ★ Invariance is closed under union. *)
Lemma invariant_union : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (A B : get_Elements S -> Prop),
  invariant f A -> invariant f B -> invariant f (fun x => A x \/ B x).
Proof.
  intros L S f A B HA HB x [Hxa | Hxb]; [ left; apply HA | right; apply HB ]; assumption.
Qed.

(* ===================================================================== *)
(*  CONCRETE INVARIANT SETS                                                *)
(* ===================================================================== *)

(** ★★ A fixed point gives the minimal invariant SINGLETON {x*}. *)
Lemma equilibrium_invariant_singleton : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (xstar : get_Elements S),
  equilibrium f xstar -> invariant f (fun y => y = xstar).
Proof. intros L S f xstar Heq y Hy. unfold equilibrium in Heq. rewrite Hy. exact Heq. Qed.

(** The forward-reachable set: everything the dynamics reaches from x. *)
Definition reachable {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) : get_Elements S -> Prop := fun y => exists n, evolve f x n = y.

(** ★ The start is reachable (0 steps). *)
Lemma reachable_contains_start : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S), reachable f x x.
Proof. intros L S f x. exists 0. reflexivity. Qed.

(** ★★ The reachable set is invariant. *)
Lemma reachable_invariant : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S), invariant f (reachable f x).
Proof.
  intros L S f x y [n Hn]. exists (Datatypes.S n).
  change (evolve f x (Datatypes.S n)) with (err_map f (evolve f x n)). rewrite Hn. reflexivity.
Qed.

(** ★★ The reachable set is the SMALLEST invariant set containing x: any invariant set that holds x
    holds the whole forward orbit. *)
Lemma reachable_smallest : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) (A : get_Elements S -> Prop),
  invariant f A -> A x -> forall y, reachable f x y -> A y.
Proof.
  intros L S f x A Hinv Hx y [n Hn]. rewrite <- Hn.
  apply invariant_trajectory_stays; assumption.
Qed.

(* ===================================================================== *)
(*  THE SUB-DYNAMICS — f restricted to an invariant set                    *)
(* ===================================================================== *)

(** f restricted to an invariant set A is a well-defined endo of the subtype {x | A x}. *)
Definition restrict {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (A : get_Elements S -> Prop) (Hinv : invariant f A) (xa : {x | A x}) : {x | A x} :=
  exist _ (err_map f (proj1_sig xa)) (Hinv (proj1_sig xa) (proj2_sig xa)).

(** ★★ The sub-dynamics PROJECTS DOWN to f: the inclusion intertwines `restrict` with `f`.  So the
    sub-dynamics is literally f confined to A. *)
Lemma restrict_commutes : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (A : get_Elements S -> Prop) (Hinv : invariant f A) (xa : {x | A x}),
  proj1_sig (restrict f A Hinv xa) = err_map f (proj1_sig xa).
Proof. intros. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ INVARIANT SETS & SUB-DYNAMICS:
      (confinement)  the orbit stays in any invariant set holding the start;
      (lattice)      invariant sets are closed under ⊤, ∩, ∪;
      (singleton)    a fixed point is an invariant singleton;
      (reachable)    the forward orbit is the smallest invariant set containing the start;
      (sub-dynamics) f restricted to an invariant set projects down to f.
    A subset closed under the step is a sub-dynamics; the orbit is confined to it; invariant sets form
    a lattice; the reachable set is the least one; restriction is f confined. *)
Theorem err_dynamics_invariant :
  (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (A : get_Elements S -> Prop),
     invariant f A -> forall x, A x -> forall n, A (evolve f x n))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S), invariant f (fun _ => True))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (A B : get_Elements S -> Prop),
        invariant f A -> invariant f B -> invariant f (fun x => A x /\ B x))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (A B : get_Elements S -> Prop),
        invariant f A -> invariant f B -> invariant f (fun x => A x \/ B x))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (xstar : get_Elements S),
        equilibrium f xstar -> invariant f (fun y => y = xstar))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x : get_Elements S),
        reachable f x x
        /\ invariant f (reachable f x)
        /\ (forall A, invariant f A -> A x -> forall y, reachable f x y -> A y))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S)
            (A : get_Elements S -> Prop) (Hinv : invariant f A) (xa : {x | A x}),
        proj1_sig (restrict f A Hinv xa) = err_map f (proj1_sig xa)).
Proof.
  split; [ exact @invariant_trajectory_stays | ].
  split; [ exact @invariant_full | ].
  split; [ exact @invariant_inter | ].
  split; [ exact @invariant_union | ].
  split; [ exact @equilibrium_invariant_singleton | ].
  split; [ | exact @restrict_commutes ].
  intros L S f x. split; [ exact (reachable_contains_start f x) | ].
  split; [ exact (reachable_invariant f x) | exact (reachable_smallest f x) ].
Qed.

Print Assumptions err_dynamics_invariant.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Deepens thread ②: INVARIANT SETS and the SUB-DYNAMICS they carry.          *)
(*  invariant (closure under the step); invariant_trajectory_stays (orbit      *)
(*  confined).  LATTICE: invariant_full/_empty/_inter/_union.  CONCRETE:        *)
(*  equilibrium_invariant_singleton (fixed point = invariant singleton);        *)
(*  reachable (forward orbit), reachable_contains_start, reachable_invariant,   *)
(*  reachable_smallest (= least invariant set containing the start).            *)
(*  SUB-DYNAMICS: restrict (f on {x|A x}) + restrict_commutes (projects to f).  *)
(*  Capstone err_dynamics_invariant.  HONEST: subsets=predicates; invariance =  *)
(*  forward closure f(A)⊆A; sub-dynamics = restricted MAP (not a full sub-      *)
(*  FunctionalSystem — constitution need not restrict); lattice not claimed     *)
(*  complete.                                                                    *)
(* ========================================================================= *)
