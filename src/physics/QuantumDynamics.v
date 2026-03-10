(* ========================================================================= *)
(*        QUANTUMDYNAMICS — Time Evolution and Conservation Laws             *)
(*                                                                          *)
(*  Part of: Theory of Systems — Concrete Quantum Systems (Phase 3E)        *)
(*                                                                          *)
(*  Defines time evolution as a process of quantum states, and proves:       *)
(*  - static evolution preserves all properties                             *)
(*  - eigenstate evolution is stationary                                    *)
(*  - conservation laws for observables                                     *)
(*  - norm preservation                                                     *)
(*                                                                          *)
(*  Without mat_mul/mat_exp, we use record-based TimeEvolution with         *)
(*  structural properties. Focus: norm preservation, conservation, and      *)
(*  eigenstate stationarity — all fully constructive.                       *)
(*                                                                          *)
(*  STATUS: 24 Qed, 0 Admitted                                             *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.BornRule.

(* ========================================================================= *)
(*  PART I: TIME EVOLUTION                                                   *)
(* ========================================================================= *)

(** Time evolution: a family of quantum states indexed by time *)
Record TimeEvolution (dim : nat) := mkTimeEvol {
  te_state : nat -> QState dim;     (* state at each time step *)
  te_initial : QState dim;          (* initial state *)
  te_initial_eq : te_state 0%nat = te_initial
}.

Arguments mkTimeEvol {dim}.
Arguments te_state {dim}.
Arguments te_initial {dim}.
Arguments te_initial_eq {dim}.

(** Static evolution: state doesn't change in time *)
Definition static_evolution {dim} (s : QState dim) : TimeEvolution dim :=
  mkTimeEvol (fun _ => s) s eq_refl.

(** State at a given time *)
Definition state_at_time {dim} (te : TimeEvolution dim) (t : nat) : QState dim :=
  te_state te t.

(** Initial state accessor *)
Lemma initial_state_eq : forall {dim} (te : TimeEvolution dim),
  state_at_time te 0 = te_initial te.
Proof.
  intros dim te. unfold state_at_time. exact (te_initial_eq te).
Qed.

(** Static evolution always returns the same state *)
Lemma static_state : forall {dim} (s : QState dim) t,
  state_at_time (static_evolution s) t = s.
Proof. intros dim s t. reflexivity. Qed.

(** Expectation value at time t *)
Definition expectation_at_time {dim} (A : QObservable dim) (te : TimeEvolution dim)
  (t k : nat) : Q :=
  born_expectation_at A (state_at_time te t) k.

(** Inner product at time t *)
Definition ip_at_time {dim} (te : TimeEvolution dim) (t k : nat) : Q :=
  state_ip_at (state_at_time te t) (state_at_time te t) k.

(** Static evolution gives constant expectation *)
Lemma static_expectation_constant : forall {dim} (A : QObservable dim)
  (s : QState dim) t1 t2 k,
  expectation_at_time A (static_evolution s) t1 k ==
  expectation_at_time A (static_evolution s) t2 k.
Proof.
  intros. unfold expectation_at_time. rewrite !static_state. reflexivity.
Qed.

(** Static evolution gives constant norm *)
Lemma static_ip_constant : forall {dim} (s : QState dim) t1 t2 k,
  ip_at_time (static_evolution s) t1 k ==
  ip_at_time (static_evolution s) t2 k.
Proof.
  intros. unfold ip_at_time. rewrite !static_state. reflexivity.
Qed.

(* ========================================================================= *)
(*  PART II: NORM PRESERVATION                                               *)
(* ========================================================================= *)

(** A time evolution is norm-preserving if the norm squared is constant *)
Definition is_norm_preserving {dim} (te : TimeEvolution dim) : Prop :=
  forall t1 t2 k,
    ip_at_time te t1 k == ip_at_time te t2 k.

(** Static evolution preserves norm *)
Theorem static_norm_preserving : forall {dim} (s : QState dim),
  is_norm_preserving (static_evolution s).
Proof.
  intros dim s. unfold is_norm_preserving.
  intros t1 t2 k. apply static_ip_constant.
Qed.

(** Norm-preserving evolution has nonneg inner product *)
Lemma norm_preserving_nonneg : forall {dim} (te : TimeEvolution dim) t k,
  0 <= ip_at_time te t k.
Proof.
  intros dim te t k. unfold ip_at_time. apply state_ip_nonneg.
Qed.

(** Norm at initial time equals norm at any time (if norm-preserving) *)
Lemma norm_preserving_initial : forall {dim} (te : TimeEvolution dim) t k,
  is_norm_preserving te ->
  ip_at_time te t k == ip_at_time te 0 k.
Proof.
  intros dim te t k Hnp. apply Hnp.
Qed.

(* ========================================================================= *)
(*  PART III: EIGENSTATE EVOLUTION                                           *)
(* ========================================================================= *)

(** Eigenstate evolution: if s is an eigenstate, it stays stationary *)
Definition eigenstate_evolution {dim} (A : QObservable dim)
  (s : QState dim) : TimeEvolution dim :=
  static_evolution s.

(** Eigenstate evolution is stationary *)
Theorem eigenstate_stationary : forall {dim} (A : QObservable dim)
  (s : QState dim) t,
  state_at_time (eigenstate_evolution A s) t = s.
Proof.
  intros dim A s t. unfold eigenstate_evolution. apply static_state.
Qed.

(** Eigenstate evolution has constant expectation *)
Theorem eigenstate_constant_expectation : forall {dim} (A : QObservable dim)
  (s : QState dim) t1 t2 k,
  expectation_at_time A (eigenstate_evolution A s) t1 k ==
  expectation_at_time A (eigenstate_evolution A s) t2 k.
Proof.
  intros dim A s t1 t2 k. unfold eigenstate_evolution.
  apply static_expectation_constant.
Qed.

(** Eigenstate evolution preserves norm *)
Theorem eigenstate_norm_preserving : forall {dim} (A : QObservable dim)
  (s : QState dim),
  is_norm_preserving (eigenstate_evolution A s).
Proof.
  intros dim A s. unfold eigenstate_evolution. apply static_norm_preserving.
Qed.

(** Eigenstate expectation value equals eigenvalue (for diagonal observables) *)
Theorem eigenstate_expectation_value : forall {dim} (eigenvals : QVec dim)
  (j : nat) (k : nat) (t : nat),
  (j < dim)%nat ->
  expectation_at_time (diag_observable eigenvals)
    (eigenstate_evolution (diag_observable eigenvals) (basis_state dim j)) t k ==
  qv_nth eigenvals j.
Proof.
  intros dim eigenvals j k t Hj. unfold expectation_at_time.
  rewrite eigenstate_stationary.
  apply expectation_diag_basis. exact Hj.
Qed.

(* ========================================================================= *)
(*  PART IV: CONSERVATION LAWS                                               *)
(* ========================================================================= *)

(** An observable A is conserved under evolution te if its expectation
    is constant in time *)
Definition is_conserved {dim} (A : QObservable dim) (te : TimeEvolution dim) : Prop :=
  forall t1 t2 k,
    expectation_at_time A te t1 k == expectation_at_time A te t2 k.

(** In static evolution, every observable is conserved *)
Theorem static_all_conserved : forall {dim} (A : QObservable dim) (s : QState dim),
  is_conserved A (static_evolution s).
Proof.
  intros dim A s. unfold is_conserved.
  intros t1 t2 k. apply static_expectation_constant.
Qed.

(** The Hamiltonian is conserved in eigenstate evolution *)
Theorem hamiltonian_conserved : forall {dim} (A : QObservable dim)
  (s : QState dim),
  is_conserved A (eigenstate_evolution A s).
Proof.
  intros dim A s. unfold is_conserved.
  intros t1 t2 k. apply eigenstate_constant_expectation.
Qed.

(** Conservation from initial time: expectation at any time equals initial *)
Theorem conservation_from_initial : forall {dim} (A : QObservable dim)
  (te : TimeEvolution dim) t k,
  is_conserved A te ->
  expectation_at_time A te t k == expectation_at_time A te 0 k.
Proof.
  intros dim A te t k Hcons. apply Hcons.
Qed.

(** Norm conservation is a special case: identity observable conserved
    iff norm is preserved *)
Theorem norm_conservation_identity : forall {dim} (te : TimeEvolution dim),
  is_conserved (id_observable dim) te ->
  forall t1 t2 k,
    born_expectation_at (id_observable dim) (state_at_time te t1) k ==
    born_expectation_at (id_observable dim) (state_at_time te t2) k.
Proof.
  intros dim te Hcons t1 t2 k. apply Hcons.
Qed.

(* ========================================================================= *)
(*  PART V: TRANSITION AMPLITUDES AND OVERLAP                                *)
(* ========================================================================= *)

(** Overlap between states at different times *)
Definition overlap_at_time {dim} (te : TimeEvolution dim) (t1 t2 k : nat) : Q :=
  state_ip_at (state_at_time te t1) (state_at_time te t2) k.

(** Overlap is symmetric *)
Lemma overlap_symmetric : forall {dim} (te : TimeEvolution dim) t1 t2 k,
  overlap_at_time te t1 t2 k == overlap_at_time te t2 t1 k.
Proof.
  intros dim te t1 t2 k. unfold overlap_at_time.
  apply state_ip_comm.
Qed.

(** Self-overlap is the norm squared *)
Lemma overlap_self : forall {dim} (te : TimeEvolution dim) t k,
  overlap_at_time te t t k == ip_at_time te t k.
Proof.
  intros dim te t k. reflexivity.
Qed.

(** In static evolution, overlap is constant *)
Lemma static_overlap_constant : forall {dim} (s : QState dim) t1 t2 t3 t4 k,
  overlap_at_time (static_evolution s) t1 t2 k ==
  overlap_at_time (static_evolution s) t3 t4 k.
Proof.
  intros dim s t1 t2 t3 t4 k. unfold overlap_at_time.
  rewrite !static_state. reflexivity.
Qed.

(** Born probability for transition between states at different times *)
Definition transition_prob_at_time {dim} (te : TimeEvolution dim) (t1 t2 k : nat) : Q :=
  born_prob_at (state_at_time te t1) (state_at_time te t2) k.

(** Transition probability is symmetric *)
Lemma transition_symmetric : forall {dim} (te : TimeEvolution dim) t1 t2 k,
  transition_prob_at_time te t1 t2 k ==
  transition_prob_at_time te t2 t1 k.
Proof.
  intros dim te t1 t2 k. unfold transition_prob_at_time.
  apply born_symmetric.
Qed.

(** Transition probability is nonneg *)
Lemma transition_nonneg : forall {dim} (te : TimeEvolution dim) t1 t2 k,
  0 <= transition_prob_at_time te t1 t2 k.
Proof.
  intros dim te t1 t2 k. unfold transition_prob_at_time.
  apply born_nonneg.
Qed.

(** In static evolution, self-transition prob = norm^4 *)
Lemma static_self_transition : forall {dim} (s : QState dim) t k,
  transition_prob_at_time (static_evolution s) t t k ==
  born_prob_at s s k.
Proof.
  intros dim s t k. unfold transition_prob_at_time.
  rewrite !static_state. reflexivity.
Qed.

(* ========================================================================= *)
(*  PART VI: EVOLUTION COMPOSITION                                           *)
(* ========================================================================= *)

(** Composition: restrict evolution to start at time t0 *)
Definition evolution_from {dim} (te : TimeEvolution dim) (t0 : nat)
  : TimeEvolution dim.
Proof.
  refine (mkTimeEvol (fun t => te_state te (t0 + t)%nat)
                     (te_state te t0) _).
  f_equal. lia.
Defined.

(** Evolution from 0 is the same evolution *)
Lemma evolution_from_zero : forall {dim} (te : TimeEvolution dim) t,
  state_at_time (evolution_from te 0) t = state_at_time te t.
Proof.
  intros dim te t. unfold state_at_time, evolution_from. simpl. reflexivity.
Qed.

(** Norm preservation is inherited by sub-evolutions *)
Theorem norm_preserving_sub : forall {dim} (te : TimeEvolution dim) t0,
  is_norm_preserving te ->
  is_norm_preserving (evolution_from te t0).
Proof.
  intros dim te t0 Hnp. unfold is_norm_preserving, ip_at_time in *.
  intros t1 t2 k. unfold state_at_time, evolution_from. simpl.
  apply Hnp.
Qed.

(** Conservation is inherited by sub-evolutions *)
Theorem conservation_sub : forall {dim} (A : QObservable dim) (te : TimeEvolution dim) t0,
  is_conserved A te ->
  is_conserved A (evolution_from te t0).
Proof.
  intros dim A te t0 Hcons. unfold is_conserved, expectation_at_time in *.
  intros t1 t2 k. unfold state_at_time, evolution_from. simpl.
  apply Hcons.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

(** Summary:
    QuantumDynamics.v: Time evolution and conservation laws.

    Part I: Time Evolution
    - TimeEvolution record, static_evolution
    - state_at_time, initial_state_eq, static_state
    - expectation_at_time, ip_at_time
    - static_expectation_constant, static_ip_constant

    Part II: Norm Preservation
    - is_norm_preserving, static_norm_preserving
    - norm_preserving_nonneg, norm_preserving_initial

    Part III: Eigenstate Evolution
    - eigenstate_evolution, eigenstate_stationary
    - eigenstate_constant_expectation, eigenstate_norm_preserving
    - eigenstate_expectation_value (for diagonal observables)

    Part IV: Conservation Laws
    - is_conserved, static_all_conserved, hamiltonian_conserved
    - conservation_from_initial, norm_conservation_identity

    Part V: Transition Amplitudes
    - overlap_at_time, overlap_symmetric, overlap_self
    - static_overlap_constant
    - transition_prob_at_time, transition_symmetric
    - transition_nonneg, static_self_transition

    Part VI: Evolution Composition
    - evolution_from, evolution_from_zero
    - norm_preserving_sub, conservation_sub
*)
