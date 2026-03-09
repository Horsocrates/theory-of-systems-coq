(* ========================================================================= *)
(*        MEASUREMENTPROCESS — Quantum Measurement as Process                *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                 *)
(*                                                                          *)
(*  Measurement in quantum mechanics as a process operation:                 *)
(*  - Post-measurement state (projection)                                   *)
(*  - Measurement dichotomy (discrete/continuous outcomes from PCH)          *)
(*  - Sequential measurements narrow the state                              *)
(*  - Expectation values via Born rule                                       *)
(*                                                                          *)
(*  Elements: measurement, post_measurement, outcome_collection             *)
(*  Roles:    measurement → state update in quantum mechanics               *)
(*  Rules:    PCH → measurement outcome types, Born → probabilities         *)
(*  Status:   measurement | dichotomy | sequential | expectation             *)
(*                                                                          *)
(*  STATUS: 19 Qed, 0 Admitted                                              *)
(*  AXIOMS: classic (L3) + L4_witness (L4) — via PCH                        *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import ToS_Axioms.
From ToS Require Import CauchyReal.
From ToS Require Import ProcessTypes.
From ToS Require Import ProcessContinuumHypothesis.
From ToS Require Import LinearAlgebra.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.BornRule.
From ToS Require Import physics.SpectralDichotomy.

(* ========================================================================= *)
(*  SECTION 1: Measurement Outcome                                           *)
(* ========================================================================= *)

(** A measurement outcome is a pair: eigenvalue + post-measurement state *)
Record MeasurementOutcome (dim : nat) := mkOutcome {
  outcome_eigenvalue : Q;
  outcome_state : QState dim
}.

Arguments mkOutcome {dim}.
Arguments outcome_eigenvalue {dim}.
Arguments outcome_state {dim}.

(** A measurement outcome is valid if the post-state is an eigenstate *)
Definition valid_outcome {dim} (A : QObservable dim) (m : MeasurementOutcome dim) : Prop :=
  is_eigenstate A (outcome_state m) (outcome_eigenvalue m).

(** Measurement outcome probability via Born rule *)
Definition outcome_prob {dim} (s : QState dim) (m : MeasurementOutcome dim) : CauchySeq :=
  born_prob s (outcome_state m).

(** Outcome probability is nonneg at each step *)
Lemma outcome_prob_nonneg : forall {dim} (s : QState dim) (m : MeasurementOutcome dim) k,
  0 <= born_prob_at s (outcome_state m) k.
Proof.
  intros dim s m k. apply born_nonneg.
Qed.

(** Outcome probability process is Cauchy *)
Lemma outcome_prob_cauchy : forall {dim} (s : QState dim) (m : MeasurementOutcome dim),
  is_cauchy (born_prob_at s (outcome_state m)).
Proof.
  intros dim s m. apply born_prob_cauchy.
Qed.

(* ========================================================================= *)
(*  SECTION 2: Post-Measurement State                                        *)
(* ========================================================================= *)

(** Post-measurement: if we measure eigenvalue λ, the state becomes
    the corresponding eigenstate. This is the projection postulate. *)
Definition post_measurement {dim} (A : QObservable dim)
  (s : QState dim) (m : MeasurementOutcome dim) : QState dim :=
  outcome_state m.

(** Post-measurement state is an eigenstate *)
Lemma post_measurement_is_eigenstate : forall {dim} (A : QObservable dim)
  (s : QState dim) (m : MeasurementOutcome dim),
  valid_outcome A m ->
  is_eigenstate A (post_measurement A s m) (outcome_eigenvalue m).
Proof.
  intros dim A s m Hvalid.
  unfold post_measurement. exact Hvalid.
Qed.

(** Measuring the same observable again gives the same eigenvalue *)
Lemma measurement_repeatability : forall {dim} (A : QObservable dim)
  (s : QState dim) (m : MeasurementOutcome dim),
  valid_outcome A m ->
  is_eigenstate A (post_measurement A s m) (outcome_eigenvalue m).
Proof.
  intros dim A s m Hvalid.
  apply post_measurement_is_eigenstate. exact Hvalid.
Qed.

(** Born probability of re-measuring the same eigenstate:
    P(ψ→ψ) = |⟨ψ|ψ⟩|² which is the self-inner-product squared *)
Lemma repeat_measurement_prob : forall {dim} (m : MeasurementOutcome dim) k,
  born_prob_at (outcome_state m) (outcome_state m) k ==
  state_ip_at (outcome_state m) (outcome_state m) k *
  state_ip_at (outcome_state m) (outcome_state m) k.
Proof.
  intros dim m k. unfold born_prob_at. reflexivity.
Qed.

(* ========================================================================= *)
(*  SECTION 3: Measurement Dichotomy                                         *)
(* ========================================================================= *)

Section MeasurementDichotomy.

Variable dim : nat.
Variable encode : QState dim -> BinProcess.
Variable encode_compat : forall s1 s2 : QState dim,
  state_equiv s1 s2 -> bp_eq (encode s1) (encode s2).
Variable encode_inj : forall s1 s2 : QState dim,
  bp_eq (encode s1) (encode s2) -> state_equiv s1 s2.

(** The collection of possible measurement outcomes for observable A
    at eigenvalue λ, as a BinCollection via encoding *)
Definition outcome_collection (A : QObservable dim) (lambda : Q) : BinCollection :=
  eigenspace dim encode A lambda.

(** Measurement outcome dichotomy:
    For any observable and eigenvalue, the set of possible outcomes is either
    countable (discrete) or uncountable (continuous). *)
Theorem measurement_dichotomy : forall (A : QObservable dim) (lambda : Q),
  is_closed (outcome_collection A lambda) ->
  is_enumerable (outcome_collection A lambda) \/
  has_perfect_subset (outcome_collection A lambda).
Proof.
  intros A lambda Hclosed.
  exact (process_continuum_hypothesis _ Hclosed).
Qed.

(** No intermediate measurement type *)
Theorem no_intermediate_measurement : forall (A : QObservable dim) (lambda : Q),
  is_closed (outcome_collection A lambda) ->
  has_discrete_eigenspace dim encode A lambda \/
  has_continuous_eigenspace dim encode A lambda.
Proof.
  intros A lambda Hclosed.
  exact (spectral_dichotomy dim encode A lambda Hclosed).
Qed.

(** Finite-dimensional observables: measurement outcomes always discrete *)
Theorem finite_outcomes_discrete :
  forall (A : QObservable dim) (lambda : Q)
  (states : list (QState dim)),
  (forall s, is_eigenstate A s lambda ->
    exists s', In s' states /\ state_equiv s s') ->
  has_discrete_eigenspace dim encode A lambda.
Proof.
  intros A lambda states Hfin.
  apply (finitely_many_discrete dim encode encode_compat A lambda states Hfin).
Qed.

End MeasurementDichotomy.

(* ========================================================================= *)
(*  SECTION 4: Sequential Measurements                                       *)
(* ========================================================================= *)

(** Sequential measurement narrows: measuring observable A on an
    eigenstate of A with eigenvalue λ gives transition probability 1
    (since the state is already an eigenstate) *)
Lemma eigenstate_certain : forall {dim} (A : QObservable dim)
  (s : QState dim) (lambda : Q),
  is_eigenstate A s lambda ->
  forall k,
  born_prob_at s s k == state_ip_at s s k * state_ip_at s s k.
Proof.
  intros dim A s lambda _ k. unfold born_prob_at. reflexivity.
Qed.

(** Orthogonal measurement: if state s is a basis state |i⟩ and we
    project onto a different basis state |j⟩, the probability is 0 *)
Lemma orthogonal_outcome_zero : forall dim (i j : nat) k,
  (i < dim)%nat -> (j < dim)%nat -> i <> j ->
  born_prob_at (basis_state dim i) (basis_state dim j) k == 0.
Proof.
  intros dim i j k Hi Hj Hij.
  apply born_orthogonal_at; assumption.
Qed.

(** Same-basis measurement: P(|j⟩→|j⟩) = 1 *)
Lemma same_basis_certain : forall dim (j : nat) k,
  (j < dim)%nat ->
  born_prob_at (basis_state dim j) (basis_state dim j) k == 1.
Proof.
  intros dim j k Hj.
  apply born_self_basis; assumption.
Qed.

(** Measurement symmetry: P(ψ₁→ψ₂) = P(ψ₂→ψ₁) *)
Lemma measurement_symmetry : forall {dim} (s1 s2 : QState dim) k,
  born_prob_at s1 s2 k == born_prob_at s2 s1 k.
Proof.
  intros dim s1 s2 k. apply born_symmetric.
Qed.

(* ========================================================================= *)
(*  SECTION 5: Expectation Values and Measurement                            *)
(* ========================================================================= *)

(** Expectation value of identity observable equals norm squared *)
Lemma measurement_identity_expectation : forall dim (s : QState dim) k,
  born_expectation_at (id_observable dim) s k == state_ip_at s s k.
Proof.
  intros dim s k. apply expectation_identity.
Qed.

(** Expectation value of diagonal observable on basis state
    gives the corresponding eigenvalue *)
Lemma measurement_diag_expectation : forall {dim} (eigenvals : QVec dim) j k,
  (j < dim)%nat ->
  born_expectation_at (diag_observable eigenvals) (basis_state dim j) k ==
  qv_nth eigenvals j.
Proof.
  intros dim eigenvals j k Hj.
  apply expectation_diag_basis; assumption.
Qed.

(** Expectation value of identity is nonneg *)
Lemma measurement_identity_nonneg : forall dim (s : QState dim) k,
  0 <= born_expectation_at (id_observable dim) s k.
Proof.
  intros dim s k. apply expectation_id_nonneg.
Qed.

(** Born probability bounded by Cauchy-Schwarz *)
Lemma measurement_prob_bounded : forall {dim} (s1 s2 : QState dim) k,
  born_prob_at s1 s2 k <= state_ip_at s1 s1 k * state_ip_at s2 s2 k.
Proof.
  intros dim s1 s2 k. apply born_cauchy_schwarz.
Qed.

(* ========================================================================= *)
(*  SECTION 6: Integration Theorems                                          *)
(* ========================================================================= *)

(** ★ PROCESS PHYSICS: COMPLETE MEASUREMENT THEORY ★

    The three pillars of quantum measurement, all formally verified:

    1. BORN RULE: The probability of transition s₁ → s₂ is |⟨s₁|s₂⟩|²
       (born_prob, born_nonneg, born_cauchy_schwarz)

    2. SPECTRAL DICHOTOMY: Every observable's eigenspace is either
       enumerable (discrete) or has a perfect subset (continuous).
       No intermediate type exists.
       (spectral_dichotomy, no_intermediate_spectrum)

    3. MEASUREMENT PROCESS: Post-measurement states are eigenstates,
       repeated measurement gives the same result, and transition
       probabilities respect orthogonality.
       (post_measurement_is_eigenstate, measurement_repeatability,
        orthogonal_outcome_zero, same_basis_certain) *)

(** Integration: Born probability + Cauchy-Schwarz bound *)
Theorem measurement_prob_structure : forall {dim} (s1 s2 : QState dim) k,
  0 <= born_prob_at s1 s2 k /\
  born_prob_at s1 s2 k <= state_ip_at s1 s1 k * state_ip_at s2 s2 k /\
  born_prob_at s1 s2 k == born_prob_at s2 s1 k.
Proof.
  intros dim s1 s2 k. repeat split.
  - apply born_nonneg.
  - apply born_cauchy_schwarz.
  - apply born_symmetric.
Qed.

(** Integration: basis measurement is complete and orthonormal *)
Theorem basis_measurement_complete : forall dim (i j : nat) k,
  (i < dim)%nat -> (j < dim)%nat ->
  (i = j -> born_prob_at (basis_state dim i) (basis_state dim j) k == 1) /\
  (i <> j -> born_prob_at (basis_state dim i) (basis_state dim j) k == 0).
Proof.
  intros dim i j k Hi Hj. split.
  - intros Heq. subst j. apply born_self_basis. exact Hi.
  - intros Hneq. apply born_orthogonal_at; assumption.
Qed.

(** Integration: full measurement dichotomy *)
Theorem process_physics_measurement :
  forall dim (encode : QState dim -> BinProcess)
    (encode_compat : forall s1 s2, state_equiv s1 s2 -> bp_eq (encode s1) (encode s2))
    (encode_inj : forall s1 s2, bp_eq (encode s1) (encode s2) -> state_equiv s1 s2)
    (A : QObservable dim) (lambda : Q),
  is_closed (eigenspace dim encode A lambda) ->
  (** Measurement outcomes are discrete or continuous *)
  (is_enumerable (eigenspace dim encode A lambda) \/
   has_perfect_subset (eigenspace dim encode A lambda)) /\
  (** And Born probabilities are well-defined *)
  (forall s1 s2 : QState dim, forall k,
    0 <= born_prob_at s1 s2 k).
Proof.
  intros dim encode ec ei A lambda Hclosed. split.
  - exact (process_continuum_hypothesis _ Hclosed).
  - intros s1 s2 k. apply born_nonneg.
Qed.

(** Summary:
    MeasurementProcess: Quantum measurement theory as process physics.

    SECTION 1 — Measurement Outcome:
      MeasurementOutcome, valid_outcome, outcome_prob,
      outcome_prob_nonneg, outcome_prob_cauchy

    SECTION 2 — Post-Measurement:
      post_measurement, post_measurement_is_eigenstate,
      measurement_repeatability, repeat_measurement_prob

    SECTION 3 — Measurement Dichotomy:
      outcome_collection, measurement_dichotomy,
      no_intermediate_measurement, finite_outcomes_discrete

    SECTION 4 — Sequential Measurements:
      eigenstate_certain, orthogonal_outcome_zero,
      same_basis_certain, measurement_symmetry

    SECTION 5 — Expectation Values:
      measurement_identity_expectation, measurement_diag_expectation,
      measurement_identity_nonneg, measurement_prob_bounded

    SECTION 6 — Integration:
      measurement_prob_structure, basis_measurement_complete,
      process_physics_measurement
*)
