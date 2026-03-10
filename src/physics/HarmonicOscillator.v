(* ========================================================================= *)
(*        HARMONICOSCILLATOR — Quantum Harmonic Oscillator                  *)
(*                                                                          *)
(*  Part of: Theory of Systems — Concrete Quantum Systems (Phase 3E)        *)
(*                                                                          *)
(*  Defines the quantum harmonic oscillator with N-level truncation:        *)
(*  energy levels E_n = n + 1/2, equispacing, eigenstates, Born             *)
(*  probabilities for superpositions, and expectation values.               *)
(*                                                                          *)
(*  KEY RESULTS:                                                            *)
(*  - ho_level_spacing: E(n+1) - E(n) = 1 (equispaced)                    *)
(*  - ho_superposition_ground_prob: P(|0⟩ → |+⟩) = 1/2                   *)
(*  - ho_superposition_expectation: ⟨H⟩ = E0 + E1                        *)
(*                                                                          *)
(*  STATUS: 35 Qed, 0 Admitted                                             *)
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
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.BornRule.
From ToS Require Import physics.Qubit.

(* ========================================================================= *)
(*  PART I: HARMONIC OSCILLATOR DEFINITION                                  *)
(* ========================================================================= *)

(** Energy of the n-th level: E_n = n + 1/2 *)
Definition ho_energy (n : nat) : Q := (1#2) + inject_Z (Z.of_nat n).

(** Eigenvalue vector for N-level truncation *)
Definition ho_eigenvals (N : nat) : QVec N :=
  mkQVec (map ho_energy (seq 0 N))
    (eq_trans (map_length ho_energy (seq 0 N)) (seq_length N 0)).

(** Hamiltonian = diagonal observable with ho_eigenvals *)
Definition ho_hamiltonian (N : nat) : QObservable N := diag_observable (ho_eigenvals N).

(** Energy eigenstate |n⟩ = basis_state N n *)
Definition energy_state (N n : nat) : QState N := basis_state N n.

(** Eigenvalue access: the j-th eigenvalue is ho_energy j *)
Lemma ho_eigenval_access : forall N j, (j < N)%nat ->
  qv_nth (ho_eigenvals N) j == ho_energy j.
Proof.
  intros N j Hj. unfold qv_nth, ho_eigenvals. simpl.
  rewrite (nth_map_general ho_energy (seq 0 N) 0%nat 0 j);
    [| rewrite seq_length; exact Hj].
  rewrite seq_nth; [| exact Hj]. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*  PART II: EQUISPACED ENERGY LEVELS                                       *)
(* ========================================================================= *)

(** Explicit energy values *)
Lemma ho_E0 : ho_energy 0 == (1#2).
Proof. unfold ho_energy, inject_Z, Qeq, Qplus. simpl. lia. Qed.

Lemma ho_E1 : ho_energy 1 == (3#2).
Proof. unfold ho_energy, inject_Z, Qeq, Qplus. simpl. lia. Qed.

Lemma ho_E2 : ho_energy 2 == (5#2).
Proof. unfold ho_energy, inject_Z, Qeq, Qplus. simpl. lia. Qed.

Lemma ho_E3 : ho_energy 3 == (7#2).
Proof. unfold ho_energy, inject_Z, Qeq, Qplus. simpl. lia. Qed.

(** ★ Level spacing is exactly 1 — THE KEY RESULT *)
Theorem ho_level_spacing : forall n,
  ho_energy (S n) - ho_energy n == 1.
Proof.
  intros n. unfold ho_energy.
  setoid_replace (inject_Z (Z.of_nat (S n)))
    with (inject_Z (Z.of_nat n) + 1).
  - ring.
  - rewrite Nat2Z.inj_succ. unfold Z.succ.
    rewrite inject_Z_plus. reflexivity.
Qed.

(** Energy is always positive *)
Lemma ho_energy_positive : forall n, 0 < ho_energy n.
Proof.
  intros n.
  assert (Hn : 0 <= inject_Z (Z.of_nat n)).
  { change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. }
  unfold ho_energy. lra.
Qed.

(** Energy is strictly increasing *)
Lemma ho_energy_increasing : forall n m,
  (n < m)%nat -> ho_energy n < ho_energy m.
Proof.
  intros n m Hnm.
  assert (Hn : inject_Z (Z.of_nat n) < inject_Z (Z.of_nat m)).
  { rewrite <- Zlt_Qlt. lia. }
  unfold ho_energy. lra.
Qed.

(** Ground state has minimum energy *)
Lemma ho_ground_minimum : forall n, ho_energy 0 <= ho_energy n.
Proof.
  intros n.
  assert (Hn : inject_Z (Z.of_nat 0) <= inject_Z (Z.of_nat n)).
  { rewrite <- Zle_Qle. lia. }
  unfold ho_energy. lra.
Qed.

(* ========================================================================= *)
(*  PART III: EIGENSTATES AND SPECTRAL PROPERTIES                           *)
(* ========================================================================= *)

(** |n⟩ is eigenstate of H with eigenvalue E_n *)
Theorem ho_eigenstate : forall N j, (j < N)%nat ->
  is_eigenstate (ho_hamiltonian N) (energy_state N j) (ho_energy j).
Proof.
  intros N j Hj.
  unfold ho_hamiltonian, energy_state.
  exact (eigenstate_eigenvalue_compat _ _ _ _
    (ho_eigenval_access N j Hj)
    (diag_eigenstate (ho_eigenvals N) j Hj)).
Qed.

(** Normalization: ⟨n|n⟩ = 1 *)
Lemma ho_normalization : forall N j k, (j < N)%nat ->
  state_ip_at (energy_state N j) (energy_state N j) k == 1.
Proof.
  intros N j k Hj. unfold energy_state. apply basis_self_ip. exact Hj.
Qed.

(** Orthogonality: ⟨n|m⟩ = 0 for n ≠ m *)
Lemma ho_orthogonality : forall N i j k,
  (i < N)%nat -> (j < N)%nat -> i <> j ->
  state_ip_at (energy_state N i) (energy_state N j) k == 0.
Proof.
  intros N i j k Hi Hj Hij. unfold energy_state.
  apply basis_orthogonal_direct; assumption.
Qed.

(** Expectation of H in eigenstate = eigenvalue *)
Theorem ho_expectation : forall N j k, (j < N)%nat ->
  born_expectation_at (ho_hamiltonian N) (energy_state N j) k == ho_energy j.
Proof.
  intros N j k Hj. unfold ho_hamiltonian, energy_state.
  etransitivity.
  - apply expectation_diag_basis. exact Hj.
  - apply ho_eigenval_access. exact Hj.
Qed.

(** Non-degeneracy: equal energies imply same level *)
Theorem ho_nondeg : forall n m, ho_energy n == ho_energy m -> n = m.
Proof.
  intros n m H.
  assert (Hz : inject_Z (Z.of_nat n) == inject_Z (Z.of_nat m)).
  { unfold ho_energy in H. lra. }
  unfold inject_Z, Qeq in Hz. simpl in Hz. lia.
Qed.

(** Positive energy gap between different levels *)
Lemma ho_energy_gap : forall n m, (n < m)%nat ->
  0 < ho_energy m - ho_energy n.
Proof.
  intros n m Hnm.
  assert (Hn : inject_Z (Z.of_nat n) < inject_Z (Z.of_nat m)).
  { rewrite <- Zlt_Qlt. lia. }
  unfold ho_energy. lra.
Qed.

(** Different levels have different energies *)
Lemma ho_spectral_discrete : forall n m,
  (n < m)%nat -> ~(ho_energy n == ho_energy m).
Proof.
  intros n m Hnm Heq. apply ho_nondeg in Heq. lia.
Qed.

(* ========================================================================= *)
(*  PART IV: TRANSITION PROBABILITIES AND SUPERPOSITION                     *)
(* ========================================================================= *)

(** Self-transition probability = 1 *)
Lemma ho_born_same : forall N j k, (j < N)%nat ->
  born_prob_at (energy_state N j) (energy_state N j) k == 1.
Proof.
  intros N j k Hj. unfold energy_state. apply born_self_basis. exact Hj.
Qed.

(** Transition between different levels = 0 *)
Lemma ho_born_diff : forall N i j k,
  (i < N)%nat -> (j < N)%nat -> i <> j ->
  born_prob_at (energy_state N i) (energy_state N j) k == 0.
Proof.
  intros N i j k Hi Hj Hij. unfold energy_state.
  apply born_orthogonal_at; assumption.
Qed.

(** Superposition of ground and first excited states (dim = 2) *)
Definition ho_superposition_2 : QState 2 :=
  state_add (energy_state 2 0) (energy_state 2 1).

(** Superposition component access *)
Lemma ho_super2_component_0 : forall k,
  qv_nth (state_at ho_superposition_2 k) 0 == 1.
Proof.
  intros k. unfold ho_superposition_2, energy_state.
  change (state_at (state_add (basis_state 2 0) (basis_state 2 1)) k)
    with (qv_add (state_at (basis_state 2 0) k) (state_at (basis_state 2 1) k)).
  rewrite qv_add_nth; [| lia].
  rewrite !basis_state_at.
  rewrite (basis_vec_same 2 0); [| lia].
  rewrite (basis_vec_diff 2 0 1); [| lia | lia].
  ring.
Qed.

Lemma ho_super2_component_1 : forall k,
  qv_nth (state_at ho_superposition_2 k) 1 == 1.
Proof.
  intros k. unfold ho_superposition_2, energy_state.
  change (state_at (state_add (basis_state 2 0) (basis_state 2 1)) k)
    with (qv_add (state_at (basis_state 2 0) k) (state_at (basis_state 2 1) k)).
  rewrite qv_add_nth; [| lia].
  rewrite !basis_state_at.
  rewrite (basis_vec_diff 2 1 0); [| lia | lia].
  rewrite (basis_vec_same 2 1); [| lia].
  ring.
Qed.

(** Superposition norm squared = 2 *)
Lemma ho_superposition_2_norm_sq : forall k,
  state_ip_at ho_superposition_2 ho_superposition_2 k == 2.
Proof.
  intros k. unfold state_ip_at.
  rewrite dot_product_2.
  rewrite ho_super2_component_0, ho_super2_component_1. ring.
Qed.

(** ⟨ground|superposition⟩ = 1 *)
Lemma ho_superposition_ground_ip : forall k,
  state_ip_at (energy_state 2 0) ho_superposition_2 k == 1.
Proof.
  intros k. unfold state_ip_at, energy_state.
  rewrite dot_product_2.
  rewrite ho_super2_component_0, ho_super2_component_1.
  rewrite basis_state_at.
  rewrite (basis_vec_same 2 0); [| lia].
  rewrite (basis_vec_diff 2 1 0); [| lia | lia].
  ring.
Qed.

(** ⟨excited|superposition⟩ = 1 *)
Lemma ho_superposition_excited_ip : forall k,
  state_ip_at (energy_state 2 1) ho_superposition_2 k == 1.
Proof.
  intros k. unfold state_ip_at, energy_state.
  rewrite dot_product_2.
  rewrite ho_super2_component_0, ho_super2_component_1.
  rewrite basis_state_at.
  rewrite (basis_vec_diff 2 0 1); [| lia | lia].
  rewrite (basis_vec_same 2 1); [| lia].
  ring.
Qed.

(** ★ Ground state probability in superposition = 1/2 *)
Theorem ho_superposition_ground_prob : forall k,
  normalized_prob (energy_state 2 0) ho_superposition_2 k == (1#2).
Proof.
  intros k. unfold normalized_prob, born_prob_at.
  rewrite ho_superposition_ground_ip, ho_superposition_2_norm_sq. field.
Qed.

(** Excited state probability in superposition = 1/2 *)
Theorem ho_superposition_excited_prob : forall k,
  normalized_prob (energy_state 2 1) ho_superposition_2 k == (1#2).
Proof.
  intros k. unfold normalized_prob, born_prob_at.
  rewrite ho_superposition_excited_ip, ho_superposition_2_norm_sq. field.
Qed.

(** Probabilities sum to 1 *)
Theorem ho_prob_sum_2 : forall k,
  normalized_prob (energy_state 2 0) ho_superposition_2 k +
  normalized_prob (energy_state 2 1) ho_superposition_2 k == 1.
Proof.
  intros k. rewrite ho_superposition_ground_prob, ho_superposition_excited_prob.
  ring.
Qed.

(* ========================================================================= *)
(*  PART V: SUPERPOSITION EXPECTATION VALUE                                 *)
(* ========================================================================= *)

(** Diagonal matrix entry helpers for ho_hamiltonian 2 *)
Lemma ho2_mat_entry_00 :
  qv_nth (mat_row (diag_mat (ho_eigenvals 2)) 0) 0 == ho_energy 0.
Proof.
  change (mat_entry (diag_mat (ho_eigenvals 2)) 0 0 == ho_energy 0).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 0 0); [| congruence].
  apply ho_eigenval_access. lia.
Qed.

Lemma ho2_mat_entry_01 :
  qv_nth (mat_row (diag_mat (ho_eigenvals 2)) 0) 1 == 0.
Proof.
  change (mat_entry (diag_mat (ho_eigenvals 2)) 0 1 == 0).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 0 1); [lia |]. reflexivity.
Qed.

Lemma ho2_mat_entry_10 :
  qv_nth (mat_row (diag_mat (ho_eigenvals 2)) 1) 0 == 0.
Proof.
  change (mat_entry (diag_mat (ho_eigenvals 2)) 1 0 == 0).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 1 0); [lia |]. reflexivity.
Qed.

Lemma ho2_mat_entry_11 :
  qv_nth (mat_row (diag_mat (ho_eigenvals 2)) 1) 1 == ho_energy 1.
Proof.
  change (mat_entry (diag_mat (ho_eigenvals 2)) 1 1 == ho_energy 1).
  rewrite diag_mat_entry; [| lia | lia].
  destruct (Nat.eq_dec 1 1); [| congruence].
  apply ho_eigenval_access. lia.
Qed.

(** ★ Superposition expectation = E0 + E1 *)
Theorem ho_superposition_expectation : forall k,
  born_expectation_at (ho_hamiltonian 2) ho_superposition_2 k ==
  ho_energy 0 + ho_energy 1.
Proof.
  intros k. unfold born_expectation_at, obs_action_at.
  rewrite dot_product_2.
  rewrite ho_super2_component_0, ho_super2_component_1.
  change (obs_at (ho_hamiltonian 2) k) with (diag_mat (ho_eigenvals 2)).
  set (Mh := diag_mat (ho_eigenvals 2)).
  rewrite !mat_vec_mul_nth; try lia.
  rewrite !dot_product_2.
  rewrite !ho_super2_component_0, !ho_super2_component_1.
  subst Mh.
  rewrite ho2_mat_entry_00, ho2_mat_entry_01,
          ho2_mat_entry_10, ho2_mat_entry_11.
  ring.
Qed.

(** Explicit expectation: ⟨H⟩ = E0 + E1 = 2 *)
Corollary ho_superposition_expectation_value : forall k,
  born_expectation_at (ho_hamiltonian 2) ho_superposition_2 k == 2.
Proof.
  intros k. rewrite ho_superposition_expectation.
  rewrite ho_E0, ho_E1. ring.
Qed.

(** Energy quantization: gap between adjacent levels is always 1 *)
Theorem ho_energy_quantized : forall n,
  ho_energy (S n) - ho_energy n == 1.
Proof. exact ho_level_spacing. Qed.

(** Zero-point energy: ground state has positive energy *)
Theorem ho_zero_point_energy : 0 < ho_energy 0.
Proof. apply ho_energy_positive. Qed.

(** Normalized superposition expectation = average energy = 1 *)
Theorem ho_normalized_expectation : forall k,
  born_expectation_at (ho_hamiltonian 2) ho_superposition_2 k /
  state_ip_at ho_superposition_2 ho_superposition_2 k == 1.
Proof.
  intros k. rewrite ho_superposition_expectation_value,
                    ho_superposition_2_norm_sq. field.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

(** Summary:
    HarmonicOscillator.v: Quantum harmonic oscillator (N-level truncation).

    Part I: Definition
    - ho_energy, ho_eigenvals, ho_hamiltonian, energy_state
    - ho_eigenval_access

    Part II: Equispaced Levels
    - ★ ho_level_spacing: E(n+1) - E(n) == 1
    - Explicit E0-E3 values
    - Energy positive, increasing, ground minimum

    Part III: Eigenstates + Spectral
    - ho_eigenstate: |n⟩ is eigenstate with E_n
    - ho_normalization, ho_orthogonality
    - ho_expectation, ho_nondeg, ho_energy_gap, ho_spectral_discrete

    Part IV: Transition Probabilities
    - ho_born_same/diff for energy eigenstates
    - ★ ho_superposition_ground_prob: P(|0⟩ → |super⟩) = 1/2
    - ho_prob_sum_2: probabilities sum to 1

    Part V: Expectation Values
    - ★ ho_superposition_expectation: ⟨H⟩ = E0 + E1
    - ho_normalized_expectation: normalized ⟨H⟩ = 1
    - Energy quantization, zero-point energy
*)
