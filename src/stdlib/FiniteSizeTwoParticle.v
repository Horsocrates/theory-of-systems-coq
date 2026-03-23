(** * FiniteSizeTwoParticle.v — Two-Particle Finite-Size Spectrum
    Elements: Single-particle energy, two-particle additive spectrum, interaction
    Roles:    Connect single-particle eigenvalue to two-body sector
    Rules:    E_two = E1 + E2, interaction matrix for K=2
    Status:   Stdlib
    STATUS: 9 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  SINGLE-PARTICLE ENERGY                                             *)
(*  For K-site chain, ground state E1(K) from spectral flow            *)
(* ================================================================== *)

(* E1(K=2) = 1 (from SpectralFlowGround: ground_K2 = 1) *)
Definition E1_K2 : Q := 1.

(* E1(K=3) ≈ 7/12 *)
Definition E1_K3 : Q := 7#12.

(* E1(K=4) ≈ 55/144 *)
Definition E1_K4 : Q := 55#144.

(* ================================================================== *)
(*  TWO-PARTICLE ADDITIVE SPECTRUM                                     *)
(*  Without interaction: E_two = E1 + E1                               *)
(* ================================================================== *)

Definition E0_two (E1 : Q) : Q := 2 * E1.

Lemma two_particle_K2 : E0_two E1_K2 == 2.
Proof. unfold E0_two, E1_K2. ring. Qed.

Lemma two_particle_K3 : E0_two E1_K3 == 7#6.
Proof. unfold E0_two, E1_K3. ring. Qed.

Lemma two_particle_K4 : E0_two E1_K4 == 55#72.
Proof. unfold E0_two, E1_K4. ring. Qed.

(* ================================================================== *)
(*  INTERACTION TERM                                                   *)
(*  For K=2, 4x4 interaction matrix g: coupling between sites          *)
(*  g_ij = delta(|i-j|, 1) * g_strength                               *)
(* ================================================================== *)

Definition g_strength : Q := 1#10.

(* 4x4 interaction matrix for K=2 two-particle sector *)
(* Basis: |00>, |01>, |10>, |11> — interaction only on adjacent *)
Definition interaction_K2 (r c : nat) : Q :=
  match r, c with
  | O, S O => g_strength
  | S O, O => g_strength
  | S (S O), S (S (S O)) => g_strength
  | S (S (S O)), S (S O) => g_strength
  | _, _ => 0
  end.

Lemma interaction_symmetric :
  interaction_K2 O (S O) == interaction_K2 (S O) O.
Proof. vm_compute. reflexivity. Qed.

Lemma interaction_diagonal_zero :
  interaction_K2 O O == 0 /\ interaction_K2 (S O) (S O) == 0.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  ENERGY ORDERING                                                    *)
(*  E1(K) decreasing in K (finer grid → lower ground state)           *)
(* ================================================================== *)

Lemma energy_ordering_K2_K3 : E1_K3 < E1_K2.
Proof. unfold E1_K3, E1_K2. lra. Qed.

Lemma energy_ordering_K3_K4 : E1_K4 < E1_K3.
Proof. unfold E1_K4, E1_K3. lra. Qed.

Lemma two_particle_larger : forall E1, 0 < E1 -> E1 < E0_two E1.
Proof. intros. unfold E0_two. lra. Qed.

Theorem finite_size_two_particle_synthesis :
  E0_two E1_K2 == 2 /\
  E1_K3 < E1_K2 /\
  E1_K4 < E1_K3.
Proof.
  split; [exact two_particle_K2|].
  split; [exact energy_ordering_K2_K3|].
  exact energy_ordering_K3_K4.
Qed.
