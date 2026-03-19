(** * AtomicSynthesis.v — Atomic Physics Summary as ToS System
    Elements: H, He, Li atoms on lattice
    Roles:    Coulomb tower (H), two-particle (He), Slater screening (Li)
    Rules:    all atoms have negative energy, positive ionization
    Status:   Dir 1, File 4 of Atomic Physics — synthesis
    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import MonotoneConvergence.
From ToS Require Import experimental.CoulombTower.
From ToS Require Import experimental.TwoParticleLattice.
From ToS Require Import experimental.HeliumLattice.
From ToS Require Import experimental.LithiumLattice.

(* ========================================================================= *)
(*              HYDROGEN RECAP                                               *)
(* ========================================================================= *)

(** H ground state is negative (from CoulombTower) *)
Lemma hydrogen_bound : scaled_energy 3 0 < 0.
Proof. apply ground_negative. Qed.

(* ========================================================================= *)
(*              THREE-ATOM SUMMARY                                           *)
(* ========================================================================= *)

(** All three atoms have bound (negative energy) ground states *)
Theorem atoms_are_bound :
  scaled_energy 3 0 < 0 /\
  he_ground_estimate 3 1 < 0 /\
  li_total_energy < 0.
Proof.
  split; [|split].
  - apply ground_negative.
  - rewrite he_ground_K3. lra.
  - unfold li_total_energy.
    assert (H1 := li_inner_negative). assert (H2 := li_outer_negative). lra.
Qed.

(** All three atoms have positive ionization energy *)
Theorem atoms_have_ionization :
  0 < he_ionization 3 1 /\
  0 < li_ionization.
Proof.
  split.
  - apply he_ionization_positive_K3.
  - apply li_ionization_positive.
Qed.

(** The periodic table: Z=1,2,3 computed.
    H: diagonal Coulomb tower
    He: two-particle lattice with repulsion
    Li: Slater screening frozen-core *)
Theorem atomic_physics_summary :
  (* H: negative ground state *)
  scaled_energy 3 0 < 0 /\
  (* He: negative ground state, repulsion raises energy *)
  he_ground_estimate 3 1 < 0 /\
  he_no_repulsion 3 1 < he_ground_estimate 3 1 /\
  (* Li: bound state with screening *)
  li_total_energy < 0 /\
  0 < li_ionization.
Proof.
  split; [|split; [|split; [|split]]].
  - apply ground_negative.
  - rewrite he_ground_K3. lra.
  - apply repulsion_raises_energy.
  - unfold li_total_energy.
    assert (H1 := li_inner_negative). assert (H2 := li_outer_negative). lra.
  - apply li_ionization_positive.
Qed.

(** Multi-electron complexity: He repulsion is 1 at same site *)
Theorem repulsion_at_nucleus :
  electron_repulsion 3 1 1 == 1.
Proof.
  apply repulsion_same_site.
Qed.
