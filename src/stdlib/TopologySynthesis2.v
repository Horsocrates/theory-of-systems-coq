(** * TopologySynthesis2.v — Grand Topology Synthesis (Phase 2)
    Elements: Chern number, edge states, process refinement, Z2 invariant
    Roles:    Unify all topological computations into one coherent picture
    Rules:    Topology = process-level classification beyond band theory
    Status:   Stdlib — Six Directions Phase 2, Section E9
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.LatticeChernFull.
From ToS Require Import stdlib.EdgeStates.
From ToS Require Import stdlib.TopologicalProcessRefinement.
From ToS Require Import stdlib.Z2Invariant.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: CHERN NUMBER RECAP                                         *)
(* ================================================================== *)

Lemma chern_m1_topological : sign_count_negative_4x4 1 = 1%nat.
Proof. exact chern_m1. Qed.

Lemma chern_m3_trivial : sign_count_negative_4x4 3 = 0%nat.
Proof. exact chern_m3. Qed.

(* ================================================================== *)
(*  PART II: BULK-BOUNDARY RECAP                                       *)
(* ================================================================== *)

Lemma edge_in_bulk_gap :
  bulk_energy_min < edge_eigenvalue /\ edge_eigenvalue < bulk_energy_max.
Proof.
  split; [exact edge_in_gap_lower | exact edge_in_gap_upper].
Qed.

(* ================================================================== *)
(*  PART III: PROCESS REFINEMENT RECAP                                  *)
(* ================================================================== *)

Lemma process_finer_than_chern :
  sum4 concentrated_F == sum4 uniform_F /\
  ~ (concentrated_F O == uniform_F O).
Proof.
  split; [exact same_chern | exact different_at_0].
Qed.

(* ================================================================== *)
(*  PART IV: Z2 RECAP                                                   *)
(* ================================================================== *)

Lemma z2_classifies :
  Z2_invariant (1%Z :: 1%Z :: 1%Z :: (-1)%Z :: nil) = (-1)%Z /\
  Z2_invariant (1%Z :: 1%Z :: 1%Z :: 1%Z :: nil) = 1%Z.
Proof.
  split; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  PART V: HIERARCHY OF INVARIANTS                                     *)
(*  Process ⊃ Chern ⊃ Z2                                              *)
(*  Process sees distribution; Chern sees parity; Z2 sees ±1          *)
(* ================================================================== *)

Lemma chern_determines_topology :
  is_topological 1 = true /\ is_topological 3 = false.
Proof.
  split; [exact topological_m1 | exact trivial_m3].
Qed.

Lemma z2_coarser_than_chern :
  (* Z2 only sees ±1; Chern sees the full count *)
  sign_count_negative_4x4 1 = 1%nat /\
  sign_count_negative_4x4 3 = 0%nat /\
  is_Z2_topological (1%Z :: 1%Z :: 1%Z :: (-1)%Z :: nil) = true /\
  is_Z2_topological (1%Z :: 1%Z :: 1%Z :: 1%Z :: nil) = false.
Proof.
  repeat split; try (vm_compute; reflexivity).
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

Theorem topology_grand_synthesis_2 :
  (* E5: Chern from lattice *)
  sign_count_negative_4x4 1 = 1%nat /\
  (* E6: Edge in gap *)
  bulk_energy_min < edge_eigenvalue /\
  (* E7: Process strictly finer *)
  sum4 concentrated_F == sum4 uniform_F /\
  ~ (concentrated_F O == uniform_F O) /\
  (* E8: Z2 classification *)
  Z2_invariant (1%Z :: 1%Z :: 1%Z :: (-1)%Z :: nil) = (-1)%Z.
Proof.
  split; [exact chern_m1|].
  split; [exact edge_in_gap_lower|].
  split; [exact same_chern|].
  split; [exact different_at_0|].
  vm_compute. reflexivity.
Qed.
