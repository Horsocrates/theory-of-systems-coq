(** * GraphUncertaintySynthesis.v — Synthesis: graph-dependent uncertainty
    Elements: graph_grand, topology_orders_uncertainty, edge_uncertainty_link
    Roles:    More connected graph = larger uncertainty = more information flow
    Rules:    chain < cycle < complete in both edges and rms_hbar
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.heisenberg.GraphUncertainty.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Grand Synthesis                                            *)
(* ================================================================== *)

Theorem graph_grand :
  rms_hbar_chain 10 == 9#20 /\
  rms_hbar_cycle 10 == 1#2 /\
  rms_hbar_complete 10 == 9#4.
Proof.
  split; [exact chain_rms_10|].
  split; [exact cycle_rms_10|].
  exact complete_rms_10.
Qed.

Theorem topology_orders_uncertainty :
  rms_hbar_chain 10 < rms_hbar_cycle 10 /\
  rms_hbar_cycle 10 < rms_hbar_complete 10 /\
  rms_hbar_complete 10 > rms_hbar_chain 10.
Proof.
  split; [exact cycle_larger_than_chain|].
  split; [exact complete_larger_than_cycle|].
  exact complete_larger.
Qed.

Theorem edge_uncertainty_link :
  edge_count_chain 10 < edge_count_cycle 10 /\
  edge_count_cycle 10 < edge_count_complete 10.
Proof.
  split; [exact edge_ordering|exact edge_ordering_2].
Qed.

(* ================================================================== *)
(*  Part II: Concrete Adjacency Verification                           *)
(* ================================================================== *)

Theorem adjacency_concrete :
  adj_chain_entry 5 0 1 == 1 /\
  adj_chain_entry 5 0 2 == 0 /\
  adj_cycle_entry 5 0 4 == 1 /\
  adj_complete_entry 5 0 3 == 1 /\
  adj_complete_entry 5 2 2 == 0.
Proof.
  split; [exact chain_01|].
  split; [exact chain_02|].
  split; [exact cycle_04|].
  split; [exact complete_03|].
  exact complete_22.
Qed.

Theorem tr_A2_concrete :
  tr_A2_chain 10 == 18 /\
  tr_A2_cycle 10 == 20 /\
  tr_A2_complete 10 == 90.
Proof.
  split; [exact tr_A2_chain_10|].
  split; [exact tr_A2_cycle_10|].
  exact tr_A2_complete_10.
Qed.

(** Key insight: edge_count and rms_hbar have same ordering.
    More edges = more uncertainty. Connectivity drives quantum uncertainty. *)
Theorem more_edges_more_uncertainty :
  edge_count_chain 10 < edge_count_cycle 10 /\
  rms_hbar_chain 10 < rms_hbar_cycle 10 /\
  edge_count_cycle 10 < edge_count_complete 10 /\
  rms_hbar_cycle 10 < rms_hbar_complete 10.
Proof.
  split; [exact edge_ordering|].
  split; [exact cycle_larger_than_chain|].
  split; [exact edge_ordering_2|].
  exact complete_larger_than_cycle.
Qed.

Theorem cycle_rms_is_half : rms_hbar_cycle 10 == 1#2.
Proof. exact cycle_rms_10. Qed.

Theorem chain_rms_less_than_half : rms_hbar_chain 10 < (1#2).
Proof.
  unfold rms_hbar_chain, tr_A2_chain.
  vm_compute. reflexivity.
Qed.
