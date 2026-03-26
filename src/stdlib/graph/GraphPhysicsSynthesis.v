(* GraphPhysicsSynthesis.v *)
(* E/R/R: Elements = graph zoo + classification synthesis
         Roles = connect spectral gaps to phase classification
         Rules = hbar ordering determines gapped vs critical phase *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.

From ToS Require Import stdlib.graph.GraphZoo.
From ToS Require Import stdlib.graph.GraphClassification.

Open Scope Q_scope.

(* === Chain graph: adjacency + gap + classification === *)

Lemma chain_graph_summary :
  chain_adj 8 0 1 == 1 /\
  chain_edges 8 == 7 /\
  classify_graph (70#100) = GappedGraph (70#100).
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

(* === Complete graph: highest hbar === *)

Lemma complete_graph_summary :
  complete_adj 8 0 1 == 1 /\
  complete_edges 8 == 28 /\
  hbar_complete 8 == 7#2.
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

(* === Star graph: hub-spoke structure === *)

Lemma star_graph_summary :
  star_adj 8 0 1 == 1 /\
  star_adj 8 1 2 == 0.
Proof.
  split; vm_compute; reflexivity.
Qed.

(* === Hbar ordering recap === *)

Lemma hbar_full_ordering :
  hbar_chain < hbar_cycle /\
  hbar_cycle < hbar_ladder /\
  hbar_ladder < hbar_petersen /\
  hbar_petersen < hbar_complete 8.
Proof. exact hbar_ordering. Qed.

(* === Phase classification summary === *)

Lemma phase_summary :
  classify_graph (70#100) = GappedGraph (70#100) /\
  classify_graph (76#100) = GappedGraph (76#100) /\
  classify_graph 0 = CriticalGraph.
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

(* === Grand synthesis === *)

Theorem graph_physics_grand_synthesis :
  (* 1. Graph zoo is well-defined *)
  chain_edges 8 == 7 /\
  complete_edges 8 == 28 /\
  (* 2. Hbar ordering holds *)
  hbar_chain < hbar_complete 8 /\
  (* 3. Classification separates phases *)
  classify_graph (70#100) = GappedGraph (70#100) /\
  classify_graph 0 = CriticalGraph /\
  (* 4. Adjacency matrices are symmetric *)
  (forall K i j, chain_adj K i j == chain_adj K j i) /\
  (forall K i j, complete_adj K i j == complete_adj K j i).
Proof.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold hbar_chain, hbar_complete. simpl. unfold Qlt. simpl. lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact chain_symmetric.
  - exact complete_symmetric.
Qed.

Lemma zoo_count : (gapped_count + critical_count = 7)%nat.
Proof. exact total_zoo_size. Qed.
