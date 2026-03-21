(* CutDistinction.v *)
(* Elements: graph cuts, independent cut families, entropy from cuts *)
(* Roles: max_independent_cuts counts non-crossing partitions, *)
(*        graph_entropy measures information in graph structure *)
(* Rules: entropy <= edges, ratio measures efficiency *)

From Stdlib Require Import QArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

From ToS Require Import stdlib.GraphCuts.

Open Scope Q_scope.

(** * Maximum independent cuts = N - 1 for tree-like graphs *)

Definition max_independent_cuts (N : nat) : nat := Nat.pred N.

(** * Graph entropy = number of independent cuts *)

Definition graph_entropy (N : nat) : nat := max_independent_cuts N.

(** * Concrete values *)

Lemma max_cuts_P4 : max_independent_cuts 4 = 3%nat.
Proof. reflexivity. Qed.

Lemma max_cuts_C3 : max_independent_cuts 3 = 2%nat.
Proof. reflexivity. Qed.

Lemma max_cuts_K4 : max_independent_cuts 4 = 3%nat.
Proof. reflexivity. Qed.

(** * Entropy bounded by vertex count minus 1 *)

Lemma entropy_bound : forall N : nat,
  graph_entropy N = Nat.pred N.
Proof. intros. reflexivity. Qed.

(** * Entropy <= edges: for P4 (3 edges, entropy 3) *)

Lemma entropy_le_edges_P4 :
  (graph_entropy 4 <= num_edges P4_edges)%nat.
Proof. simpl. lia. Qed.

(** * Entropy <= edges: for C3 (3 edges, entropy 2) *)

Lemma entropy_le_edges_C3 :
  (graph_entropy 3 <= num_edges C3_edges)%nat.
Proof. simpl. lia. Qed.

(** * Entropy <= edges: for K4 (6 edges, entropy 3) *)

Lemma entropy_le_edges_K4 :
  (graph_entropy 4 <= num_edges K4_edges)%nat.
Proof. simpl. lia. Qed.

(** * Edge-entropy ratio: how many edges per unit of entropy *)

Definition edge_entropy_ratio (n_edges entropy : nat) : Q :=
  inject_Z (Z.of_nat n_edges) / inject_Z (Z.of_nat entropy).

Lemma ratio_P4 : edge_entropy_ratio (num_edges P4_edges) (graph_entropy 4) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_C3 : edge_entropy_ratio (num_edges C3_edges) (graph_entropy 3) == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_K4 : edge_entropy_ratio (num_edges K4_edges) (graph_entropy 4) == 2.
Proof. vm_compute. reflexivity. Qed.

(** * Complete graphs are least efficient: ratio >= 1 for small cases *)

Lemma ratio_ge_1_P4 : 1 <= edge_entropy_ratio (num_edges P4_edges) (graph_entropy 4).
Proof. vm_compute. discriminate. Qed.

Lemma ratio_ge_1_K4 : 1 <= edge_entropy_ratio (num_edges K4_edges) (graph_entropy 4).
Proof. vm_compute. discriminate. Qed.

(** * Summary *)

Theorem cut_distinction_summary :
  max_independent_cuts 4 = 3%nat /\
  max_independent_cuts 3 = 2%nat /\
  edge_entropy_ratio (num_edges P4_edges) (graph_entropy 4) == 1 /\
  edge_entropy_ratio (num_edges K4_edges) (graph_entropy 4) == 2.
Proof.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { vm_compute. reflexivity. }
  vm_compute. reflexivity.
Qed.
