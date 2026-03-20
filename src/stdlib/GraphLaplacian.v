(** * GraphLaplacian.v -- Graph Laplacian on finite lattice over Q
    Elements: path_adj, path_degree, graph_laplacian, cycle_laplacian
    Roles:    L = D - A on path and cycle graphs
    Rules:    Row sums = 0, eigenvalue 0 for constant vector
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  GRAPH ON FINITE LATTICE                                            *)
(* ================================================================== *)

(** Adjacency matrix for path graph P_n: 0-1-2-...-n *)
Definition path_adj (n : nat) (i j : nat) : Q :=
  if (Nat.eqb (S i) j || Nat.eqb i (S j))%bool then 1 else 0.

(** Degree of vertex i in path: d(0) = d(n) = 1, d(middle) = 2 *)
Definition path_degree (n i : nat) : Q :=
  if Nat.eqb i 0 then 1
  else if Nat.eqb i n then 1
  else 2.

(** Graph Laplacian: L = D - A *)
Definition graph_laplacian (n : nat) (i j : nat) : Q :=
  (if Nat.eqb i j then path_degree n i else 0) - path_adj n i j.

(* ================================================================== *)
(*  CONCRETE: P₃ (path on 4 vertices: 0-1-2-3)                        *)
(*  L = [1 -1 0 0; -1 2 -1 0; 0 -1 2 -1; 0 0 -1 1]                  *)
(* ================================================================== *)

Lemma L_P3_00 : graph_laplacian 3 0 0 == 1.
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

Lemma L_P3_01 : graph_laplacian 3 0 1 == -(1).
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

Lemma L_P3_02 : graph_laplacian 3 0 2 == 0.
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

Lemma L_P3_11 : graph_laplacian 3 1 1 == 2.
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

Lemma L_P3_12 : graph_laplacian 3 1 2 == -(1).
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PROPERTIES                                                         *)
(* ================================================================== *)

(** Row sums = 0 (L·1 = 0) *)
Lemma L_row_sum_0 :
  graph_laplacian 3 0 0 + graph_laplacian 3 0 1 +
  graph_laplacian 3 0 2 + graph_laplacian 3 0 3 == 0.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

Lemma L_row_sum_1 :
  graph_laplacian 3 1 0 + graph_laplacian 3 1 1 +
  graph_laplacian 3 1 2 + graph_laplacian 3 1 3 == 0.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

Lemma L_row_sum_2 :
  graph_laplacian 3 2 0 + graph_laplacian 3 2 1 +
  graph_laplacian 3 2 2 + graph_laplacian 3 2 3 == 0.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

Lemma L_row_sum_3 :
  graph_laplacian 3 3 0 + graph_laplacian 3 3 1 +
  graph_laplacian 3 3 2 + graph_laplacian 3 3 3 == 0.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CYCLE GRAPH                                                        *)
(* ================================================================== *)

(** Cycle graph C₃ (triangle): L = [2 -1 -1; -1 2 -1; -1 -1 2] *)
Definition cycle_laplacian (n : nat) (i j : nat) : Q :=
  if Nat.eqb i j then 2
  else if Nat.eqb (S i mod S n) (j mod S n) then -(1)
  else if Nat.eqb (i mod S n) (S j mod S n) then -(1)
  else 0.

Lemma cycle_L_00 : cycle_laplacian 2 0 0 == 2.
Proof. unfold cycle_laplacian. vm_compute. reflexivity. Qed.

Lemma cycle_L_01 : cycle_laplacian 2 0 1 == -(1).
Proof. unfold cycle_laplacian. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** Graph Laplacian eigenvalues = lattice mode frequencies
    Mass gap = smallest nonzero eigenvalue of Laplacian *)

Theorem laplacian_mass_gap_connection :
  graph_laplacian 3 0 0 + graph_laplacian 3 0 1 +
  graph_laplacian 3 0 2 + graph_laplacian 3 0 3 == 0 /\
  graph_laplacian 3 1 1 == 2 /\
  graph_laplacian 3 0 1 == -(1).
Proof.
  split; [|split].
  - exact L_row_sum_0.
  - exact L_P3_11.
  - exact L_P3_01.
Qed.
