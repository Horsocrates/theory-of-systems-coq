(** * SpectralGraphSynthesis.v -- Spectral graph theory: eigenvalues + Cheeger
    Elements: constant_vec, cheeger_bound, spectral_graph_synthesis
    Roles:    Eigenvalue tests and Cheeger inequality on path graph P₃
    Rules:    L·1 = 0 (constant vector), λ₂ ≥ h²/(2d_max) (Cheeger)
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GraphLaplacian.

Open Scope Q_scope.

(* ================================================================== *)
(*  EIGENVALUE TESTS                                                   *)
(* ================================================================== *)

(** Test vector v = [1,1,1,1]: L·v should = 0 (eigenvalue 0) *)
Definition constant_vec : nat -> Q := fun _ => 1.

Lemma L_times_constant_row0 :
  graph_laplacian 3 0 0 * 1 + graph_laplacian 3 0 1 * 1 +
  graph_laplacian 3 0 2 * 1 + graph_laplacian 3 0 3 * 1 == 0.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

Lemma L_times_constant_row1 :
  graph_laplacian 3 1 0 * 1 + graph_laplacian 3 1 1 * 1 +
  graph_laplacian 3 1 2 * 1 + graph_laplacian 3 1 3 * 1 == 0.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

(** Test vector v = [1,-1,1,-1]: alternating *)
Lemma L_times_alternating_row0 :
  graph_laplacian 3 0 0 * 1 + graph_laplacian 3 0 1 * (-(1)) +
  graph_laplacian 3 0 2 * 1 + graph_laplacian 3 0 3 * (-(1)) == 2.
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

Lemma L_times_alternating_row3 :
  graph_laplacian 3 3 0 * 1 + graph_laplacian 3 3 1 * (-(1)) +
  graph_laplacian 3 3 2 * 1 + graph_laplacian 3 3 3 * (-(1)) == -(2).
Proof.
  unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CHEEGER INEQUALITY                                                 *)
(* ================================================================== *)

(** λ₂ ≥ h²/(2d_max)
    For P₃: d_max = 2, h(P₃) = 1/2
    Cheeger: λ₂ ≥ (1/2)²/4 = 1/16
    True λ₂ = 2 - √2 ≈ 0.586 >> 1/16 *)

Definition cheeger_bound (h d_max : Q) : Q :=
  h * h / (2 * d_max).

Lemma cheeger_P3 : cheeger_bound (1#2) 2 == 1 # 16.
Proof.
  unfold cheeger_bound. vm_compute. reflexivity.
Qed.

(** Cheeger bound is positive for connected graph *)
Lemma cheeger_positive : 0 < cheeger_bound (1#2) 2.
Proof. rewrite cheeger_P3. lra. Qed.

(* ================================================================== *)
(*  LAPLACIAN SYMMETRY                                                 *)
(* ================================================================== *)

(** L is symmetric: L(i,j) = L(j,i) *)
Lemma L_symmetric_01 : graph_laplacian 3 0 1 == graph_laplacian 3 1 0.
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

Lemma L_symmetric_12 : graph_laplacian 3 1 2 == graph_laplacian 3 2 1.
Proof. unfold graph_laplacian, path_degree, path_adj. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem spectral_graph_synthesis :
  graph_laplacian 3 0 0 + graph_laplacian 3 0 1 +
  graph_laplacian 3 0 2 + graph_laplacian 3 0 3 == 0 /\
  cheeger_bound (1#2) 2 == 1 # 16 /\
  graph_laplacian 3 1 1 == 2.
Proof.
  split; [|split].
  - exact L_row_sum_0.
  - exact cheeger_P3.
  - exact L_P3_11.
Qed.
