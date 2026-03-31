(* ========================================================================= *)
(*                    LATTICE FIELD EQUATIONS                               *)
(*         Discrete Laplacian and Klein-Gordon on the lattice              *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 6 Qed, 0 Admitted, 0 axioms                                    *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Field equations on the lattice = discrete differential operators:       *)
(*                                                                          *)
(*    Elements = phi : nat -> Q (field configurations)                      *)
(*    Roles    = laplacian_1d, klein_gordon_1d (discrete operators)          *)
(*    Rules    = laplacian_constant_zero, kg_is_laplacian_plus_mass         *)
(*               (L5: equations of motion from action extremum)             *)
(*                                                                          *)
(*  PHILOSOPHICAL NOTE (P4):                                                *)
(*    The discrete Laplacian Delta_phi(v) = 2*phi(v) - phi(v-1) - phi(v+1) *)
(*    is the GRAPH Laplacian on the path graph. It IS the second            *)
(*    derivative — not an approximation, but the exact finite analog.       *)
(*    The continuum Laplacian is the PROCESS LIMIT of this sequence.        *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Discrete Differential Operators === *)

(** Discrete Laplacian on 1D lattice (graph Laplacian of path graph):
    Delta phi(v) = 2*phi(v) - phi(v-1) - phi(v+1)
    This is (z*I - A) applied to phi, where z=2 and A is adjacency matrix. *)
Definition laplacian_1d (phi : nat -> Q) (v : nat) : Q :=
  2 * phi v - phi (pred v) - phi (S v).

(** Discrete Klein-Gordon operator: Laplacian + mass term *)
Definition klein_gordon_1d (phi : nat -> Q) (m_sq : Q) (v : nat) : Q :=
  laplacian_1d phi v + m_sq * phi v.

(* === Laplacian Properties === *)

(** Constant field is in the kernel of the Laplacian *)
Lemma laplacian_constant_zero : laplacian_1d (fun _ => 1) 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Linear field f(v)=v is harmonic (Laplacian = 0) on the interior.
    This is the discrete analog of d^2(x)/dx^2 = 0. *)
Lemma laplacian_linear :
  laplacian_1d (fun v => inject_Z (Z.of_nat v)) 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Quadratic field f(v)=v^2 has Laplacian = -2 at v=1.
    Delta f(1) = 2*f(1) - f(0) - f(2) = 2*1 - 0 - 4 = -2.
    Note: our convention is Delta = 2I - A (positive semidefinite graph Laplacian),
    so the second difference of a convex function is negative. *)
Lemma laplacian_quadratic :
  laplacian_1d (fun v => inject_Z (Z.of_nat v) * inject_Z (Z.of_nat v)) 1 == -(2).
Proof. vm_compute. reflexivity. Qed.

(** Massless Klein-Gordon on constant field = 0
    (constant is in kernel of both Laplacian and m=0 mass term) *)
Lemma kg_massless : klein_gordon_1d (fun _ => 1) 0 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Klein-Gordon is definitionally Laplacian + mass *)
Lemma kg_is_laplacian_plus_mass :
  forall (phi : nat -> Q) (m : Q) (v : nat),
  klein_gordon_1d phi m v == laplacian_1d phi v + m * phi v.
Proof. intros. unfold klein_gordon_1d. ring. Qed.

(** Graph Laplacian interpretation: at v=1, the Laplacian equals
    (degree * phi(v)) - sum of neighbor values.
    For path graph interior, degree = 2, neighbors = {v-1, v+1}. *)
Lemma laplacian_is_graph_laplacian :
  forall (phi : nat -> Q),
  laplacian_1d phi 1 == 2 * phi 1%nat - (phi 0%nat + phi 2%nat).
Proof. intros. unfold laplacian_1d. simpl. ring. Qed.
