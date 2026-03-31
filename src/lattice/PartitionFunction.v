(* ========================================================================= *)
(*                     PARTITION FUNCTION                                    *)
(*           Lattice path integral: determinant from eigenvalues             *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 12 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  The partition function Z = det(M) counts field configurations:          *)
(*                                                                          *)
(*    Elements = Laplacian eigenvalues (spectral decomposition)             *)
(*    Roles    = mass parameter m², shifted eigenvalues λ+m²               *)
(*    Rules    = Z = Π(λ_k + m²), zero mode ∈ spectrum (L5: order)         *)
(*                                                                          *)
(*  PHYSICAL NOTE (P4):                                                     *)
(*    The partition function is a FINITE product over eigenvalues.          *)
(*    Each eigenvalue represents a normal mode of the lattice.             *)
(*    The zero mode (λ=0) corresponds to constant field translation.       *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Laplacian eigenvalues for small chain graphs === *)

(* Chain of 2 vertices (path graph P2): eigenvalues of Laplacian *)
Definition laplacian_eigs_2 : list Q := [0; 4].

(* Chain of 3 vertices (path graph P3): eigenvalues *)
Definition laplacian_eigs_3 : list Q := [0; 3; 3].

(* Chain of 4 vertices: eigenvalues (symmetry-adapted) *)
Definition laplacian_eigs_4 : list Q := [0; 2; 4; 2].

(* Shift eigenvalues by mass squared *)
Definition mass_matrix_eigs (eigs : list Q) (m_sq : Q) : list Q :=
  map (fun l => l + m_sq) eigs.

(* Product of a list of rationals *)
Fixpoint list_product (l : list Q) : Q :=
  match l with
  | [] => 1
  | x :: rest => x * list_product rest
  end.

(* Determinant of mass matrix = product of shifted eigenvalues *)
Definition det_mass_matrix (eigs : list Q) (m_sq : Q) : Q :=
  list_product (mass_matrix_eigs eigs m_sq).

(* === Theorems === *)

Lemma mass_eigs_2_m1 :
  mass_matrix_eigs laplacian_eigs_2 1 = [1; 5].
Proof. vm_compute. reflexivity. Qed.

Lemma mass_eigs_3_m1 :
  mass_matrix_eigs laplacian_eigs_3 1 = [1; 4; 4].
Proof. vm_compute. reflexivity. Qed.

Lemma det_chain2_m1 :
  det_mass_matrix laplacian_eigs_2 1 == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma det_chain3_m1 :
  det_mass_matrix laplacian_eigs_3 1 == 16.
Proof. vm_compute. reflexivity. Qed.

Lemma det_chain4_m1 :
  det_mass_matrix laplacian_eigs_4 1 == 45.
Proof. vm_compute. reflexivity. Qed.

Lemma det_chain2_m2 :
  det_mass_matrix laplacian_eigs_2 2 == 12.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_mode :
  In 0 laplacian_eigs_2.
Proof. left. reflexivity. Qed.

Lemma det_positive_m1 :
  0 < det_mass_matrix laplacian_eigs_2 1.
Proof. vm_compute. reflexivity. Qed.

Lemma det_grows_with_mass :
  det_mass_matrix laplacian_eigs_2 1 < det_mass_matrix laplacian_eigs_2 2.
Proof. vm_compute. reflexivity. Qed.

Lemma eigs_count_2 :
  length laplacian_eigs_2 = 2%nat.
Proof. reflexivity. Qed.

Lemma eigs_count_3 :
  length laplacian_eigs_3 = 3%nat.
Proof. reflexivity. Qed.

Lemma partition_synthesis :
  det_mass_matrix laplacian_eigs_2 1 == 5 /\
  det_mass_matrix laplacian_eigs_3 1 == 16 /\
  det_mass_matrix laplacian_eigs_4 1 == 45 /\
  In 0 laplacian_eigs_2 /\
  0 < det_mass_matrix laplacian_eigs_2 1 /\
  det_mass_matrix laplacian_eigs_2 1 < det_mass_matrix laplacian_eigs_2 2.
Proof.
  repeat split; try (vm_compute; reflexivity).
  left. reflexivity.
Qed.
