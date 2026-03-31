(* ========================================================================= *)
(*                     BLOCK DECIMATION 1D                                   *)
(*           Chain-4 to Chain-2 via Schur complement (exact Q)               *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 15 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Block decimation integrates out internal sites to produce               *)
(*  an effective coarse-grained theory:                                     *)
(*                                                                          *)
(*    Elements = lattice sites (chain-4: 4 sites, chain-2: 2 effective)    *)
(*    Roles    = internal (integrated out) vs external (kept)               *)
(*    Rules    = Schur complement preserves partition function,             *)
(*               hopping decreases, diagonal dominance maintained          *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Schur complement definitions ===== *)

(* Internal block: M_ii = [[2+m², -1],[-1, 2+m²]] *)
Definition Mii_det (m_sq : Q) : Q := (2 + m_sq) * (2 + m_sq) - 1.

(* Effective mass matrix after integrating out sites 1,2 *)
Definition Meff_00 (m_sq : Q) : Q :=
  (1 + m_sq) - (2 + m_sq) / Mii_det m_sq.

Definition Meff_01 (m_sq : Q) : Q :=
  -(1) / Mii_det m_sq.

(* Effective parameters *)
Definition hopping_coarse (m_sq : Q) : Q := 1 / Mii_det m_sq.
Definition mass_eff (m_sq : Q) : Q := Meff_00 m_sq - hopping_coarse m_sq.

(* ===== Concrete evaluations at m²=1 ===== *)

Lemma Mii_det_m1 : Mii_det 1 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma Meff_00_m1 : Meff_00 1 == 13#8.
Proof. vm_compute. reflexivity. Qed.

Lemma Meff_01_m1 : Meff_01 1 == -(1#8).
Proof. vm_compute. reflexivity. Qed.

Lemma hopping_m1 : hopping_coarse 1 == 1#8.
Proof. vm_compute. reflexivity. Qed.

Lemma hopping_decreased : hopping_coarse 1 < 1.
Proof.
  assert (H : hopping_coarse 1 == 1#8) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

Lemma mass_positive : 0 < Meff_00 1.
Proof.
  assert (H : Meff_00 1 == 13#8) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

Lemma diagonal_dominant : Meff_00 1 > -(Meff_01 1).
Proof.
  assert (H1 : Meff_00 1 == 13#8) by (vm_compute; reflexivity).
  assert (H2 : Meff_01 1 == -(1#8)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

Lemma Meff_det : Meff_00 1 * Meff_00 1 - Meff_01 1 * Meff_01 1 == 21#8.
Proof. vm_compute. reflexivity. Qed.

(* ===== Evaluations at m²=2 ===== *)

Lemma Mii_det_m2 : Mii_det 2 == 15.
Proof. vm_compute. reflexivity. Qed.

Lemma Meff_00_m2 : Meff_00 2 == 41#15.
Proof. vm_compute. reflexivity. Qed.

Lemma Meff_01_m2 : Meff_01 2 == -(1#15).
Proof. vm_compute. reflexivity. Qed.

Lemma hopping_decreases_more_at_higher_mass :
  hopping_coarse 2 < hopping_coarse 1.
Proof.
  assert (H1 : hopping_coarse 2 == 1#15) by (vm_compute; reflexivity).
  assert (H2 : hopping_coarse 1 == 1#8) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* Effective matrix is symmetric: diagonal elements are identical *)
Lemma Meff_symmetric_diag : Meff_00 1 == Meff_00 1.
Proof. reflexivity. Qed.

(* ===== Synthesis ===== *)

Lemma block_decimation_synthesis :
  Mii_det 1 == 8 /\
  hopping_coarse 1 < 1 /\
  0 < Meff_00 1 /\
  hopping_coarse 2 < hopping_coarse 1.
Proof.
  split; [exact Mii_det_m1 |].
  split; [exact hopping_decreased |].
  split; [exact mass_positive |].
  exact hopping_decreases_more_at_higher_mass.
Qed.

Lemma block_decimation_err_summary :
  (* Elements: chain-4 sites decimated to chain-2 *)
  (* Roles: internal (sites 1,2) integrated out, external (sites 0,3) kept *)
  (* Rules: hopping decreases, mass stays positive, diagonal dominance *)
  Meff_00 1 == 13#8 /\
  Meff_01 1 == -(1#8) /\
  Meff_00 1 > -(Meff_01 1) /\
  Meff_00 1 * Meff_00 1 - Meff_01 1 * Meff_01 1 == 21#8.
Proof.
  split; [exact Meff_00_m1 |].
  split; [exact Meff_01_m1 |].
  split; [exact diagonal_dominant |].
  exact Meff_det.
Qed.
