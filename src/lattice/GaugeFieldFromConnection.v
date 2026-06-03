(* ========================================================================= *)
(*                  GAUGE FIELD FROM CONNECTION                             *)
(*         SU(2) link variables as ToS connection (3/5, 4/5 rotation)      *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 10 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Gauge fields live on LINKS (edges), not vertices:                       *)
(*                                                                          *)
(*    Elements = U_ij (2x2 matrix entries over Q)                           *)
(*    Roles    = unitary properties, det=1, orthogonality                   *)
(*    Rules    = link_unitary, link_det_one (L5: gauge invariance)          *)
(*                                                                          *)
(*  PHILOSOPHICAL NOTE (P4):                                                *)
(*    The Pythagorean triple (3,4,5) gives an EXACT rational rotation.     *)
(*    This is key: gauge fields over Q require rational group elements.     *)
(*    The 3-4-5 right triangle gives cos=3/5, sin=4/5, det=1 exactly.     *)
(*    SYSTEMATIC: this (cos=3/5, sin=4/5) rotation is now DERIVED as       *)
(*    param(1/2) in stdlib/PythagoreanTriples.v (three_four_five_is_       *)
(*    param_half) — no longer an ad hoc constant.                         *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Link Variable: 2x2 rotation matrix from 3-4-5 Pythagorean triple === *)

(** Matrix entries of the link variable U (SO(2) rotation by arctan(4/3)) *)
Definition U00 : Q := 3#5.
Definition U01 : Q := -(4#5).
Definition U10 : Q := 4#5.
Definition U11 : Q := 3#5.

(* === Unitarity / Orthogonality Properties === *)

(** Column 0 is unit vector: U00^2 + U10^2 = 1 *)
Lemma link_unitary_col0 : U00 * U00 + U10 * U10 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Column 1 is unit vector: U01^2 + U11^2 = 1 *)
Lemma link_unitary_col1 : U01 * U01 + U11 * U11 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Determinant equals 1: special orthogonal *)
Lemma link_det_one : U00 * U11 - U01 * U10 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Columns are orthogonal *)
Lemma link_orthogonal : U00 * U01 + U10 * U11 == 0.
Proof. vm_compute. reflexivity. Qed.

(* === Trace and Powers === *)

(** Trace of U = 6/5 *)
Lemma trace_T : U00 + U11 == 6#5.
Proof. vm_compute. reflexivity. Qed.

(** (U^2)_{00} entry *)
Lemma T_sq_00 : U00 * U00 + U01 * U10 == -(7#25).
Proof. vm_compute. reflexivity. Qed.

(** (U^2)_{11} entry *)
Lemma T_sq_11 : U10 * U01 + U11 * U11 == -(7#25).
Proof. vm_compute. reflexivity. Qed.

(** Trace of U^2 = -14/25 *)
Lemma trace_T_sq :
  (U00 * U00 + U01 * U10) + (U10 * U01 + U11 * U11) == -(14#25).
Proof. vm_compute. reflexivity. Qed.

(** Wilson loop for single link = trace of U *)
Lemma wilson_loop_trivial : U00 + U11 == 6#5.
Proof. vm_compute. reflexivity. Qed.

(** Synthesis: all gauge field properties hold simultaneously *)
Lemma connection_is_gauge_synthesis :
  U00 * U00 + U10 * U10 == 1 /\
  U01 * U01 + U11 * U11 == 1 /\
  U00 * U11 - U01 * U10 == 1 /\
  U00 * U01 + U10 * U11 == 0 /\
  U00 + U11 == 6#5 /\
  (U00 * U00 + U01 * U10) + (U10 * U01 + U11 * U11) == -(14#25).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
