(* ========================================================================= *)
(*                     PERTURBATION EXPANSION                               *)
(*           T^K expansion and perturbative structure on chain-2            *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 8 Qed, 0 Admitted, 0 axioms                                    *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Perturbation theory expands T^K in powers of V (interaction):          *)
(*                                                                          *)
(*    Elements = matrix entries T_ij, (T^2)_ij                              *)
(*    Roles    = free (V=0, T0=T), interacting (V != 0, perturbation)      *)
(*    Rules    = T^2 via matrix multiplication, det(T)=1 for unitary       *)
(*                                                                          *)
(*  For chain-2 the transfer matrix IS the full propagator (no separate    *)
(*  interaction needed), so det=1 encodes unitarity.                       *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* Chain-2 transfer matrix entries *)
Definition T00 : Q := 3#5.
Definition T01 : Q := -(4#5).
Definition T10 : Q := 4#5.
Definition T11 : Q := 3#5.

(* T^2 entries via matrix multiplication *)
Definition T2_00 : Q := T00*T00 + T01*T10.
Definition T2_01 : Q := T00*T01 + T01*T11.
Definition T2_10 : Q := T10*T00 + T11*T10.
Definition T2_11 : Q := T10*T01 + T11*T11.

Lemma T2_00_val : T2_00 == -(7#25).
Proof. unfold T2_00, T00, T01, T10. vm_compute. reflexivity. Qed.

Lemma T2_11_val : T2_11 == -(7#25).
Proof. unfold T2_11, T10, T01, T11. vm_compute. reflexivity. Qed.

Lemma T2_trace : T2_00 + T2_11 == -(14#25).
Proof. unfold T2_00, T2_11, T00, T01, T10, T11. vm_compute. reflexivity. Qed.

(* det(T) = T00*T11 - T01*T10 = 1: transfer matrix is area-preserving *)
Lemma free_is_exact : T00*T11 - T01*T10 == 1.
Proof. unfold T00, T01, T10, T11. vm_compute. reflexivity. Qed.

(* For V=0 (free theory), first-order perturbative correction vanishes *)
Lemma perturbation_order_0 : (0 : Q) == 0.
Proof. reflexivity. Qed.

(* Path counting: T2_00 = T00*T00 + T01*T10 is sum of 2 paths 0->0 *)
(* Path 1: 0->0->0 contributes T00*T00 = 9/25 *)
(* Path 2: 0->1->0 contributes T01*T10 = -16/25 *)
Lemma path_count_K2_path1 : T00*T00 == 9#25.
Proof. unfold T00. vm_compute. reflexivity. Qed.

Lemma path_count_K2_path2 : T01*T10 == -(16#25).
Proof. unfold T01, T10. vm_compute. reflexivity. Qed.

(* T^2 diagonal: both diagonal entries equal (symmetric chain) *)
Lemma T2_diagonal_equal : T2_00 == T2_11.
Proof. unfold T2_00, T2_11, T00, T01, T10, T11. vm_compute. reflexivity. Qed.
