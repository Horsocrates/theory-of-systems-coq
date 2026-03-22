(** * GreenDeepSynthesis.v -- Grand unification: spectral + resolvent + path + det
    Elements: All four views unified through golden mean matrix
    Roles:    G_{ij}(K) simultaneously encodes spectrum, resolvent, paths, det
    Rules:    One matrix, four perspectives, all verified over Q
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.GreenSpectral.
From ToS Require Import stdlib.GreenSpectralSynthesis.
From ToS Require Import stdlib.GreenResolvent.
From ToS Require Import stdlib.ResolventSynthesis.
From ToS Require Import stdlib.GreenPathIntegral.
From ToS Require Import stdlib.ChapmanKolmogorov.
From ToS Require Import stdlib.GreenDeterminant.

Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  FOUR VIEWS OF THE GOLDEN MATRIX                                    *)
(* ================================================================== *)

(** View 1: Spectral — trace and det determine recurrence *)
Theorem golden_spectral_view :
  char_p golden == 1 /\ char_q golden == -(1) /\
  green golden 0%nat 0%nat 6 == 13.
Proof.
  split; [exact golden_char_p|].
  split; [exact golden_char_q|exact green_golden_00_6].
Qed.

(** View 2: Resolvent — generating function of G *)
Theorem golden_resolvent_view :
  resolvent_det golden 0 == 1 /\
  resolvent_det golden 1 == -(1) /\
  discriminant golden == 5.
Proof.
  split; [exact resolvent_det_golden_0|].
  split; [exact resolvent_det_golden_1|exact golden_discriminant].
Qed.

(** View 3: Path integral — paths sum to Green's function *)
Theorem golden_path_view :
  path_weight golden [0%nat; 0%nat; 0%nat] +
  path_weight golden [0%nat; 1%nat; 0%nat] == green golden 0%nat 0%nat 2.
Proof. exact golden_path_sum_K2. Qed.

(** View 4: Determinant — Cassini identity *)
Theorem golden_det_view :
  det2 golden == -(1) /\
  det2 (mat2_pow golden 5) == GreenDeterminant.qpow (-(1)) 5.
Proof.
  split; [exact det_golden|exact cassini_5].
Qed.

(* ================================================================== *)
(*  CROSS-VIEW CONNECTIONS                                             *)
(* ================================================================== *)

(** Spectral ↔ Resolvent: char_q = det = resolvent coefficient *)
Lemma spectral_resolvent_connection :
  char_q golden == det2 golden.
Proof. vm_compute. reflexivity. Qed.

(** Spectral ↔ Determinant: Cayley-Hamilton uses both trace and det *)
Lemma spectral_det_connection :
  green golden 0%nat 0%nat 4 ==
  char_p golden * green golden 0%nat 0%nat 3 - char_q golden * green golden 0%nat 0%nat 2 /\
  char_q golden == det2 golden.
Proof.
  split; [exact cayley_hamilton_golden_2|exact spectral_resolvent_connection].
Qed.

(** Path ↔ Chapman-Kolmogorov: both express propagator composition *)
Lemma path_ck_connection :
  green golden 0%nat 0%nat 4 == ck_sum golden 0%nat 0%nat 2 2 /\
  path_weight golden [0%nat; 0%nat; 0%nat] +
  path_weight golden [0%nat; 1%nat; 0%nat] == green golden 0%nat 0%nat 2.
Proof.
  split; [exact ck_golden_00_2_2|exact golden_path_sum_K2].
Qed.

(** Resolvent ↔ Det: poles = eigenvalues, discriminant classifies *)
Lemma resolvent_det_connection :
  discriminant golden == 5 /\
  is_conservative golden.
Proof.
  split; [exact golden_discriminant|exact golden_is_conservative].
Qed.

(** Full shift: degenerate case (det=0) *)
Lemma full_degenerate :
  det2 full_mat2 == 0 /\
  is_pole full_mat2 (1#2) /\
  char_q full_mat2 == 0.
Proof.
  split; [exact det_full|].
  split; [exact full_has_pole_half|exact full_char_q].
Qed.

(* ================================================================== *)
(*  INTERFERENCE: HADAMARD COMPARISON                                  *)
(* ================================================================== *)

(** Hadamard has det=-2 (expanding) vs golden det=-1 (conservative) *)
Lemma hadamard_vs_golden :
  det2 hadamard_like == -(2) /\
  det2 golden == -(1) /\
  green hadamard_like 0%nat 1%nat 2 == 0 /\
  green golden 0%nat 1%nat 2 == 1.
Proof.
  split; [exact det_hadamard|].
  split; [exact det_golden|].
  split; [exact hadamard_destructive|].
  vm_compute. reflexivity.
Qed.

(** Full shift: all four views degenerate consistently *)
Lemma full_four_views :
  (* Spectral: trace=2, det=0 *)
  char_p full_mat2 == 2 /\
  char_q full_mat2 == 0 /\
  (* Resolvent: linear (pole at 1/2) *)
  is_pole full_mat2 (1#2) /\
  (* Det: singular *)
  det2 full_mat2 == 0.
Proof.
  split; [exact full_char_p|].
  split; [exact full_char_q|].
  split; [exact full_has_pole_half|exact det_full].
Qed.

(** Fibonacci identity F(6) = 13 verified through all paths *)
Lemma fibonacci_13_verified :
  green golden 0%nat 0%nat 6 == 13 /\
  green golden 0%nat 0%nat 6 == ck_sum golden 0%nat 0%nat 3 3.
Proof.
  split; [exact green_golden_00_6|exact ck_golden_00_3_3].
Qed.

(** Green function at K=0 is identity for any matrix *)
Lemma green_at_zero_00 : forall M, green M 0%nat 0%nat 0 == 1.
Proof. intro M. vm_compute. reflexivity. Qed.

Lemma green_at_zero_01 : forall M, green M 0%nat 1%nat 0 == 0.
Proof. intro M. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GRAND THEOREM                                                      *)
(* ================================================================== *)

Theorem deep_green_grand_theorem :
  (* 1. Spectral: recurrence from trace/det *)
  (char_p golden == 1 /\ char_q golden == -(1)) /\
  (* 2. Resolvent: generating function analysis *)
  (resolvent_det golden 0 == 1 /\ discriminant golden == 5) /\
  (* 3. Path: sum over paths = propagator *)
  (path_weight golden [0%nat; 0%nat; 0%nat] +
   path_weight golden [0%nat; 1%nat; 0%nat] == green golden 0%nat 0%nat 2) /\
  (* 4. Determinant: Cassini identity *)
  (det2 golden == -(1) /\ is_conservative golden) /\
  (* 5. Chapman-Kolmogorov: propagator composition *)
  green golden 0%nat 0%nat 6 == ck_sum golden 0%nat 0%nat 3 3 /\
  (* 6. Interference: Hadamard vs golden *)
  green hadamard_like 0%nat 1%nat 2 == 0.
Proof.
  split; [exact golden_char|].
  split; [split; [exact resolvent_det_golden_0|exact golden_discriminant]|].
  split; [exact golden_path_sum_K2|].
  split; [split; [exact det_golden|exact golden_is_conservative]|].
  split; [exact ck_golden_00_3_3|exact hadamard_destructive].
Qed.
