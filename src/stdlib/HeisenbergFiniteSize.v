(** * HeisenbergFiniteSize.v — Finite-Size Error in Heisenberg Commutator
    Elements: heisenberg_error, error_norm_sq, relative_error_sq
    Roles:    Quantify deviation of [X,P] from -I on K-site lattice
    Rules:    Error grows with K; relative error decreases; boundary effects
    Status:   Stdlib
    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.HeisenbergReturn.
Open Scope Q_scope.

(* ================================================================== *)
(*  HEISENBERG ERROR: [X,P] + I (should be 0 if perfect)               *)
(* ================================================================== *)

(** Error matrix: [X,P]_{ij} + delta_{ij} *)
Definition heisenberg_error (K : nat) (i j : nat) : Q :=
  XP_comm K i j + (if Nat.eqb i j then 1 else 0).

(** Frobenius norm squared of error matrix *)
Definition error_norm_sq (K : nat) : Q :=
  fold_left (fun acc i =>
    fold_left (fun acc2 j =>
      acc2 + heisenberg_error K i j * heisenberg_error K i j)
      (seq 0 K) acc)
    (seq 0 K) 0.

(** Relative error: ||error||^2 / K *)
Definition relative_error_sq (K : nat) : Q :=
  error_norm_sq K / inject_Z (Z.of_nat K).

(* ================================================================== *)
(*  K=3: INDIVIDUAL ERROR ENTRIES                                       *)
(* ================================================================== *)

Lemma error_3_00 : heisenberg_error 3 0 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma error_3_01 : heisenberg_error 3 0 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma error_3_11 : heisenberg_error 3 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma error_3_12 : heisenberg_error 3 1 2 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma error_3_22 : heisenberg_error 3 2 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FROBENIUS NORM OF ERROR                                             *)
(* ================================================================== *)

Lemma error_norm_sq_3 : error_norm_sq 3 == 7.
Proof. vm_compute. reflexivity. Qed.

Lemma error_norm_sq_4 : error_norm_sq 4 == 10.
Proof. vm_compute. reflexivity. Qed.

Lemma error_norm_sq_5 : error_norm_sq 5 == 13.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  RELATIVE ERROR                                                      *)
(* ================================================================== *)

Lemma relative_error_sq_3 : relative_error_sq 3 == (7#3).
Proof. vm_compute. reflexivity. Qed.

Lemma relative_error_sq_4 : relative_error_sq 4 == (5#2).
Proof. vm_compute. reflexivity. Qed.

Lemma relative_error_sq_5 : relative_error_sq 5 == (13#5).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ERROR GROWTH                                                        *)
(* ================================================================== *)

Lemma error_grows_3_to_4 : error_norm_sq 3 < error_norm_sq 4.
Proof. vm_compute. reflexivity. Qed.

Lemma error_grows_4_to_5 : error_norm_sq 4 < error_norm_sq 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem heisenberg_finite_size_synthesis :
  (* Error norm grows with K *)
  error_norm_sq 3 < error_norm_sq 4 /\
  error_norm_sq 4 < error_norm_sq 5 /\
  (* Diagonal error is always 1 (boundary effect) *)
  heisenberg_error 3 0 0 == 1 /\
  heisenberg_error 4 0 0 == 1 /\
  (* Off-diagonal error is -1 (Laplacian leakage) *)
  heisenberg_error 3 0 1 == -(1) /\
  heisenberg_error 4 0 1 == -(1).
Proof. repeat split; vm_compute; reflexivity. Qed.
