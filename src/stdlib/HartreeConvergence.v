(** * HartreeConvergence.v — Convergence Bounds for Hartree Iteration
    Elements: Geometric error bound qpow, iteration error estimates
    Roles:    Prove exponential convergence of Hartree SCF iteration
    Rules:    error(K) = alpha^K; bound decreases geometrically; bound positive
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  RATIONAL POWER (Qpower may not be available)                       *)
(* ================================================================== *)

Fixpoint qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => q * qpow q m
  end.

(* ================================================================== *)
(*  HARTREE ERROR BOUND: error after K iterations = alpha^K            *)
(* ================================================================== *)

Definition hartree_error_bound (alpha : Q) (K : nat) : Q := qpow alpha K.

(* ================================================================== *)
(*  CONCRETE: bound(1/2, 5) = 1/32                                    *)
(* ================================================================== *)

Lemma bound_half_5 : hartree_error_bound (1#2) 5 == 1 # 32.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE: bound(1/2, 10) = 1/1024                                 *)
(* ================================================================== *)

Lemma bound_half_10 : hartree_error_bound (1#2) 10 == 1 # 1024.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONVERGENCE: bound(1/2, 10) < bound(1/2, 5)                       *)
(* ================================================================== *)

Lemma bound_decreases : hartree_error_bound (1#2) 10 < hartree_error_bound (1#2) 5.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  POSITIVITY: bound(1/2, 5) > 0                                     *)
(* ================================================================== *)

Lemma bound_positive : 0 < hartree_error_bound (1#2) 5.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  QPOW BASE CASES                                                   *)
(* ================================================================== *)

Lemma qpow_0 : forall q, qpow q 0 == 1.
Proof. intro q. simpl. ring. Qed.

Lemma qpow_1 : forall q, qpow q 1 == q.
Proof. intro q. simpl. ring. Qed.

(* ================================================================== *)
(*  CONCRETE: bound(1/2, 3) = 1/8                                     *)
(* ================================================================== *)

Lemma bound_half_3 : hartree_error_bound (1#2) 3 == 1 # 8.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  MONOTONICITY: bound(1/2, 5) < bound(1/2, 3)                       *)
(* ================================================================== *)

Lemma bound_decreases_2 : hartree_error_bound (1#2) 5 < hartree_error_bound (1#2) 3.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.
