(** * TransitionFamily.v -- One-parameter family M(ε) interpolating classical↔quantum
    Elements: M_eps, det_eps, trace_eps, discriminant_eps
    Roles:    ε parametrizes the transition; ε=0 classical, ε=1/2 golden critical, ε=1 maximal
    Rules:    det = -2ε, trace = 2-2ε, disc = (2-2ε)² + 8ε ≥ 4
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  THE TRANSITION FAMILY M(ε)                                         *)
(* ================================================================== *)

(** M(ε) = [[1, 1], [1, 1-2ε]] — interpolates from full shift to golden *)
Definition M_eps (eps : Q) : Mat2 := fun i j =>
  match i, j with
  | O, O => 1
  | O, S O => 1
  | S O, O => 1
  | S O, S O => 1 - 2 * eps
  | _, _ => 0
  end.

(* ================================================================== *)
(*  ALGEBRAIC INVARIANTS                                                *)
(* ================================================================== *)

Definition det_eps (eps : Q) : Q :=
  M_eps eps O O * M_eps eps (S O) (S O) - M_eps eps O (S O) * M_eps eps (S O) O.

Definition trace_eps (eps : Q) : Q :=
  M_eps eps O O + M_eps eps (S O) (S O).

Definition discriminant_eps (eps : Q) : Q :=
  trace_eps eps * trace_eps eps + 4 * (2 * eps).

(* ================================================================== *)
(*  UNIVERSAL FORMULAS                                                  *)
(* ================================================================== *)

Lemma det_formula : forall eps, det_eps eps == -(2) * eps.
Proof. intro eps. unfold det_eps, M_eps. ring. Qed.

Lemma trace_formula : forall eps, trace_eps eps == 2 - 2 * eps.
Proof. intro eps. unfold trace_eps, M_eps. ring. Qed.

Lemma discriminant_formula : forall eps,
  discriminant_eps eps == 4 + 4 * eps * eps.
Proof. intro eps. unfold discriminant_eps, trace_eps, M_eps. ring. Qed.

(* ================================================================== *)
(*  CONCRETE DETERMINANT VALUES                                         *)
(* ================================================================== *)

Lemma det_at_0 : det_eps 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma det_at_quarter : det_eps (1#4) == -(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma det_at_half : det_eps (1#2) == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma det_at_1 : det_eps 1 == -(2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONCRETE DISCRIMINANT VALUES                                        *)
(* ================================================================== *)

Lemma disc_at_0 : discriminant_eps 0 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma disc_at_half : discriminant_eps (1#2) == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma disc_at_1 : discriminant_eps 1 == 8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONCRETE TRACE VALUES                                               *)
(* ================================================================== *)

Lemma trace_at_0 : trace_eps 0 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_at_half : trace_eps (1#2) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_at_1 : trace_eps 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  LINK TO GOLDEN MEAN MATRIX AT ε = 1/2                              *)
(* ================================================================== *)

Lemma M_eps_half_00 : M_eps (1#2) O O == golden O O.
Proof. vm_compute. reflexivity. Qed.

Lemma M_eps_half_01 : M_eps (1#2) O (S O) == golden O (S O).
Proof. vm_compute. reflexivity. Qed.

Lemma M_eps_half_10 : M_eps (1#2) (S O) O == golden (S O) O.
Proof. vm_compute. reflexivity. Qed.

Lemma M_eps_half_11 : M_eps (1#2) (S O) (S O) == golden (S O) (S O).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem transition_family_synthesis :
  (* Universal formulas *)
  (forall eps, det_eps eps == -(2) * eps) /\
  (forall eps, trace_eps eps == 2 - 2 * eps) /\
  (* Key values *)
  det_eps 0 == 0 /\
  det_eps (1#2) == -(1) /\
  det_eps 1 == -(2) /\
  (* Discriminant always ≥ 4 (concrete) *)
  discriminant_eps 0 == 4 /\
  discriminant_eps (1#2) == 5 /\
  discriminant_eps 1 == 8.
Proof.
  split; [exact det_formula|].
  split; [exact trace_formula|].
  split; [exact det_at_0|].
  split; [exact det_at_half|].
  split; [exact det_at_1|].
  split; [exact disc_at_0|].
  split; [exact disc_at_half|exact disc_at_1].
Qed.
