(** * ResolventSynthesis.v -- Resolvent analysis: poles, eigenvalues, comparison
    Elements: resolvent properties, pole detection, eigenvalue connection
    Roles:    Poles of resolvent = eigenvalues; det=0 ↔ eigenvalue
    Rules:    R(z) = (I-zM)^{-1} has poles where det(I-zM)=0
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.GreenSpectral.
From ToS Require Import stdlib.GreenResolvent.

Open Scope Q_scope.

(* ================================================================== *)
(*  POLE DETECTION: resolvent_det = 0 means eigenvalue                 *)
(* ================================================================== *)

(** Definition: z is a pole of the resolvent iff det(I-zM) = 0 *)
Definition is_pole (M : Mat2) (z : Q) : Prop :=
  resolvent_det M z == 0.

(** Full shift has eigenvalue at z=1/2 *)
Lemma full_has_pole_half : is_pole full_mat2 (1#2).
Proof. unfold is_pole. vm_compute. reflexivity. Qed.

(** Golden has no pole at z=0 *)
Lemma golden_no_pole_0 : ~ is_pole golden 0.
Proof.
  unfold is_pole. rewrite resolvent_det_at_zero.
  unfold Qeq. simpl. lia.
Qed.

(** Golden has no pole at z=-1 *)
Lemma golden_no_pole_neg1 : ~ is_pole golden (-(1)).
Proof.
  unfold is_pole. rewrite resolvent_det_golden_neg1.
  unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  RESOLVENT COMPARISON: golden vs full                               *)
(* ================================================================== *)

(** At z=1/2: golden resolvent det = 1/4, full = 0 *)
Lemma resolvent_comparison_half :
  resolvent_det golden (1#2) == (1#4) /\
  resolvent_det full_mat2 (1#2) == 0.
Proof.
  split.
  - exact resolvent_det_golden_half.
  - exact resolvent_det_full_half.
Qed.

(** At z=1: golden det = -1, full det = -1 *)
Lemma resolvent_det_full_1 : resolvent_det full_mat2 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma resolvent_at_1 :
  resolvent_det golden 1 == resolvent_det full_mat2 1.
Proof.
  rewrite resolvent_det_golden_1, resolvent_det_full_1. reflexivity.
Qed.

(* ================================================================== *)
(*  DISCRIMINANT: determines nature of eigenvalues                     *)
(* ================================================================== *)

(** Discriminant = tr^2 - 4*det *)
Definition discriminant (M : Mat2) : Q :=
  char_p M * char_p M - 4 * char_q M.

Lemma golden_discriminant : discriminant golden == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma full_discriminant : discriminant full_mat2 == 4.
Proof. vm_compute. reflexivity. Qed.

(** Positive discriminant means real eigenvalues *)
Lemma golden_discriminant_positive : 0 < discriminant golden.
Proof. rewrite golden_discriminant. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem resolvent_deep_synthesis :
  (* Full shift has pole at z=1/2 *)
  is_pole full_mat2 (1#2) /\
  (* Golden has no pole at z=0 *)
  ~ is_pole golden 0 /\
  (* Both agree at z=1 *)
  resolvent_det golden 1 == resolvent_det full_mat2 1 /\
  (* Golden discriminant = 5 (irrational eigenvalues) *)
  discriminant golden == 5.
Proof.
  split; [exact full_has_pole_half|].
  split; [exact golden_no_pole_0|].
  split; [exact resolvent_at_1|exact golden_discriminant].
Qed.
