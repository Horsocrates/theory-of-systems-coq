(** * GreenDeterminant.v -- Determinant of matrix powers (Cassini identity)
    Elements: det2, is_conservative, is_dissipative, is_expanding
    Roles:    det(M^K) = det(M)^K; Cassini = det(golden^K) = (-1)^K
    Rules:    Conservation laws from det; det classifies dynamics type
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  DETERMINANT FOR 2x2                                                *)
(* ================================================================== *)

Definition det2 (M : Mat2) : Q :=
  M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 1%nat 0%nat.

(** Golden: det = -1 *)
Lemma det_golden : det2 golden == -(1).
Proof. vm_compute. reflexivity. Qed.

(** Full shift: det = 0 *)
Lemma det_full : det2 full_mat2 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Identity: det = 1 *)
Lemma det_id : det2 mat2_id == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CASSINI IDENTITY: det(golden^K) = (-1)^K                           *)
(* ================================================================== *)

(** Qpow local definition *)
Fixpoint qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => q * qpow q k
  end.

Lemma cassini_1 : det2 (mat2_pow golden 1) == qpow (-(1)) 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_2 : det2 (mat2_pow golden 2) == qpow (-(1)) 2.
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_3 : det2 (mat2_pow golden 3) == qpow (-(1)) 3.
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_4 : det2 (mat2_pow golden 4) == qpow (-(1)) 4.
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_5 : det2 (mat2_pow golden 5) == qpow (-(1)) 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  HADAMARD-LIKE: det = -2                                            *)
(* ================================================================== *)

Definition hadamard_like : Mat2 := fun i j =>
  match i, j with
  | O, O => 1   | O, S O => 1
  | S O, O => 1 | S O, S O => -(1)
  | _, _ => 0
  end.

Lemma det_hadamard : det2 hadamard_like == -(2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DYNAMICS CLASSIFICATION                                            *)
(* ================================================================== *)

Definition is_conservative (M : Mat2) : Prop := Qabs (det2 M) == 1.
Definition is_dissipative (M : Mat2) : Prop := Qabs (det2 M) < 1.
Definition is_expanding (M : Mat2) : Prop := 1 < Qabs (det2 M).

Lemma golden_is_conservative : is_conservative golden.
Proof.
  unfold is_conservative.
  assert (Hd : det2 golden == -(1)) by (exact det_golden).
  rewrite Hd. vm_compute. reflexivity.
Qed.

(** Cassini explicit values: F(K)*F(K) - F(K-1)*F(K+1) = (-1)^K *)
Lemma cassini_explicit_3 :
  green golden 0%nat 0%nat 3 * green golden 0%nat 0%nat 3 -
  green golden 0%nat 0%nat 2 * green golden 0%nat 0%nat 4 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_explicit_4 :
  green golden 0%nat 0%nat 4 * green golden 0%nat 0%nat 4 -
  green golden 0%nat 0%nat 3 * green golden 0%nat 0%nat 5 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_expanding : is_expanding hadamard_like.
Proof.
  unfold is_expanding.
  assert (Hd : det2 hadamard_like == -(2)) by (exact det_hadamard).
  rewrite Hd. vm_compute. reflexivity.
Qed.

Lemma full_is_dissipative : is_dissipative full_mat2.
Proof.
  unfold is_dissipative.
  assert (Hd : det2 full_mat2 == 0) by (exact det_full).
  rewrite Hd. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem determinant_synthesis :
  (* Golden det = -1 *)
  det2 golden == -(1) /\
  (* Cassini at K=5 *)
  det2 (mat2_pow golden 5) == qpow (-(1)) 5 /\
  (* Full det = 0 *)
  det2 full_mat2 == 0 /\
  (* Hadamard det = -2 *)
  det2 hadamard_like == -(2) /\
  (* Golden is conservative *)
  is_conservative golden.
Proof.
  split; [exact det_golden|].
  split; [exact cassini_5|].
  split; [exact det_full|].
  split; [exact det_hadamard|exact golden_is_conservative].
Qed.
