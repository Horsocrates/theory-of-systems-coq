(** * QuaternionFromDistinction.v -- Quaternion units from binary distinction
    Elements: quat_1, quat_i, quat_j, quat_k as 4x4 real matrices
    Roles:    i = connection in each plane; three planes from ternary → H
    Rules:    i^2 = j^2 = k^2 = -I, ij = k, ji = -k
    Status:   Stdlib
    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.DistinctionConnection.
From ToS Require Import stdlib.ComplexOverQ.
Open Scope Q_scope.

(* ================================================================== *)
(*  LOCAL: 4x4 matrix multiplication                                   *)
(* ================================================================== *)

Definition mat4_mul (A B : nat -> nat -> Q) (r c : nat) : Q :=
  fold_left (fun acc m => acc + A r m * B m c) (seq 0%nat 4%nat) 0.

Definition neg_I4 (r c : nat) : Q :=
  match (r, c) with
  | (O, O) => -(1) | (S O, S O) => -(1)
  | (S (S O), S (S O)) => -(1) | (S (S (S O)), S (S (S O))) => -(1)
  | _ => 0
  end.

(* ================================================================== *)
(*  PART I: QUATERNION UNIT MATRICES (left-regular representation)      *)
(* ================================================================== *)

Definition quat_1 (r c : nat) : Q :=
  match (r, c) with
  | (O, O) => 1 | (S O, S O) => 1
  | (S (S O), S (S O)) => 1 | (S (S (S O)), S (S (S O))) => 1
  | _ => 0
  end.

Definition quat_i (r c : nat) : Q :=
  match (r, c) with
  | (O, S O) => -(1) | (S O, O) => 1
  | (S (S O), S (S (S O))) => -(1) | (S (S (S O)), S (S O)) => 1
  | _ => 0
  end.

Definition quat_j (r c : nat) : Q :=
  match (r, c) with
  | (O, S (S O)) => -(1) | (S (S O), O) => 1
  | (S O, S (S (S O))) => 1 | (S (S (S O)), S O) => -(1)
  | _ => 0
  end.

Definition quat_k (r c : nat) : Q :=
  match (r, c) with
  | (O, S (S (S O))) => -(1) | (S (S (S O)), O) => 1
  | (S O, S (S O)) => -(1) | (S (S O), S O) => 1
  | _ => 0
  end.

(* ================================================================== *)
(*  PART II: i^2 = -I (diagonal entries)                                *)
(* ================================================================== *)

Lemma i_sq_00 : mat4_mul quat_i quat_i O O == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma i_sq_11 : mat4_mul quat_i quat_i (S O) (S O) == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma i_sq_22 : mat4_mul quat_i quat_i (S (S O)) (S (S O)) == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma i_sq_33 : mat4_mul quat_i quat_i (S (S (S O))) (S (S (S O))) == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: j^2 = -I, k^2 = -I (spot checks)                        *)
(* ================================================================== *)

Lemma j_sq_00 : mat4_mul quat_j quat_j O O == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma k_sq_00 : mat4_mul quat_k quat_k O O == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: ij = k (spot check entry (0,3))                           *)
(* ================================================================== *)

Lemma ij_eq_k_03 : mat4_mul quat_i quat_j O (S (S (S O))) == quat_k O (S (S (S O))).
Proof. vm_compute. reflexivity. Qed.

Lemma ij_eq_k_12 : mat4_mul quat_i quat_j (S O) (S (S O)) == quat_k (S O) (S (S O)).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART V: ji = -k (spot check)                                       *)
(* ================================================================== *)

Lemma ji_eq_neg_k_03 : mat4_mul quat_j quat_i O (S (S (S O))) == -(quat_k O (S (S (S O)))).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART VI: PLANES FROM SIDES                                          *)
(* ================================================================== *)

Lemma dim1_zero_planes : planes_from_sides 1 = 0%nat.
Proof. reflexivity. Qed.

Lemma dim2_one_plane : planes_from_sides 2 = 1%nat.
Proof. reflexivity. Qed.

Lemma dim3_three_planes : planes_from_sides 3 = 3%nat.
Proof. reflexivity. Qed.

Lemma dim4_six_planes : planes_from_sides 4 = 6%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem quaternion_from_distinction_synthesis :
  planes_from_sides 3 = 3%nat /\
  mat4_mul quat_i quat_i O O == -(1) /\
  mat4_mul quat_j quat_j O O == -(1) /\
  mat4_mul quat_k quat_k O O == -(1).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
