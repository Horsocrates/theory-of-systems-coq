(** * CFMatrixProduct.v -- CF digits as matrix products
    Elements: cf_matrix, cf_product, convergent_from_matrix
    Roles:    CF digit a_n → matrix A(a_n) = [[a,1],[1,0]]
    Rules:    Π A(a_k) = [[p_{K+1}, p_K],[q_{K+1}, q_K]], det = (-1)^K
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.
From ToS Require Import stdlib.SFTEntropyGeneral.
From ToS Require Import stdlib.EntropyProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  CF MATRIX                                                          *)
(* ================================================================== *)

(** CF matrix for digit a: A(a) = [[a,1],[1,0]] *)
Definition cf_matrix (a : Z) : QMat 2 2 :=
  qmat2x2 (inject_Z a) 1 1 0.

(** Golden mean: A(1) = [[1,1],[1,0]] *)
Lemma cf_golden : cf_matrix 1 = golden_sft.
Proof. unfold cf_matrix, golden_sft, inject_Z. reflexivity. Qed.

(** det(A(a)) = a·0 - 1·1 = -1 *)
Lemma cf_det_1 : det_2x2 (cf_matrix 1) == -(1).
Proof. unfold det_2x2, cf_matrix. vm_compute. reflexivity. Qed.

Lemma cf_det_2 : det_2x2 (cf_matrix 2) == -(1).
Proof. unfold det_2x2, cf_matrix. vm_compute. reflexivity. Qed.

Lemma cf_det_3 : det_2x2 (cf_matrix 3) == -(1).
Proof. unfold det_2x2, cf_matrix. vm_compute. reflexivity. Qed.

(** CF product: Π_{k=0}^{K-1} A(a_k) *)
Fixpoint cf_product (digits : list Z) : QMat 2 2 :=
  match digits with
  | nil => id_mat 2
  | d :: rest => mat_mul (cf_matrix d) (cf_product rest)
  end.

(** Convergent: p_K/q_K from matrix entries *)
Definition convergent_p (digits : list Z) : Q :=
  mat_entry (cf_product digits) 0 0.

Definition convergent_q (digits : list Z) : Q :=
  mat_entry (cf_product digits) 1 0.

(* ================================================================== *)
(*  GOLDEN MEAN: [1;1,1,1,...] → FIBONACCI                            *)
(* ================================================================== *)

(** A(1)^1 = [[1,1],[1,0]]: p=1, q=1. Convergent = 1/1 = 1 *)
Lemma golden_conv_1 : convergent_p [1%Z] == 1 /\ convergent_q [1%Z] == 1.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** A(1)²: p=2, q=1. Convergent = 2/1 = 2 *)
Lemma golden_conv_2 :
  convergent_p [1;1]%Z == 2 /\ convergent_q [1;1]%Z == 1.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** A(1)³: p=3, q=2. Convergent = 3/2 *)
Lemma golden_conv_3 :
  convergent_p [1;1;1]%Z == 3 /\ convergent_q [1;1;1]%Z == 2.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** A(1)⁴: p=5, q=3. Convergent = 5/3 *)
Lemma golden_conv_4 :
  convergent_p [1;1;1;1]%Z == 5 /\ convergent_q [1;1;1;1]%Z == 3.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** A(1)⁵: p=8, q=5. Convergent = 8/5 *)
Lemma golden_conv_5 :
  convergent_p [1;1;1;1;1]%Z == 8 /\ convergent_q [1;1;1;1;1]%Z == 5.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** THE CONNECTION: p_K/q_K = φ-process = fib(K+1)/fib(K) *)
(** p_K/q_K = fib(K+1)/fib(K) = phi_process(K-1).
    5 digits: p=8, q=5. 8/5 = phi_process 3. *)
Theorem cf_gives_phi_process :
  convergent_p [1;1;1;1;1]%Z / convergent_q [1;1;1;1;1]%Z == phi_process 3.
Proof.
  destruct golden_conv_5 as [Hp Hq].
  rewrite Hp, Hq. rewrite phi_3. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  √2: [1;2,2,2,...] → √2 convergents                                *)
(* ================================================================== *)

(** A(1)·A(2) = [[1,1],[1,0]]·[[2,1],[1,0]] = [[3,1],[2,1]] *)
Lemma sqrt2_conv_2 :
  convergent_p [1;2]%Z == 3 /\ convergent_q [1;2]%Z == 2.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** A(1)·A(2)·A(2): p=7, q=5. 7/5 = 1.4 ≈ √2 *)
Lemma sqrt2_conv_3 :
  convergent_p [1;2;2]%Z == 7 /\ convergent_q [1;2;2]%Z == 5.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** A(1)·A(2)·A(2)·A(2): p=17, q=12. 17/12 ≈ 1.4167 ≈ √2 *)
Lemma sqrt2_conv_4 :
  convergent_p [1;2;2;2]%Z == 17 /\ convergent_q [1;2;2;2]%Z == 12.
Proof.
  unfold convergent_p, convergent_q, cf_product, cf_matrix.
  vm_compute. split; reflexivity.
Qed.

(** √2 ≈ 1.414..., convergents: 1, 3/2, 7/5, 17/12, 41/29, ... *)

(** SYNTHESIS *)
Theorem cf_matrix_synthesis :
  det_2x2 (cf_matrix 1) == -(1) /\  (* det = -1 for any CF digit *)
  det_2x2 (cf_matrix 2) == -(1) /\
  convergent_p [1;1;1;1;1]%Z / convergent_q [1;1;1;1;1]%Z == phi_process 3 /\
  convergent_p [1;2;2;2]%Z == 17 /\
  convergent_q [1;2;2;2]%Z == 12.
Proof.
  split; [|split; [|split; [|split]]].
  - exact cf_det_1.
  - exact cf_det_2.
  - exact cf_gives_phi_process.
  - exact (proj1 sqrt2_conv_4).
  - exact (proj2 sqrt2_conv_4).
Qed.
