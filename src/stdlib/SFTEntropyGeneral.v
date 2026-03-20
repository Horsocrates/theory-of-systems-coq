(** * SFTEntropyGeneral.v -- General SFT entropy via tr(M^K)
    Elements: mat_pow, tr_pow, h_sft_process, even_shift matrix
    Roles:    tr(M^K) = exact integer for integer M; h_K = ln(tr(M^K))/K
    Rules:    General entropy process for ANY SFT via matrix power trace
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
From ToS Require Import stdlib.LyapunovProcess.
From ToS Require Import stdlib.EntropyProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  MATRIX POWER                                                       *)
(* ================================================================== *)

Fixpoint mat_pow {n} (M : QMat n n) (k : nat) : QMat n n :=
  match k with
  | O => id_mat n
  | S j => mat_mul M (mat_pow M j)
  end.

(** Trace of matrix power: tr(M^K) *)
Definition tr_pow {n} (M : QMat n n) (k : nat) : Q :=
  mat_trace (mat_pow M k).

(* ================================================================== *)
(*  GOLDEN MEAN SFT: M = [[1,1],[1,0]]                                *)
(* ================================================================== *)

Definition golden_sft : QMat 2 2 := qmat2x2 1 1 1 0.

(** tr(M^K) = fib(K+2) for golden mean.
    tr(M^0) = tr(I) = 2
    tr(M^1) = 1 + 0 = 1
    tr(M^2) = tr([[2,1],[1,1]]) = 2 + 1 = 3
    tr(M^3) = tr([[3,2],[2,1]]) = 3 + 1 = 4? No...
    Actually: M^2 = [[1,1],[1,0]]·[[1,1],[1,0]] = [[2,1],[1,1]], tr=3
    M^3 = M·M^2 = [[1,1],[1,0]]·[[2,1],[1,1]] = [[3,2],[2,1]], tr=4
    M^4 = M·M^3 = [[1,1],[1,0]]·[[3,2],[2,1]] = [[5,3],[3,2]], tr=7
    These are tr(M^K) = F(K+2) + F(K) = L(K) (Lucas numbers!) *)

Lemma golden_tr_0 : tr_pow golden_sft 0 == 2.
Proof. unfold tr_pow, mat_pow, golden_sft. vm_compute. reflexivity. Qed.

Lemma golden_tr_1 : tr_pow golden_sft 1 == 1.
Proof. unfold tr_pow, mat_pow, golden_sft. vm_compute. reflexivity. Qed.

Lemma golden_tr_2 : tr_pow golden_sft 2 == 3.
Proof. unfold tr_pow, mat_pow, golden_sft. vm_compute. reflexivity. Qed.

Lemma golden_tr_3 : tr_pow golden_sft 3 == 4.
Proof. unfold tr_pow, mat_pow, golden_sft. vm_compute. reflexivity. Qed.

Lemma golden_tr_4 : tr_pow golden_sft 4 == 7.
Proof. unfold tr_pow, mat_pow, golden_sft. vm_compute. reflexivity. Qed.

Lemma golden_tr_5 : tr_pow golden_sft 5 == 11.
Proof. unfold tr_pow, mat_pow, golden_sft. vm_compute. reflexivity. Qed.

(** tr(M^K) = Lucas numbers: 2, 1, 3, 4, 7, 11, 18, 29, ... *)

(* ================================================================== *)
(*  FULL SHIFT SFT: M = [[1,1],[1,1]]                                 *)
(* ================================================================== *)

Definition full_sft : QMat 2 2 := qmat2x2 1 1 1 1.

(** tr(M^K) = 2^K for full shift (eigenvalues 2 and 0) *)
Lemma full_tr_0 : tr_pow full_sft 0 == 2.
Proof. unfold tr_pow, mat_pow, full_sft. vm_compute. reflexivity. Qed.

Lemma full_tr_1 : tr_pow full_sft 1 == 2.
Proof. unfold tr_pow, mat_pow, full_sft. vm_compute. reflexivity. Qed.

Lemma full_tr_2 : tr_pow full_sft 2 == 4.
Proof. unfold tr_pow, mat_pow, full_sft. vm_compute. reflexivity. Qed.

Lemma full_tr_3 : tr_pow full_sft 3 == 8.
Proof. unfold tr_pow, mat_pow, full_sft. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SFT ENTROPY PROCESS: h_K = ln(tr(M^K)) / K via Padé               *)
(* ================================================================== *)

(** For general SFT: h_K uses Padé for ln *)
Definition h_sft_process {n} (M : QMat n n) (K : nat) : Q :=
  match K with
  | O => 0
  | S j =>
    let t := tr_pow M K in
    let ln_t := 2 * (t - 1) / (t + 1) in
    ln_t / inject_Z (Z.of_nat K)
  end.

(** Golden: h_1 = ln(1)/1 via Padé = 0 (tr=1, ln(1)=0) *)
Lemma golden_h_1 : h_sft_process golden_sft 1 == 0.
Proof.
  unfold h_sft_process, tr_pow, mat_pow, golden_sft.
  vm_compute. reflexivity.
Qed.

(** Golden: h_2 = ln(3)/2 via Padé = (2·2/4)/2 = 1/2 *)
Lemma golden_h_2 : h_sft_process golden_sft 2 == 1#2.
Proof.
  unfold h_sft_process, tr_pow, mat_pow, golden_sft.
  vm_compute. reflexivity.
Qed.

(** Full: h_1 = ln(2)/1 via Padé = 2/3 *)
Lemma full_h_1 : h_sft_process full_sft 1 == 2#3.
Proof.
  unfold h_sft_process, tr_pow, mat_pow, full_sft.
  vm_compute. reflexivity.
Qed.

(** Full: h_2 = ln(4)/2 via Padé = (2·3/5)/2 = 3/5 *)
Lemma full_h_2 : h_sft_process full_sft 2 == 3#5.
Proof.
  unfold h_sft_process, tr_pow, mat_pow, full_sft.
  vm_compute. reflexivity.
Qed.

(** Golden < Full at step 2 *)
Theorem golden_less_full_sft :
  h_sft_process golden_sft 2 < h_sft_process full_sft 2.
Proof.
  rewrite golden_h_2, full_h_2. lra.
Qed.

(** SYNTHESIS *)
Theorem sft_entropy_synthesis :
  (* tr(M^K) exact: golden Lucas, full powers of 2 *)
  tr_pow golden_sft 4 == 7 /\
  tr_pow full_sft 3 == 8 /\
  (* Entropy process: distinguishable at finite step *)
  h_sft_process golden_sft 2 < h_sft_process full_sft 2 /\
  (* Full shift h_1 = ln(2) approx *)
  h_sft_process full_sft 1 == 2#3.
Proof.
  split; [|split; [|split]].
  - exact golden_tr_4.
  - exact full_tr_3.
  - exact golden_less_full_sft.
  - exact full_h_1.
Qed.
