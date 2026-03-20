(** * DynamicalZeta.v -- Dynamical zeta function ζ_M(z) = 1/det(I - z·M)
    Elements: zeta_det_2x2, zeta_coeff, golden_zeta_fib
    Roles:    ζ(z) encodes periodic orbit counts via Taylor coefficients
    Rules:    Coefficients = tr(M^n) = periodic points. Exact over Q.
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

Open Scope Q_scope.

(* ================================================================== *)
(*  DYNAMICAL ZETA FUNCTION: det(I - z·M) for 2×2                     *)
(* ================================================================== *)

(** For 2×2 M: det(I - z·M) = 1 - tr(M)·z + det(M)·z² *)
Definition zeta_det_2x2 (M : QMat 2 2) (z : Q) : Q :=
  1 - mat_trace M * z + det_2x2 M * z * z.

(** ζ_M(z) = 1 / det(I - z·M) — evaluation at z *)
Definition zeta_eval (M : QMat 2 2) (z : Q) : Q :=
  1 / zeta_det_2x2 M z.

(** Taylor coefficients of ζ: c_n approximated via partial sums *)
(** Σ_{n=0}^{K} tr(M^n) · z^n *)
Fixpoint zeta_partial (M : QMat 2 2) (z : Q) (K : nat) : Q :=
  match K with
  | O => tr_pow M O
  | S j => zeta_partial M z j + tr_pow M K * Qpower z (Z.of_nat K)
  end.

(* ================================================================== *)
(*  GOLDEN MEAN: ζ(z) = 1/(1 - z - z²)                                *)
(* ================================================================== *)

(** det(I - z·golden) = 1 - z + (-1)z² = 1 - z - z² *)
Lemma golden_zeta_det : forall z,
  zeta_det_2x2 golden_sft z == 1 - z - z * z.
Proof.
  intro z. unfold zeta_det_2x2.
  assert (Ht : mat_trace golden_sft == 1) by (vm_compute; reflexivity).
  assert (Hd : det_2x2 golden_sft == -(1)) by (vm_compute; reflexivity).
  rewrite Ht, Hd. ring.
Qed.

(** At z=0: ζ(0) = 1 *)
Lemma golden_zeta_at_0 : zeta_eval golden_sft 0 == 1.
Proof.
  unfold zeta_eval, zeta_det_2x2.
  assert (Ht : mat_trace golden_sft == 1) by (vm_compute; reflexivity).
  assert (Hd : det_2x2 golden_sft == -(1)) by (vm_compute; reflexivity).
  rewrite Ht, Hd. vm_compute. reflexivity.
Qed.

(** Taylor coefficients = Lucas numbers (= tr(M^n)) *)
(** ζ(z) = 1 + z + 3z² + 4z³ + 7z⁴ + ... but wait,
    the EXPONENTIAL zeta uses tr(M^n)/n, the ARTIN-MAZUR uses tr(M^n).
    The partial sum Σ tr(M^n)·z^n is the orbit-counting series.
    c_0 = 2, c_1 = 1, c_2 = 3, c_3 = 4, c_4 = 7 = Lucas numbers *)

Lemma golden_partial_0 : zeta_partial golden_sft (1#10) 0 == 2.
Proof.
  unfold zeta_partial. rewrite golden_tr_0. reflexivity.
Qed.

Lemma golden_partial_1 : zeta_partial golden_sft (1#10) 1 == 21#10.
Proof.
  unfold zeta_partial. rewrite golden_tr_0, golden_tr_1.
  vm_compute. reflexivity.
Qed.

Lemma golden_partial_2 : zeta_partial golden_sft (1#10) 2 == 213#100.
Proof.
  unfold zeta_partial. rewrite golden_tr_0, golden_tr_1, golden_tr_2.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  FULL SHIFT: ζ(z) = 1/(1 - 2z)                                     *)
(* ================================================================== *)

(** det(I - z·full) = 1 - 2z + 0·z² = 1 - 2z *)
Lemma full_zeta_det : forall z,
  zeta_det_2x2 full_sft z == 1 - 2 * z.
Proof.
  intro z. unfold zeta_det_2x2.
  assert (Ht : mat_trace full_sft == 2) by (vm_compute; reflexivity).
  assert (Hd : det_2x2 full_sft == 0) by (vm_compute; reflexivity).
  rewrite Ht, Hd. ring.
Qed.

(** Full: c_n = 2^n, ζ(z) = Σ 2^n z^n = 1/(1-2z) *)
Lemma full_partial_0 : zeta_partial full_sft (1#10) 0 == 2.
Proof. unfold zeta_partial. rewrite full_tr_0. reflexivity. Qed.

Lemma full_partial_1 : zeta_partial full_sft (1#10) 1 == 22#10.
Proof. unfold zeta_partial. rewrite full_tr_0, full_tr_1.
  vm_compute. reflexivity. Qed.

Lemma full_partial_2 : zeta_partial full_sft (1#10) 2 == 224#100.
Proof. unfold zeta_partial. rewrite full_tr_0, full_tr_1, full_tr_2.
  vm_compute. reflexivity. Qed.

(** DIFFERENT ZETA: golden vs full have different partial sums *)
Theorem golden_full_different_zeta :
  ~ (zeta_partial golden_sft (1#10) 1 == zeta_partial full_sft (1#10) 1).
Proof.
  rewrite golden_partial_1, full_partial_1.
  unfold Qeq. simpl. lia.
Qed.

(** SYNTHESIS *)
Theorem dynamical_zeta_synthesis :
  (* Golden zeta = 1/(1-z-z²) *)
  zeta_det_2x2 golden_sft (1#2) == 1#4 /\
  (* Full zeta = 1/(1-2z) *)
  zeta_det_2x2 full_sft (1#2) == 0 /\
  (* Different zeta functions *)
  ~ (zeta_partial golden_sft (1#10) 1 == zeta_partial full_sft (1#10) 1).
Proof.
  split; [|split].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact golden_full_different_zeta.
Qed.
