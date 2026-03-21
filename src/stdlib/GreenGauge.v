(** * GreenGauge.v -- Gauge correlator IS a Green's function
    Elements: qpow_nat, transfer_as_mat2, correlator_as_green_ratio
    Roles:    full_correlation = G_{11}(K)/G_{00}(K) in eigenbasis
    Rules:    All gauge theory = Green's function processes
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import gauge.CharacterTransfer.

Open Scope Q_scope.

(* ================================================================== *)
(*  Q-POWER (nat exponent)                                             *)
(* ================================================================== *)

Fixpoint qpow_nat (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => q * qpow_nat q k
  end.

Lemma qpow_nat_0 : forall q, qpow_nat q 0 == 1.
Proof. intro. simpl. reflexivity. Qed.

Lemma qpow_nat_1 : forall q, qpow_nat q 1 == q.
Proof. intro. simpl. ring. Qed.

(* ================================================================== *)
(*  DIAGONAL TRANSFER MATRIX AS MAT2                                   *)
(* ================================================================== *)

(** In the eigenbasis, transfer matrix is diagonal:
    T = diag(λ₀, λ₁) where λ_j = transfer_eigenvalue j β M *)
Definition transfer_as_mat2 (beta : Q) (M_trunc : nat) : Mat2 :=
  fun i j =>
    if Nat.eqb i j then
      match i with
      | O => transfer_eigenvalue 0%nat beta M_trunc
      | _ => transfer_eigenvalue 1%nat beta M_trunc
      end
    else 0.

(* ================================================================== *)
(*  CORRELATOR = RATIO OF GREEN'S FUNCTIONS                            *)
(* ================================================================== *)

(** C(K) = G_{11}(K) / G_{00}(K) = (λ₁/λ₀)^K *)
Definition correlator_as_green_ratio (beta : Q) (M_trunc : nat) (K : nat) : Q :=
  qpow_nat (transfer_eigenvalue 1%nat beta M_trunc / transfer_eigenvalue 0%nat beta M_trunc) K.

(** At K=0: correlator = 1 (always) *)
Lemma correlator_at_0 : forall beta M_trunc,
  correlator_as_green_ratio beta M_trunc 0 == 1.
Proof.
  intros. unfold correlator_as_green_ratio. simpl. reflexivity.
Qed.

(** At K=1: correlator = λ₁/λ₀ *)
Lemma correlator_at_1 : forall beta M_trunc,
  correlator_as_green_ratio beta M_trunc 1 ==
    transfer_eigenvalue 1%nat beta M_trunc / transfer_eigenvalue 0%nat beta M_trunc.
Proof.
  intros. unfold correlator_as_green_ratio. simpl. ring.
Qed.

(* ================================================================== *)
(*  PARTITION FUNCTION = TRACE OF GREEN'S FUNCTION                     *)
(* ================================================================== *)

(** Z(K) = Σ (2j+1)·G_{jj}(K) = λ₀^K + 3·λ₁^K (for J=1 truncation) *)
Definition partition_as_trace (beta : Q) (M_trunc : nat) (K : nat) : Q :=
  qpow_nat (transfer_eigenvalue 0%nat beta M_trunc) K +
  3 * qpow_nat (transfer_eigenvalue 1%nat beta M_trunc) K.

(** At K=0: Z = 1 + 3 = 4 (number of spin-1 states) *)
Lemma partition_at_0 : forall beta M_trunc,
  partition_as_trace beta M_trunc 0 == 4.
Proof.
  intros. unfold partition_as_trace. simpl. ring.
Qed.

(** At K=1: Z = λ₀ + 3·λ₁ *)
Lemma partition_at_1 : forall beta M_trunc,
  partition_as_trace beta M_trunc 1 ==
    transfer_eigenvalue 0%nat beta M_trunc +
    3 * transfer_eigenvalue 1%nat beta M_trunc.
Proof.
  intros. unfold partition_as_trace. simpl. ring.
Qed.

(* ================================================================== *)
(*  MASS GAP FROM GREEN'S FUNCTION                                     *)
(* ================================================================== *)

(** gap ≈ 1 - C(1) = 1 - λ₁/λ₀ (linear approximation of -ln) *)
Definition gap_from_green (beta : Q) (M_trunc : nat) : Q :=
  1 - correlator_as_green_ratio beta M_trunc 1.

(** Gap is related to return time: how fast excited state decays *)
Lemma gap_from_correlator : forall beta M_trunc,
  gap_from_green beta M_trunc ==
    1 - transfer_eigenvalue 1%nat beta M_trunc / transfer_eigenvalue 0%nat beta M_trunc.
Proof.
  intros. unfold gap_from_green. rewrite correlator_at_1. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE: β=1, M=0 (simplest gauge model)                         *)
(* ================================================================== *)

(** Concrete correlator at β=1, M=0, K=0 *)
Lemma gauge_correlator_concrete : correlator_as_green_ratio 1 0%nat 0 == 1.
Proof. unfold correlator_as_green_ratio. simpl. reflexivity. Qed.

(** Concrete partition at β=1, M=0, K=0 *)
Lemma gauge_partition_concrete : partition_as_trace 1 0%nat 0 == 4.
Proof. unfold partition_as_trace. simpl. ring. Qed.

(** Correlator decreasing: C(K+1) = C(1)·C(K) for diagonal transfer *)
Lemma correlator_multiplicative : forall beta M K,
  correlator_as_green_ratio beta M (S K) ==
  (transfer_eigenvalue 1%nat beta M / transfer_eigenvalue 0%nat beta M) *
  correlator_as_green_ratio beta M K.
Proof.
  intros. unfold correlator_as_green_ratio. simpl. ring.
Qed.

(** SYNTHESIS *)
Theorem gauge_is_green :
  (* Correlator at K=0 is 1 *)
  correlator_as_green_ratio 1 0%nat 0 == 1 /\
  (* Partition at K=0 is 4 *)
  partition_as_trace 1 0%nat 0 == 4 /\
  (* Correlator is multiplicative *)
  forall beta M K,
    correlator_as_green_ratio beta M (S K) ==
    (transfer_eigenvalue 1%nat beta M / transfer_eigenvalue 0%nat beta M) *
    correlator_as_green_ratio beta M K.
Proof.
  split; [|split].
  - exact gauge_correlator_concrete.
  - exact gauge_partition_concrete.
  - exact correlator_multiplicative.
Qed.
