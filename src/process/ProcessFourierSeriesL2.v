(** * ProcessFourierSeriesL2.v — Finite/process-core L²-convergence of a Fourier
      expansion: truncation error = tail energy, monotone, minimal (Part VII, Batch 1 / E-lite)

    Elements: Fourier coefficients cₖ=⟨eₖ,f⟩; partial sum P_K; finite sums; K ≤ N
    Roles:    err(K)=‖f−P_K‖² = tail energy (completeness defect); captured(K) = caught energy
    Rules:    err(K) = ‖f‖² − captured(K); err monotone DECREASING in K; err ≥ 0;
              err(K)=0 ⟺ Parseval; P_K is the minimal-error partial sum

    The finite, honest core of "L²-convergence of the Fourier series" for an orthonormal
    system: the squared error of the K-term partial sum equals the dropped tail energy,
    decreases as K grows, stays nonnegative (Bessel), and vanishes exactly at Parseval
    completeness; moreover the Fourier partial sum is the best K-term approximation. All
    exact over ℚ for a FIXED N, 0 axioms.

    HONEST FRONTIER (the GPT plan-review safeguard): the passage N→∞ — a completed
    Fourier series summing all harmonics — is NOT proved here. It is a role-limit unless
    a separate Cauchy process in K is built and its tail shown to → 0. This file proves
    the finite truncation theory; the infinite series is the P4 boundary (cf. 7.4).

    ============ E/R/R разбор ============
      Rules (L5): err(K)=‖f‖²−captured(K); err убывает по K; err≥0; err=0⟺Парсеваль; P_K минимален.
      Roles (L4): err(K)=роль-дефект (хвостовая энергия); captured(K)=захваченная; полнота=роль-предел err→0.
      Elements  : рациональные cₖ, частичная сумма P_K, конечные суммы, K≤N (L1+P4).
    ДИАГНОСТИКА: конечное усечение — точно над ℚ (0 акс); переход N→∞ / завершённый ряд —
    P4-граница (НЕ здесь, без отдельного Коши-процесса по K).

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum_nonneg *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)
From ToS Require Import process.ProcessL2BesselGeneral. (* resid_norm *)
From ToS Require Import process.ProcessFourierCompression. (* captured, captured_mono *)
From ToS Require Import process.ProcessBestApproximation.  (* best_approx_ge *)

Open Scope Q_scope.

Section ON.

Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

(* Fourier coefficient sequence, partial-sum residual, and the squared error. *)
Local Notation cf := (fun k => seq_inner (e k) f N).
Local Notation Resid K :=
  (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K).
Local Notation errK K := (seq_inner (Resid K) (Resid K) N).

(** Truncation error = total energy − captured energy. *)
Lemma fourier_error_eq : forall K,
  errK K == seq_inner f f N - captured cf K.
Proof.
  intro K. rewrite (resid_norm e N Hon f K). unfold captured. reflexivity.
Qed.

(** Energy balance: total = captured + error. *)
Lemma fourier_energy_balance : forall K,
  seq_inner f f N == captured cf K + errK K.
Proof.
  intro K. pose proof (fourier_error_eq K) as H. lra.
Qed.

(** The truncation error is nonnegative. *)
Lemma fourier_error_nonneg : forall K, 0 <= errK K.
Proof.
  intro K. unfold seq_inner. apply q_sum_nonneg. intro i. apply q_sq_nonneg.
Qed.

(** Adding coefficients never increases the error: err is monotone DECREASING in K. *)
Lemma fourier_error_monotone : forall K K', (K <= K')%nat ->
  errK K' <= errK K.
Proof.
  intros K K' Hle.
  rewrite (fourier_error_eq K'), (fourier_error_eq K).
  pose proof (captured_mono cf K K' Hle) as Hm.
  lra.
Qed.

(** The error vanishes exactly at Parseval completeness. *)
Lemma fourier_error_zero_iff : forall K,
  errK K == 0 <-> captured cf K == seq_inner f f N.
Proof.
  intro K. pose proof (fourier_error_eq K) as H. split; intro Hx; lra.
Qed.

(** The Fourier partial sum is the minimal-error K-term approximation. *)
Theorem fourier_partial_best : forall (a : nat -> Q) (K : nat),
  errK K
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.
Proof.
  intros a K. exact (best_approx_ge e N Hon f a K).
Qed.

End ON.

Print Assumptions fourier_error_eq.
Print Assumptions fourier_error_monotone.
Print Assumptions fourier_partial_best.
