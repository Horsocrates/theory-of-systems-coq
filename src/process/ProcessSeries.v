(** * ProcessSeries.v — Series as Process Construction
    Elements: partial sums S_n = a_0 + a_1 + ... + a_n
    Roles:    Cauchy process converging to series value
    Rules:    geometric_series_cauchy, comparison_test from SeriesConvergence.v
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS SERIES — Series as Process Construction                    *)
(*                                                                            *)
(*  A series Σ a_k is the sequence of partial sums S_n = Σ_{k=0}^{n} a_k   *)
(*  Under P4: the series IS the PROCESS {S_n}_{n>=0}                        *)
(*  No completed sum — the process IS the series.                            *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: partial sums S_n                                             *)
(*    Roles:    Cauchy process converging to series value                    *)
(*    Rules:    geometric convergence, comparison test                       *)
(*                                                                            *)
(*  STATUS: 12 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.

(* ================================================================== *)
(*  Part I: Series Process                                               *)
(* ================================================================== *)

(** A series is a process: its partial sums *)
Definition series_process (a : nat -> Q) : RealProcess :=
  partial_sum a.

(** Partial sum unfolds correctly *)
Lemma series_process_zero : forall a,
  series_process a 0%nat == a 0%nat.
Proof. intro a. unfold series_process. simpl. reflexivity. Qed.

Lemma series_process_succ : forall a n,
  series_process a (S n) == series_process a n + a (S n).
Proof.
  intros a n. unfold series_process. simpl. ring.
Qed.

(* ================================================================== *)
(*  Part II: Geometric Series as Process                                 *)
(* ================================================================== *)

(** Geometric series process: S_n = 1 + r + r^2 + ... + r^n *)
Definition geometric_process (r : Q) : RealProcess :=
  series_process (fun k => Qpow r k).

(** Geometric series converges for |r| < 1 *)
Theorem geometric_process_cauchy : forall r,
  0 <= r -> r < 1 ->
  is_Cauchy (geometric_process r).
Proof.
  intros r Hr Hr1.
  unfold geometric_process, series_process.
  (* is_Cauchy and is_cauchy are definitionally equal *)
  exact (geometric_series_cauchy r Hr Hr1).
Qed.

(** Geometric partial sum formula: (1-r) * S_n = 1 - r^(n+1) *)
Lemma geometric_process_formula : forall r n,
  (1 - r) * geometric_process r n == 1 - Qpow r (S n).
Proof.
  intros r n.
  unfold geometric_process, series_process.
  apply geometric_sum_identity.
Qed.

(* ================================================================== *)
(*  Part III: Series Operations                                          *)
(* ================================================================== *)

(** Sum of series: Σ(a+b) = Σa + Σb pointwise *)
Lemma series_process_add : forall a b n,
  series_process (fun k => a k + b k) n ==
  series_process a n + series_process b n.
Proof.
  intros a b n. unfold series_process.
  induction n.
  - simpl. ring.
  - simpl. setoid_rewrite IHn. ring.
Qed.

(** Scale of series: Σ(c*a) = c * Σa pointwise *)
Lemma series_process_scale : forall c a n,
  series_process (fun k => c * a k) n ==
  c * series_process a n.
Proof.
  intros c a n. unfold series_process.
  induction n.
  - simpl. ring.
  - simpl. setoid_rewrite IHn. ring.
Qed.

(** Nonneg terms: partial sums are nondecreasing *)
Lemma series_process_nondecreasing : forall a n,
  (forall k, 0 <= a k) ->
  series_process a n <= series_process a (S n).
Proof.
  intros a n Ha.
  unfold series_process. simpl.
  assert (H := Ha (S n)). lra.
Qed.

(* ================================================================== *)
(*  Part IV: Convergence Tests as Process Properties                     *)
(* ================================================================== *)

(** Comparison test: if 0 <= a_k <= b_k and Σb converges, then Σa converges *)
Theorem series_comparison_cauchy : forall a b,
  (forall n, 0 <= a n) ->
  (forall n, 0 <= b n) ->
  (forall n, a n <= b n) ->
  is_Cauchy (series_process b) ->
  is_Cauchy (series_process a).
Proof.
  intros a b Ha Hb Hab Hcb.
  unfold series_process in *.
  exact (comparison_test a b Ha Hb Hab Hcb).
Qed.

(** Absolute convergence: if |a_k| <= b_k and Σb converges, then Σa converges *)
Theorem series_absolute_cauchy : forall a b,
  (forall n, Qabs (a n) <= b n) ->
  is_Cauchy (series_process b) ->
  is_Cauchy (series_process a).
Proof.
  intros a b Hab Hb.
  unfold series_process in *.
  exact (absolute_convergence a b Hab Hb).
Qed.

(* ================================================================== *)
(*  Part V: E/R/R Pattern                                               *)
(* ================================================================== *)

(** Convergence rate for geometric series *)
Definition series_convergence_rate (r : Q) : Q := r.

Lemma geometric_rate_valid : forall r,
  0 < r -> r < 1 ->
  0 < series_convergence_rate r /\ series_convergence_rate r < 1.
Proof.
  intros r Hr Hr1. unfold series_convergence_rate. auto.
Qed.

(** E/R/R: series as process construction *)
Theorem series_is_process_construction : forall a,
  is_Cauchy (series_process a) ->
  exists proc : RealProcess,
    is_Cauchy proc /\
    (forall n, proc n == partial_sum a n).
Proof.
  intros a Hcauchy.
  exists (series_process a).
  split.
  - exact Hcauchy.
  - intro n. unfold series_process. reflexivity.
Qed.

(** P4: the series IS the process of partial sums *)
(** Each stage n gives a rational approximation S_n *)
(** No completed infinite sum needed *)

(** Tail bound for nonneg geometric series *)
Lemma geometric_tail_bound : forall r n,
  0 <= r -> r < 1 -> ~(r == 0) ->
  geometric_process r (S n) - geometric_process r n == Qpow r (S n).
Proof.
  intros r n Hr Hr1 Hnz.
  unfold geometric_process, series_process. simpl. ring.
Qed.

(** Partial sum nondecreasing for nonneg sequences *)
Lemma series_nonneg_monotone : forall a m n,
  (forall k, 0 <= a k) ->
  (m <= n)%nat ->
  series_process a m <= series_process a n.
Proof.
  intros a m n Ha Hmn.
  unfold series_process.
  induction Hmn.
  - lra.
  - apply Qle_trans with (partial_sum a m0).
    + exact IHHmn.
    + apply partial_sum_nonneg_inc. exact Ha.
Qed.
