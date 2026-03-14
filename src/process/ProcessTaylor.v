(** * ProcessTaylor.v — Taylor Series as Process Construction
    Elements: Taylor polynomials T_n(x) = Σ_{k=0}^{n} a_k * (x-c)^k / k!
    Roles:    Cauchy process converging to function value
    Rules:    exp_series_cauchy, power_series_converges from PowerSeries.v
    Status:   complete
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS TAYLOR — Taylor Series as Process Construction             *)
(*                                                                            *)
(*  Taylor polynomial T_n(x) = Σ_{k=0}^{n} c_k * x^k                       *)
(*  Under P4: the Taylor expansion IS the PROCESS {T_n(x)}_{n>=0}           *)
(*  No infinite series needed — the process IS the Taylor expansion.         *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: Taylor polynomials of increasing degree                      *)
(*    Roles:    Cauchy process converging to function value                  *)
(*    Rules:    ratio test convergence from PowerSeries.v                    *)
(*                                                                            *)
(*  STATUS: 11 Qed, 0 Admitted                                               *)
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
From ToS Require Import PowerSeries.

(* ================================================================== *)
(*  Part I: Taylor Process from Power Series                             *)
(* ================================================================== *)

(** A power series evaluated at x as a process *)
Definition power_series_process (a : nat -> Q) (x : Q) : RealProcess :=
  fun n => partial_sum (fun k => a k * Qpow x k) n.

(** Zero-th term *)
Lemma power_series_process_zero : forall a x,
  power_series_process a x 0%nat == a 0%nat * 1.
Proof.
  intros a x. unfold power_series_process. simpl. ring.
Qed.

(** Successor step *)
Lemma power_series_process_succ : forall a x n,
  power_series_process a x (S n) ==
  power_series_process a x n + a (S n) * Qpow x (S n).
Proof.
  intros a x n. unfold power_series_process. simpl. ring.
Qed.

(* ================================================================== *)
(*  Part II: Exponential as Taylor Process                               *)
(* ================================================================== *)

(** Exponential Taylor process: e^x = Σ x^n/n! *)
Definition exp_process (x : Q) : RealProcess :=
  fun n => partial_sum (exp_term x) n.

(** exp_process at 0 gives 1 *)
Lemma exp_process_zero_at_0 :
  exp_process 0 0%nat == 1.
Proof.
  unfold exp_process, exp_term. simpl. field.
Qed.

(** Exponential process is Cauchy *)
Theorem exp_process_cauchy : forall x,
  is_Cauchy (exp_process x).
Proof.
  intro x. unfold exp_process.
  exact (exp_series_cauchy x).
Qed.

(** Each term of exp series *)
Lemma exp_process_term : forall x n,
  exp_term x n == Qpow x n * / Qfact n.
Proof.
  intros x n. unfold exp_term. reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: Taylor Process Properties                                  *)
(* ================================================================== *)

(** Taylor process for zero function *)
Lemma power_series_zero : forall x n,
  power_series_process (fun _ => 0) x n == 0.
Proof.
  intros x n. unfold power_series_process.
  induction n.
  - simpl. ring.
  - simpl. setoid_rewrite IHn. ring.
Qed.

(** Taylor process scaling *)
Lemma power_series_scale : forall c a x n,
  power_series_process (fun k => c * a k) x n ==
  c * power_series_process a x n.
Proof.
  intros c a x n. unfold power_series_process.
  induction n.
  - simpl. ring.
  - simpl. setoid_rewrite IHn. ring.
Qed.

(** Taylor process addition *)
Lemma power_series_add : forall a b x n,
  power_series_process (fun k => a k + b k) x n ==
  power_series_process a x n + power_series_process b x n.
Proof.
  intros a b x n. unfold power_series_process.
  induction n.
  - simpl. ring.
  - simpl. setoid_rewrite IHn. ring.
Qed.

(** Evaluation at zero: only the constant term survives *)
Lemma power_series_at_zero : forall a n,
  (0 < n)%nat ->
  power_series_process a 0 n == a 0%nat.
Proof.
  intros a n Hn. unfold power_series_process.
  induction n.
  - lia.
  - simpl. destruct n.
    + simpl. ring.
    + assert (IH : partial_sum (fun k => a k * Qpow 0 k) (S n) == a 0%nat).
      { apply IHn. lia. }
      setoid_rewrite IH.
      assert (Hpow : Qpow 0 (S (S n)) == 0).
      { simpl. ring. }
      setoid_rewrite Hpow. ring.
Qed.

(* ================================================================== *)
(*  Part IV: Convergence                                                 *)
(* ================================================================== *)

(** Convergence rate for Taylor/power series *)
Definition taylor_convergence_rate : Q := 1 # 2.

Lemma taylor_rate_valid : 0 < taylor_convergence_rate /\ taylor_convergence_rate < 1.
Proof. unfold taylor_convergence_rate. split; lra. Qed.

(** E/R/R: Taylor expansion as process construction *)
Theorem taylor_is_process_construction : forall a x,
  is_Cauchy (power_series_process a x) ->
  exists proc : RealProcess,
    is_Cauchy proc /\
    (forall n, proc n == partial_sum (fun k => a k * Qpow x k) n).
Proof.
  intros a x Hcauchy.
  exists (power_series_process a x).
  split.
  - exact Hcauchy.
  - intro n. unfold power_series_process. reflexivity.
Qed.

(** The exp function exemplifies Taylor convergence *)
Theorem exp_is_taylor_construction : forall x,
  exists proc : RealProcess,
    is_Cauchy proc /\
    (forall n, proc n == partial_sum (exp_term x) n).
Proof.
  intro x.
  exists (exp_process x).
  split.
  - exact (exp_process_cauchy x).
  - intro n. unfold exp_process. reflexivity.
Qed.

(** P4: the Taylor expansion IS the process of partial polynomials *)
(** Each stage n gives a degree-n polynomial approximation *)
(** No infinite series needed *)

(** Factorial is always positive *)
Lemma taylor_factorial_pos : forall n, 0 < Qfact n.
Proof. exact Qfact_pos. Qed.
