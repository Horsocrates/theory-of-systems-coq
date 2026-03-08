(** * TimeSeries.v -- Time Series Analysis as ToS Systems

    Theory of Systems -- Verified Standard Library (Batch 6)

    Elements: observations (nat -> Q), windows (list Q)
    Roles:    observation -> DataPoint, window -> SlidingView, trend -> Pattern
    Rules:    moving average computation (constitution), stationarity
    Status:   stationary | trending | seasonal | anomalous

    Connection: ProcessGeneral.v -- time series as GenProcess
    Connection: Statistics.v -- mean, sum_Q for window statistics

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import ProcessGeneral.
From ToS Require Import stdlib.Statistics.

(* ========================================================================= *)
(* CORE DEFINITIONS                                                          *)
(* ========================================================================= *)

(** A time series is a process over Q: nat -> Q *)
Definition TimeSeries := GenProcess Q.

(** Collect k values starting at time t *)
Fixpoint window (ts : TimeSeries) (t k : nat) : list Q :=
  match k with
  | O => []
  | S k' => ts t :: window ts (S t) k'
  end.

(** Moving average over a window of size k starting at t *)
Definition moving_avg (ts : TimeSeries) (k : nat) (t : nat) : Q :=
  mean (window ts t k).

(** The moving average as a time series itself *)
Definition ma_series (ts : TimeSeries) (k : nat) : TimeSeries :=
  fun t => moving_avg ts k t.

(** First difference: ts(t+1) - ts(t) *)
Definition diff (ts : TimeSeries) : TimeSeries :=
  fun t => ts (S t) - ts t.

(** Cumulative sum up to step n *)
Fixpoint cumsum (ts : TimeSeries) (n : nat) : Q :=
  match n with
  | O => ts 0%nat
  | S n' => cumsum ts n' + ts (S n')
  end.

(** Constant time series *)
Definition const_ts (c : Q) : TimeSeries := fun _ => c.

(** Linear time series: a*t + b *)
Definition linear_ts (a b : Q) : TimeSeries :=
  fun t => a * inject_Z (Z.of_nat t) + b.

(** Local power function q^n *)
Fixpoint Qpow_local (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S n' => q * Qpow_local q n'
  end.

(** Exponential decay: c * r^t *)
Definition exp_decay_ts (c r : Q) : TimeSeries :=
  fun t => c * Qpow_local r t.

(** Stationarity of mean: moving average is the same at all times *)
Definition is_stationary_mean (ts : TimeSeries) (k : nat) : Prop :=
  forall t1 t2, moving_avg ts k t1 == moving_avg ts k t2.

(* ========================================================================= *)
(* THEOREMS: window                                                          *)
(* ========================================================================= *)

Lemma window_length : forall (ts : TimeSeries) (t k : nat),
  length (window ts t k) = k.
Proof.
  intros ts t k. generalize dependent t.
  induction k as [|k' IH]; intro t.
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma window_0 : forall (ts : TimeSeries) (t : nat),
  window ts t 0 = [].
Proof. reflexivity. Qed.

Lemma window_1 : forall (ts : TimeSeries) (t : nat),
  window ts t 1 = [ts t].
Proof. intros. simpl. reflexivity. Qed.

(* ========================================================================= *)
(* THEOREMS: const_ts                                                        *)
(* ========================================================================= *)

Lemma const_ts_at : forall (c : Q) (t : nat),
  const_ts c t = c.
Proof. reflexivity. Qed.

Lemma const_ts_window_1 : forall (c : Q) (t : nat),
  window (const_ts c) t 1 = [c].
Proof. intros. unfold const_ts. simpl. reflexivity. Qed.

Lemma const_ts_ma_1 : forall (c : Q) (t : nat),
  moving_avg (const_ts c) 1 t == c.
Proof.
  intros c t.
  unfold moving_avg. rewrite window_1. unfold const_ts.
  apply mean_singleton.
Qed.

(* ========================================================================= *)
(* THEOREMS: diff                                                            *)
(* ========================================================================= *)

Lemma diff_const : forall (c : Q) (t : nat),
  diff (const_ts c) t == 0.
Proof.
  intros c t. unfold diff, const_ts. ring.
Qed.

Lemma diff_linear : forall (a b : Q) (t : nat),
  diff (linear_ts a b) t == a.
Proof.
  intros a b t. unfold diff, linear_ts.
  replace (Z.of_nat (S t)) with (Z.of_nat t + 1)%Z by lia.
  rewrite inject_Z_plus.
  ring.
Qed.

(* ========================================================================= *)
(* THEOREMS: cumsum                                                          *)
(* ========================================================================= *)

Lemma cumsum_0 : forall (ts : TimeSeries),
  cumsum ts 0 = ts 0%nat.
Proof. reflexivity. Qed.

Lemma cumsum_1 : forall (ts : TimeSeries),
  cumsum ts 1 == ts 0%nat + ts 1%nat.
Proof.
  intro ts. simpl. lra.
Qed.

(* ========================================================================= *)
(* THEOREMS: exp_decay                                                       *)
(* ========================================================================= *)

Lemma exp_decay_0 : forall (c r : Q),
  exp_decay_ts c r 0%nat == c.
Proof. intros c r. unfold exp_decay_ts, Qpow_local. ring. Qed.

Lemma exp_decay_1 : forall (c r : Q),
  exp_decay_ts c r 1%nat == c * r.
Proof. intros c r. unfold exp_decay_ts, Qpow_local. ring. Qed.

Lemma exp_decay_2 : forall (c r : Q),
  exp_decay_ts c r 2%nat == c * (r * r).
Proof. intros c r. unfold exp_decay_ts, Qpow_local. ring. Qed.

(* ========================================================================= *)
(* THEOREMS: linear_ts                                                       *)
(* ========================================================================= *)

Lemma linear_ts_0 : forall (a b : Q),
  linear_ts a b 0%nat == b.
Proof. intros a b. unfold linear_ts. simpl. ring. Qed.

Lemma linear_ts_1 : forall (a b : Q),
  linear_ts a b 1%nat == a + b.
Proof. intros a b. unfold linear_ts. simpl. ring. Qed.

(* ========================================================================= *)
(* THEOREMS: stationarity                                                    *)
(* ========================================================================= *)

Lemma const_ts_stationary : forall (c : Q),
  is_stationary_mean (const_ts c) 1.
Proof.
  intros c. unfold is_stationary_mean. intros t1 t2.
  unfold moving_avg. rewrite window_1, window_1.
  unfold const_ts. reflexivity.
Qed.

(* ========================================================================= *)
(* SUMMARY                                                                   *)
(* ========================================================================= *)

(**
  PROVEN (16 Qed):

  Window properties:
    window_length, window_0, window_1

  Constant time series:
    const_ts_at, const_ts_window_1, const_ts_ma_1

  Differentiation:
    diff_const, diff_linear

  Cumulative sum:
    cumsum_0, cumsum_1

  Exponential decay:
    exp_decay_0, exp_decay_1, exp_decay_2

  Linear time series:
    linear_ts_0, linear_ts_1

  Stationarity:
    const_ts_stationary

  AXIOMS: 0 (all proofs constructive)
*)
