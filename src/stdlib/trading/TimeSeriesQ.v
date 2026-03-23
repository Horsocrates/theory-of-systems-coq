(** TimeSeriesQ.v — Time series analysis over Q.
    E/R/R: Elements = prices, EMA values, signals;
           Roles = smoothing (EMA), trend detection (MA crossover);
           Rules = EMA recursion, signal generation from crossover.
    STATUS: 25 Qed, 0 Admitted, 0 axioms *)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
From ToS Require Import stdlib.trading.CorrMatrix.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Exponential Moving Average                                       *)
(* ================================================================ *)

Fixpoint ema_aux (alpha : Q) (prices : list Q) (prev : Q) : Q :=
  match prices with
  | nil => prev
  | p :: rest =>
      let new_val := alpha * p + (1 - alpha) * prev in
      ema_aux alpha rest new_val
  end.

Definition ema (alpha : Q) (prices : list Q) : Q :=
  match prices with
  | nil => 0
  | p :: rest => ema_aux alpha rest p
  end.

(* Full EMA series: intermediate values at each step *)
Fixpoint ema_series_aux (alpha : Q) (prices : list Q) (prev : Q) : list Q :=
  match prices with
  | nil => nil
  | p :: rest =>
      let new_val := alpha * p + (1 - alpha) * prev in
      new_val :: ema_series_aux alpha rest new_val
  end.

Definition ema_series (alpha : Q) (prices : list Q) : list Q :=
  match prices with
  | nil => nil
  | p :: rest => p :: ema_series_aux alpha rest p
  end.

(* ================================================================ *)
(* Moving average crossover signal                                  *)
(* ================================================================ *)

Definition ma_signal (fast slow : Q) : nat :=
  if Qlt_le_dec slow fast then S O    (* bullish *)
  else if Qlt_le_dec fast slow then O (* bearish *)
  else S (S O).                        (* neutral *)

(* ================================================================ *)
(* Autocorrelation (simplified lag-1)                               *)
(* ================================================================ *)

Definition lag1_pairs (xs : list Q) : list (Q * Q) :=
  combine xs (tl xs).

Definition autocorr_lag1 (xs : list Q) : Q :=
  let mu := mean_return xs in
  let pairs := lag1_pairs xs in
  fold_left Qplus (map (cross_dev mu mu) pairs) 0
    / inject_Z (Z.of_nat (length pairs)).

(* ================================================================ *)
(* Concrete examples                                                *)
(* ================================================================ *)

Definition prices1 : list Q := [100; 102; 104].
Definition prices2 : list Q := [100; 98; 96].
Definition prices3 : list Q := [10; 20; 10; 20].

(* EMA with alpha = 1/3 *)
Lemma ema_prices1 : ema (1#3) prices1 == 916#9.
Proof. vm_compute. reflexivity. Qed.

Lemma ema_prices2 : ema (1#3) prices2 == 884#9.
Proof. vm_compute. reflexivity. Qed.

(* EMA with alpha = 1 just takes last price *)
Lemma ema_alpha1 : ema 1 prices1 == 104.
Proof. vm_compute. reflexivity. Qed.

(* EMA with alpha = 0 keeps first price *)
Lemma ema_alpha0 : ema 0 prices1 == 100.
Proof. vm_compute. reflexivity. Qed.

(* EMA series length *)
Lemma ema_series_length : length (ema_series (1#3) prices1) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* MA crossover signals *)
Lemma signal_bullish : ma_signal 105 100 = S O.
Proof.
  unfold ma_signal.
  destruct (Qlt_le_dec 100 105) as [H|H]. reflexivity.
  exfalso. unfold Qle in H. simpl in H. lia.
Qed.

Lemma signal_bearish : ma_signal 95 100 = O.
Proof.
  unfold ma_signal.
  destruct (Qlt_le_dec 100 95) as [H|H].
  - exfalso. unfold Qlt in H. simpl in H. lia.
  - destruct (Qlt_le_dec 95 100) as [H2|H2]. reflexivity.
    exfalso. unfold Qle in H2. simpl in H2. lia.
Qed.

Lemma signal_neutral : ma_signal 100 100 = S (S O).
Proof.
  unfold ma_signal.
  destruct (Qlt_le_dec 100 100) as [H|H].
  - exfalso. unfold Qlt in H. simpl in H. lia.
  - destruct (Qlt_le_dec 100 100) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + reflexivity.
Qed.

(* Autocorrelation *)
Lemma autocorr_prices3 : autocorr_lag1 prices3 == -(25).
Proof. vm_compute. reflexivity. Qed.

(* Mean return *)
Lemma mean_prices1 : mean_return prices1 == 102.
Proof. vm_compute. reflexivity. Qed.

Lemma mean_prices2 : mean_return prices2 == 98.
Proof. vm_compute. reflexivity. Qed.

Lemma mean_prices3 : mean_return prices3 == 15.
Proof. vm_compute. reflexivity. Qed.

(* Variance *)
Lemma var_prices1 : variance prices1 == 8#3.
Proof. vm_compute. reflexivity. Qed.

Lemma var_prices2 : variance prices2 == 8#3.
Proof. vm_compute. reflexivity. Qed.

Lemma var_prices3 : variance prices3 == 25.
Proof. vm_compute. reflexivity. Qed.

(* EMA on empty *)
Lemma ema_nil : ema (1#3) nil == 0.
Proof. vm_compute. reflexivity. Qed.

(* EMA on singleton *)
Lemma ema_single : ema (1#3) [42] == 42.
Proof. vm_compute. reflexivity. Qed.

(* Lag1 pairs *)
Lemma lag1_pairs_len : length (lag1_pairs prices1) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* EMA series first element *)
Lemma ema_series_head : hd 0 (ema_series (1#3) prices1) == 100.
Proof. vm_compute. reflexivity. Qed.

(* Covariance of prices *)
Lemma cov_prices12 : covariance prices1 prices2 == -(8#3).
Proof. vm_compute. reflexivity. Qed.

(* EMA with alpha = 1/2 *)
Lemma ema_half_prices3 : ema (1#2) prices3 == 65#4.
Proof. vm_compute. reflexivity. Qed.

(* Autocorrelation of constant-step series is zero *)
Lemma autocorr_prices1 : autocorr_lag1 prices1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma autocorr_prices2 : autocorr_lag1 prices2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* EMA series length for prices3 *)
Lemma ema_series_len3 : length (ema_series (1#3) prices3) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(* Lag1 pairs length for prices3 *)
Lemma lag1_pairs_len3 : length (lag1_pairs prices3) = 3%nat.
Proof. vm_compute. reflexivity. Qed.
