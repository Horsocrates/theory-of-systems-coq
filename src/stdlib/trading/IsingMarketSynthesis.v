(** * IsingMarketSynthesis.v — Synthesis of Ising-Market correspondence
    Elements: transfer matrix, partition function, eigenvalue regimes;
    Roles:    unify Ising model mapping with partition function analysis;
    Rules:    combined theorems for Direction 1.
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
From ToS Require Import stdlib.trading.IsingMarketMap.
From ToS Require Import stdlib.trading.MarketPartitionFunction.
Open Scope Q_scope.

(* ===== Cross-file consistency ===== *)

Lemma trending_regime_consistent :
  IsingMarketMap.market_lambda2 (4#5) == 3#5 /\
  MarketPartitionFunction.market_Z (4#5) 1 == 8#5.
Proof.
  split.
  - exact trending_lambda2.
  - exact Z_trending_1.
Qed.

Lemma random_regime_consistent :
  IsingMarketMap.market_lambda2 (1#2) == 0 /\
  (forall N, (0 < N)%nat -> MarketPartitionFunction.market_Z (1#2) N == 1).
Proof.
  split.
  - exact random_lambda2.
  - exact Z_random_any.
Qed.

(* ===== Direction 1 key results ===== *)

Lemma three_regimes_classified :
  IsingMarketMap.market_lambda2 (4#5) == 3#5 /\
  IsingMarketMap.market_lambda2 (1#2) == 0 /\
  IsingMarketMap.market_lambda2 (1#5) == -(3#5).
Proof.
  split; [exact trending_lambda2|].
  split; [exact random_lambda2|].
  exact reverting_lambda2.
Qed.

Lemma correction_hierarchy :
  MarketPartitionFunction.market_correction (3#5) 3 == 1#125 /\
  MarketPartitionFunction.market_correction (4#5) 3 == 27#125.
Proof.
  split; [exact mild_trend_N3 | exact strong_trend_N3].
Qed.

Lemma memory_decay_bound :
  IsingMarketMap.qpow (3#5) 3 < 1#4.
Proof. exact memory_3_periods. Qed.

Lemma doubly_stochastic :
  forall p, IsingMarketMap.market_transfer p O O +
            IsingMarketMap.market_transfer p O (S O) == 1.
Proof. exact transfer_row0_sums. Qed.

Lemma imbalance_eigenvalue :
  forall p, IsingMarketMap.market_transfer p O O -
            IsingMarketMap.market_transfer p O (S O) ==
            IsingMarketMap.market_lambda2 p.
Proof. exact imbalance_is_lambda2. Qed.

Lemma correction_scales_as_27 :
  MarketPartitionFunction.market_correction (4#5) 3 ==
  27 * MarketPartitionFunction.market_correction (3#5) 3.
Proof. exact correction_ratio_N3. Qed.

Lemma partition_function_N5 :
  MarketPartitionFunction.market_correction (4#5) 5 == 243#3125.
Proof. exact strong_trend_N5. Qed.

(* ===== Grand synthesis ===== *)

Theorem ising_market_grand_synthesis :
  (* Three regimes *)
  (IsingMarketMap.market_lambda2 (4#5) == 3#5 /\
   IsingMarketMap.market_lambda2 (1#2) == 0 /\
   IsingMarketMap.market_lambda2 (1#5) == -(3#5)) /\
  (* Memory decay *)
  IsingMarketMap.qpow (3#5) 3 < 1#4 /\
  (* Correction hierarchy *)
  (MarketPartitionFunction.market_correction (3#5) 3 == 1#125 /\
   MarketPartitionFunction.market_correction (4#5) 3 == 27#125) /\
  (* Doubly stochastic *)
  (forall p, IsingMarketMap.market_transfer p O O +
             IsingMarketMap.market_transfer p O (S O) == 1).
Proof.
  split; [exact three_regimes_classified|].
  split; [exact memory_decay_bound|].
  split; [exact correction_hierarchy|].
  exact doubly_stochastic.
Qed.
