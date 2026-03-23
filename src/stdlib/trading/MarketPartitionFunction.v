(** * MarketPartitionFunction.v — Partition function for market regimes
    Elements: partition function Z, correction terms, qpow;
    Roles:    quantify regime strength via Z(p,N);
    Rules:    correction decays exponentially, trend strength measurable.
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Open Scope Q_scope.

(* ===== Rational power ===== *)

Fixpoint qpow (b : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => b * qpow b k
  end.

(* ===== Market partition function ===== *)

Definition market_Z (p : Q) (N : nat) : Q := 1 + qpow (2 * p - 1) N.

(* ===== Market correction term ===== *)

Definition market_correction (p : Q) (N : nat) : Q := qpow (Qabs (2 * p - 1)) N.

(* ===== Qabs concrete values ===== *)

Lemma qabs_one_fifth : Qabs (2 * (3#5) - 1) == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma qabs_three_fifths : Qabs (2 * (4#5) - 1) == 3#5.
Proof. vm_compute. reflexivity. Qed.

(* ===== Partition function values ===== *)

Lemma Z_random_any : forall N, (0 < N)%nat -> market_Z (1#2) N == 1.
Proof.
  intros N HN. unfold market_Z.
  destruct N as [|k]; [lia|].
  simpl.
  assert (H0 : 2 * (1 # 2) - 1 == 0) by (vm_compute; reflexivity).
  apply Qeq_trans with (1 + 0 * qpow (2 * (1 # 2) - 1) k).
  - apply Qplus_comp; [apply Qeq_refl|].
    apply Qmult_comp; [exact H0 | apply Qeq_refl].
  - ring.
Qed.

Lemma Z_trending_1 : market_Z (4#5) 1 == 8#5.
Proof. vm_compute. reflexivity. Qed.

Lemma Z_trending_3 : market_Z (4#5) 3 == 152#125.
Proof. vm_compute. reflexivity. Qed.

(* ===== Correction terms ===== *)

Lemma mild_trend_N3 : market_correction (3#5) 3 == 1#125.
Proof. vm_compute. reflexivity. Qed.

Lemma strong_trend_N3 : market_correction (4#5) 3 == 27#125.
Proof. vm_compute. reflexivity. Qed.

Lemma strong_trend_N5 : market_correction (4#5) 5 == 243#3125.
Proof. vm_compute. reflexivity. Qed.

(* ===== Correction ratio: strong vs mild ===== *)

Lemma correction_ratio_N3 : market_correction (4#5) 3 == 27 * market_correction (3#5) 3.
Proof. vm_compute. reflexivity. Qed.

(* ===== Synthesis ===== *)

Theorem partition_function_synthesis :
  market_correction (3#5) 3 == 1#125 /\
  market_correction (4#5) 3 == 27#125 /\
  market_correction (4#5) 5 == 243#3125 /\
  (forall N, (0 < N)%nat -> market_Z (1#2) N == 1).
Proof.
  split; [exact mild_trend_N3|].
  split; [exact strong_trend_N3|].
  split; [exact strong_trend_N5|].
  exact Z_random_any.
Qed.
