(** * IsingMarketMap.v — Ising model mapped to market regimes
    Elements: transfer matrices, eigenvalues, momentum parameter;
    Roles:    regime classification via lambda2;
    Rules:    trending/random/reverting determined by p parameter.
    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Open Scope Q_scope.

(* ===== Market transfer matrix ===== *)

Definition market_transfer (p : Q) (i j : nat) : Q :=
  match (i, j) with
  | (O, O) => p
  | (O, S O) => 1 - p
  | (S O, O) => 1 - p
  | (S O, S O) => p
  | _ => 0
  end.

(* ===== Second eigenvalue ===== *)

Definition market_lambda2 (p : Q) : Q := 2 * p - 1.

(* ===== Rational power ===== *)

Fixpoint qpow (b : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => b * qpow b k
  end.

(* ===== Market momentum (memory) ===== *)

Definition market_momentum (p : Q) (t : nat) : Q := qpow (market_lambda2 p) t.

(* ===== Transfer matrix is doubly stochastic ===== *)

Lemma transfer_row0_sums : forall p,
  market_transfer p O O + market_transfer p O (S O) == 1.
Proof.
  intro p. unfold market_transfer. ring.
Qed.

Lemma transfer_row1_sums : forall p,
  market_transfer p (S O) O + market_transfer p (S O) (S O) == 1.
Proof.
  intro p. unfold market_transfer. ring.
Qed.

(* ===== Eigenvalue classification ===== *)

Lemma trending_lambda2 : market_lambda2 (4#5) == 3#5.
Proof. vm_compute. reflexivity. Qed.

Lemma random_lambda2 : market_lambda2 (1#2) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma reverting_lambda2 : market_lambda2 (1#5) == -(3#5).
Proof. vm_compute. reflexivity. Qed.

(* ===== Trending regime: momentum persists ===== *)

Lemma trending_momentum_1 : market_momentum (4#5) 1 == 3#5.
Proof. vm_compute. reflexivity. Qed.

Lemma trending_momentum_2 : market_momentum (4#5) 2 == 9#25.
Proof. vm_compute. reflexivity. Qed.

(* ===== Random walk: no memory ===== *)

Lemma random_momentum_1 : market_momentum (1#2) 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma random_momentum_any : forall t, (0 < t)%nat ->
  market_momentum (1#2) t == 0.
Proof.
  intros t Ht. unfold market_momentum.
  destruct t as [|k]; [lia|].
  simpl. unfold market_lambda2.
  assert (H0 : 2 * (1 # 2) - 1 == 0) by (vm_compute; reflexivity).
  apply Qeq_trans with (0 * qpow (2 * (1 # 2) - 1) k).
  - apply Qmult_comp; [exact H0 | apply Qeq_refl].
  - ring.
Qed.

(* ===== Reverting regime: momentum oscillates ===== *)

Lemma reverting_momentum_1 : market_momentum (1#5) 1 == -(3#5).
Proof. vm_compute. reflexivity. Qed.

Lemma reverting_momentum_2 : market_momentum (1#5) 2 == 9#25.
Proof. vm_compute. reflexivity. Qed.

(* ===== Memory decay: 3 periods of trending ===== *)

Lemma memory_3_periods : qpow (3#5) 3 < 1#4.
Proof. unfold Qlt; simpl; lia. Qed.

(* ===== Imbalance equals lambda2 (universal) ===== *)

Lemma imbalance_is_lambda2 : forall p,
  market_transfer p O O - market_transfer p O (S O) == market_lambda2 p.
Proof.
  intro p. unfold market_transfer, market_lambda2. ring.
Qed.

(* ===== Trace determines eigenvalues ===== *)

Lemma transfer_trace : forall p,
  market_transfer p O O + market_transfer p (S O) (S O) == 2 * p.
Proof.
  intro p. unfold market_transfer. ring.
Qed.

Lemma transfer_det : forall p,
  market_transfer p O O * market_transfer p (S O) (S O) -
  market_transfer p O (S O) * market_transfer p (S O) O == 2 * p - 1.
Proof.
  intro p. unfold market_transfer. ring.
Qed.

(* ===== Synthesis: Ising-Market correspondence ===== *)

Theorem ising_market_map_synthesis :
  (* trending *)
  market_lambda2 (4#5) == 3#5 /\
  (* random *)
  market_lambda2 (1#2) == 0 /\
  (* reverting *)
  market_lambda2 (1#5) == -(3#5) /\
  (* memory decay *)
  qpow (3#5) 3 < 1#4 /\
  (* doubly stochastic *)
  (forall p, market_transfer p O O + market_transfer p O (S O) == 1).
Proof.
  split; [exact trending_lambda2|].
  split; [exact random_lambda2|].
  split; [exact reverting_lambda2|].
  split; [exact memory_3_periods|].
  exact transfer_row0_sums.
Qed.
