(** * MarketHeisenberg.v — Heisenberg analogy for markets
    Elements: gap-memory trade-off, uncertainty product, analogy table;
    Roles:    connect quantum uncertainty to market information limits;
    Rules:    gap*memory bounded, product maximized at lambda=1/2.
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
From ToS Require Import stdlib.trading.MarketUncertainty.
Open Scope Q_scope.

(* ===== Heisenberg analogy table (as comments) =====
   QM:      Delta_x * Delta_p >= hbar/2
   Market:  gap(l) * memory(l) <= 1/4

   QM position uncertainty  <->  market gap (prediction error)
   QM momentum uncertainty  <->  market memory (autocorrelation)
   hbar/2                   <->  1/4 (maximum product)
   ====================================================== *)

(* ===== Uncertainty bound: product <= 1/4 ===== *)

(* For |l| in [0,1]: gap*memory = (1-|l|)*|l| <= 1/4
   This is AM-GM: a*(1-a) <= 1/4 for a in [0,1] *)

Lemma Qsquare_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x.
  destruct (Qlt_le_dec x 0).
  - assert (Hx : x <= 0) by lra.
    assert (H : 0 <= (-x) * (-x)).
    { apply Qmult_le_0_compat; lra. }
    lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma am_gm_quarter : forall a : Q,
  0 <= a -> a <= 1 ->
  a * (1 - a) <= 1#4.
Proof.
  intros a Ha0 Ha1.
  assert (H : 0 <= (1 - 2*a) * (1 - 2*a)) by (apply Qsquare_nonneg).
  lra.
Qed.

Lemma uncertainty_bounded : forall l : Q,
  0 <= Qabs l -> Qabs l <= 1 ->
  uncertainty_product l <= 1#4.
Proof.
  intros l Habs0 Habs1.
  unfold uncertainty_product, market_gap, market_memory_param.
  rewrite Qmult_comm.
  apply am_gm_quarter; assumption.
Qed.

(* ===== Maximum achieved at l=1/2 ===== *)

Lemma heisenberg_max_at_half : uncertainty_product (1#2) == 1#4.
Proof. exact max_uncertainty_product. Qed.

(* ===== Perfect memory means no gap ===== *)

Lemma perfect_memory_no_gap : market_gap 1 == 0.
Proof.
  unfold market_gap.
  assert (H : Qabs 1 == 1) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

(* ===== No memory means full gap ===== *)

Lemma no_memory_full_gap : market_gap 0 == 1.
Proof.
  unfold market_gap.
  assert (H : Qabs 0 == 0) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

(* ===== Concrete uncertainty products ===== *)

Lemma uncertainty_at_one_fifth : uncertainty_product (1#5) == 4#25.
Proof. exact uncertainty_one_fifth. Qed.

Lemma uncertainty_at_three_fifths : uncertainty_product (3#5) == 6#25.
Proof. exact uncertainty_three_fifths. Qed.

(* ===== Both products < 1/4 ===== *)

Lemma one_fifth_below_max : uncertainty_product (1#5) < 1#4.
Proof. unfold Qlt; simpl; lia. Qed.

Lemma three_fifths_below_max : uncertainty_product (3#5) < 1#4.
Proof. unfold Qlt; simpl; lia. Qed.

(* ===== Grand synthesis ===== *)

Theorem heisenberg_market_synthesis :
  (* Maximum at 1/2 *)
  uncertainty_product (1#2) == 1#4 /\
  (* Extremes give zero *)
  uncertainty_product 0 == 0 /\
  uncertainty_product 1 == 0 /\
  (* Symmetry *)
  (forall l, uncertainty_product l == uncertainty_product (-(l))).
Proof.
  split; [exact max_uncertainty_product|].
  split; [exact uncertainty_at_zero|].
  split; [exact uncertainty_at_one|].
  exact uncertainty_symmetric.
Qed.
