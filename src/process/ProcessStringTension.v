(** * ProcessStringTension.v — String Tension from Transfer Matrix
    Theory of Systems - Phase 38: String Tension (W8) (File 1)

    Elements: neg_ln_taylor, string_tension, sigma_process
    Roles:    compute σa² = −ln(t₁/t₀) via Taylor series over Q
    Rules:    σa² = −ln(1 − gap/t₀) = Σ (gap/t₀)^k/k
    Status:   complete

    The string tension σ is the coefficient of the area law in Wilson
    loops — the fundamental observable of confinement. We compute it
    from our transfer matrix eigenvalues using Taylor series of −ln(1−x).

    σ = −ln(t₁/t₀) = −ln(1 − gap/t₀) where gap = t₀ − t₁.
    At β=1, M=0: gap/t₀ = (289/384)/(7/8) = 289/336.
    M=0 overestimates; exact value −ln(I₁/I₀) ≈ 0.764.

    STATUS: 43 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.SpectralGapCorrect.

(* ================================================================== *)
(*  Part I: Rational Logarithm  (~10 lemmas)                          *)
(* ================================================================== *)

(** Taylor series: −ln(1−x) = x + x²/2 + x³/3 + x⁴/4 + ...
    Partial sum to order N *)
Fixpoint neg_ln_taylor (x : Q) (N : nat) : Q :=
  match N with
  | 0%nat => 0
  | S k => neg_ln_taylor x k + Qpow x N / inject_Z (Z.of_nat N)
  end.

(** Order 1: just x *)
Lemma taylor_order_1 : forall x,
  neg_ln_taylor x 1 == x.
Proof.
  intros x. simpl. unfold Qdiv.
  assert (H : / inject_Z 1 == 1).
  { unfold Qeq. simpl. lia. }
  rewrite H. ring.
Qed.

(** Order 2: x + x²/2 *)
Lemma taylor_order_2 : forall x,
  neg_ln_taylor x 2 == x + x * x / 2.
Proof.
  intros x. unfold neg_ln_taylor.
  (* 0 + Qpow x 1 / inject_Z 1 + Qpow x 2 / inject_Z 2 *)
  unfold Qdiv.
  assert (H1 : / inject_Z (Z.of_nat 1) == 1) by (unfold Qeq; simpl; lia).
  assert (H2 : inject_Z (Z.of_nat 2) == 2) by (unfold Qeq; simpl; lia).
  rewrite H1, H2. simpl Qpow.
  ring.
Qed.

(** Order 3: x + x²/2 + x³/3 *)
Lemma taylor_order_3 : forall x,
  neg_ln_taylor x 3 == x + x * x / 2 + x * (x * x) / 3.
Proof.
  intros x. unfold neg_ln_taylor.
  unfold Qdiv.
  assert (H1 : / inject_Z (Z.of_nat 1) == 1) by (unfold Qeq; simpl; lia).
  assert (H2 : inject_Z (Z.of_nat 2) == 2) by (unfold Qeq; simpl; lia).
  assert (H3 : inject_Z (Z.of_nat 3) == 3) by (unfold Qeq; simpl; lia).
  rewrite H1, H2, H3. simpl Qpow.
  ring.
Qed.

(** inject_Z of positive nat is positive *)
Lemma inject_Z_of_nat_pos : forall k,
  (1 <= k)%nat -> 0 < inject_Z (Z.of_nat k).
Proof.
  intros k Hk. change 0 with (inject_Z 0).
  rewrite <- Zlt_Qlt. lia.
Qed.

(** Each term x^k/k is positive for x > 0 *)
Lemma taylor_term_positive : forall x k,
  0 < x -> (1 <= k)%nat ->
  0 < Qpow x k / inject_Z (Z.of_nat k).
Proof.
  intros x k Hx Hk.
  unfold Qdiv. apply Qmult_lt_0_compat.
  - apply Qpow_pos. exact Hx.
  - apply Qinv_lt_0_compat. apply inject_Z_of_nat_pos. exact Hk.
Qed.

(** Each term is nonneg for x >= 0 *)
Lemma taylor_term_nonneg : forall x k,
  0 <= x -> (1 <= k)%nat ->
  0 <= Qpow x k / inject_Z (Z.of_nat k).
Proof.
  intros x k Hx Hk.
  unfold Qdiv. apply Qmult_le_0_compat.
  - apply Qpow_nonneg. exact Hx.
  - apply Qlt_le_weak. apply Qinv_lt_0_compat.
    apply inject_Z_of_nat_pos. exact Hk.
Qed.

(** Partial sums are nonneg for x >= 0 *)
Lemma taylor_nonneg : forall x N,
  0 <= x ->
  0 <= neg_ln_taylor x N.
Proof.
  intros x N Hx. induction N as [| k IH].
  - simpl. lra.
  - change (neg_ln_taylor x (S k)) with
      (neg_ln_taylor x k + Qpow x (S k) / inject_Z (Z.of_nat (S k))).
    assert (Ht : 0 <= Qpow x (S k) / inject_Z (Z.of_nat (S k))).
    { apply taylor_term_nonneg; [exact Hx | lia]. }
    lra.
Qed.

(** Partial sums are increasing for x > 0 *)
Lemma taylor_increasing : forall x N,
  0 < x ->
  neg_ln_taylor x N <= neg_ln_taylor x (S N).
Proof.
  intros x N Hx.
  change (neg_ln_taylor x (S N)) with
    (neg_ln_taylor x N + Qpow x (S N) / inject_Z (Z.of_nat (S N))).
  assert (Ht : 0 < Qpow x (S N) / inject_Z (Z.of_nat (S N))).
  { apply taylor_term_positive; [exact Hx | lia]. }
  lra.
Qed.

(** Strict increase *)
Lemma taylor_strict_increasing : forall x N,
  0 < x ->
  neg_ln_taylor x N < neg_ln_taylor x (S N).
Proof.
  intros x N Hx.
  change (neg_ln_taylor x (S N)) with
    (neg_ln_taylor x N + Qpow x (S N) / inject_Z (Z.of_nat (S N))).
  assert (Ht : 0 < Qpow x (S N) / inject_Z (Z.of_nat (S N))).
  { apply taylor_term_positive; [exact Hx | lia]. }
  lra.
Qed.

(** Qpow x (S k) = x * Qpow x k *)
Lemma Qpow_S : forall x k,
  Qpow x (S k) == x * Qpow x k.
Proof. intros. simpl. reflexivity. Qed.

(** x^k <= x^j when j <= k and 0 <= x <= 1 *)
Lemma Qpow_le_mono : forall x j k,
  0 <= x -> x <= 1 -> (j <= k)%nat ->
  Qpow x k <= Qpow x j.
Proof.
  intros x j k Hx Hx1 Hjk.
  induction k as [| m IH].
  - assert (j = 0%nat) by lia. subst. lra.
  - destruct (Nat.eq_dec j (S m)).
    + subst. lra.
    + assert (Hm : (j <= m)%nat) by lia.
      specialize (IH Hm).
      assert (Qpow x (S m) <= Qpow x m).
      { rewrite Qpow_S.
        assert (Hpm : 0 <= Qpow x m) by (apply Qpow_nonneg; lra).
        assert (x * Qpow x m <= 1 * Qpow x m).
        { apply Qmult_le_compat_r; lra. }
        lra. }
      lra.
Qed.

(** Each term x^k/k <= x^k for k >= 1 *)
Lemma taylor_term_le_power : forall x k,
  0 <= x -> (1 <= k)%nat ->
  Qpow x k / inject_Z (Z.of_nat k) <= Qpow x k.
Proof.
  intros x k Hx Hk.
  assert (Hkp : 0 < inject_Z (Z.of_nat k)) by (apply inject_Z_of_nat_pos; exact Hk).
  assert (Hpn : 0 <= Qpow x k) by (apply Qpow_nonneg; exact Hx).
  assert (Ht : 0 <= Qpow x k / inject_Z (Z.of_nat k)).
  { apply taylor_term_nonneg; assumption. }
  (* Multiply both sides by k: Qpow x k <= Qpow x k * k *)
  (* Equivalent: Qpow x k / k * k <= Qpow x k *)
  (* Qpow x k / k * k = Qpow x k *)
  (* So actually: we need Qpow x k / k <= Qpow x k *)
  (* <=> Qpow x k / k * k <= Qpow x k * k (multiply by k > 0) *)
  (* <=> Qpow x k <= Qpow x k * k *)
  (* <=> 1 <= k (divide by Qpow x k if > 0, or Qpow = 0 => trivial) *)
  destruct (Qeq_dec (Qpow x k) 0) as [Hz | Hnz].
  - (* Qpow x k = 0 => term = 0 <= 0 = Qpow x k *)
    assert (Qpow x k / inject_Z (Z.of_nat k) == 0).
    { unfold Qdiv. rewrite Hz. ring. }
    lra.
  - (* Qpow x k > 0 *)
    assert (Hpp : 0 < Qpow x k) by lra.
    apply Qle_shift_div_r; [exact Hkp |].
    assert (H1 : 1 <= inject_Z (Z.of_nat k)).
    { change 1 with (inject_Z 1). rewrite <- Zle_Qle. lia. }
    apply Qle_trans with (Qpow x k * 1).
    + lra.
    + apply Qmult_le_compat_nonneg.
      * split; lra.
      * split; lra.
Qed.

(** Helper: geometric partial sum *)
Fixpoint geo_partial (x : Q) (N : nat) : Q :=
  match N with
  | 0%nat => 0
  | S k => geo_partial x k + Qpow x N
  end.

(** geo_partial x N = x * (1 - x^N) / (1-x) — we prove bound directly *)
Lemma geo_partial_nonneg : forall x N,
  0 <= x -> 0 <= geo_partial x N.
Proof.
  intros x N Hx. induction N as [|k IH].
  - simpl. lra.
  - change (geo_partial x (S k)) with (geo_partial x k + Qpow x (S k)).
    assert (0 <= Qpow x (S k)) by (apply Qpow_nonneg; lra). lra.
Qed.

Lemma geo_partial_increasing : forall x N,
  0 < x -> geo_partial x N <= geo_partial x (S N).
Proof.
  intros x N Hx.
  change (geo_partial x (S N)) with (geo_partial x N + Qpow x (S N)).
  assert (0 < Qpow x (S N)) by (apply Qpow_pos; lra). lra.
Qed.

(** neg_ln_taylor <= geo_partial *)
Lemma taylor_le_geo : forall x N,
  0 <= x -> neg_ln_taylor x N <= geo_partial x N.
Proof.
  intros x N Hx. induction N as [|k IH].
  - simpl. lra.
  - change (neg_ln_taylor x (S k)) with
      (neg_ln_taylor x k + Qpow x (S k) / inject_Z (Z.of_nat (S k))).
    change (geo_partial x (S k)) with (geo_partial x k + Qpow x (S k)).
    assert (H1 : (1 <= S k)%nat) by lia.
    assert (Ht := taylor_term_le_power x (S k) Hx H1).
    lra.
Qed.

(** geo_partial x (S N) = geo_partial x N + x^(S N) *)
Lemma geo_partial_unfold : forall x N,
  geo_partial x (S N) == geo_partial x N + Qpow x (S N).
Proof.
  intros. reflexivity.
Qed.

(** geo_partial x N * (1-x) + x^(S N) == x *)
Lemma geo_partial_telescope : forall x N,
  geo_partial x N * (1 - x) + Qpow x (S N) == x.
Proof.
  intros x N. induction N as [|k IH].
  - simpl. ring.
  - change (geo_partial x (S k)) with (geo_partial x k + Qpow x (S k)).
    (* Need: (geo k + x^(Sk)) * (1-x) + x^(S(Sk)) == x *)
    (* = geo k*(1-x) + x^(Sk)*(1-x) + x^(S(Sk)) *)
    (* = geo k*(1-x) + x^(Sk) - x^(S(Sk)) + x^(S(Sk)) *)
    (* = geo k*(1-x) + x^(Sk) *)
    (* = x by IH *)
    assert (Hsimp : (geo_partial x k + Qpow x (S k)) * (1 - x) + Qpow x (S (S k)) ==
                    geo_partial x k * (1 - x) + Qpow x (S k)).
    { assert (Hxx : Qpow x (S (S k)) == x * Qpow x (S k)) by (simpl Qpow; ring).
      lra. }
    lra.
Qed.

(** geo_partial * (1-x) <= x *)
Lemma geo_partial_times_1mx_le_x : forall x N,
  0 <= x ->
  geo_partial x N * (1 - x) <= x.
Proof.
  intros x N Hx.
  assert (Htel := geo_partial_telescope x N).
  assert (Hpn : 0 <= Qpow x (S N)) by (apply Qpow_nonneg; lra).
  lra.
Qed.

(** geo_partial bounded by x/(1-x) *)
Lemma geo_partial_bounded : forall x N,
  0 <= x -> x < 1 ->
  geo_partial x N <= x / (1 - x).
Proof.
  intros x N Hx Hx1.
  assert (H1mx : 0 < 1 - x) by lra.
  assert (Hmul := geo_partial_times_1mx_le_x x N Hx).
  (* geo_partial * (1-x) <= x, divide by (1-x) *)
  assert (Hgn : 0 <= geo_partial x N) by (apply geo_partial_nonneg; exact Hx).
  apply Qle_shift_div_l; [lra |].
  (* goal: geo_partial x N * (1 - x) <= x *)
  exact Hmul.
Qed.

(** Now the actual taylor_bounded *)
Lemma taylor_bounded : forall x N,
  0 < x -> x < 1 ->
  neg_ln_taylor x N <= x / (1 - x).
Proof.
  intros x N Hx Hx1.
  assert (Htg := taylor_le_geo x N (Qlt_le_weak _ _ Hx)).
  assert (Hgb := geo_partial_bounded x N (Qlt_le_weak _ _ Hx) Hx1).
  lra.
Qed.

(** ★ The Taylor partial sum process is Cauchy (converges) *)
Definition ln_process (x : Q) : RealProcess :=
  fun N => neg_ln_taylor x (S N).

(** ln_process is monotone increasing *)
Lemma ln_process_increasing : forall x,
  0 < x ->
  monotone_increasing (ln_process x).
Proof.
  intros x Hx n. unfold ln_process.
  apply taylor_increasing. exact Hx.
Qed.

(** ln_process is bounded above *)
Lemma ln_process_bounded : forall x,
  0 < x -> x < 1 ->
  forall n, ln_process x n <= x / (1 - x).
Proof.
  intros x Hx Hx1 n. unfold ln_process.
  apply taylor_bounded; assumption.
Qed.

Theorem ln_process_cauchy : forall x,
  0 < x -> x < 1 ->
  is_Cauchy (ln_process x).
Proof.
  intros x Hx Hx1.
  apply (monotone_bounded_Cauchy _ (x / (1 - x))).
  - exact (ln_process_increasing x Hx).
  - intro n. exact (ln_process_bounded x Hx Hx1 n).
Qed.

(* ================================================================== *)
(*  Part II: String Tension  (~10 lemmas)                             *)
(* ================================================================== *)

(** String tension: σa² = −ln(t₁/t₀) = −ln(1 − gap/t₀)
    Using Taylor: σa² = Σ (gap/t₀)^k/k
    At β=1, M=0: gap/t₀ = (289/384)/(7/8) = 289/336 *)

Definition string_tension_gap (gap : Q) (order : nat) : Q :=
  neg_ln_taylor gap order.

(** String tension from spectral gap, corrected: use gap/t₀ *)
Definition string_tension (beta : Q) (order : nat) : Q :=
  neg_ln_taylor (gap_M0 beta / t0_M0 beta) order.

(** At β=1: gap = 289/384, t₀ = 7/8, gap/t₀ = 289/336 *)
Lemma gap_289_384 : gap_M0 1 == 289 # 384.
Proof. exact gap_at_beta_1. Qed.

Lemma gap_over_t0_beta_1 : gap_M0 1 / t0_M0 1 == 289 # 336.
Proof.
  rewrite gap_at_beta_1. rewrite t0_at_beta_1.
  unfold Qdiv. unfold Qeq. simpl. lia.
Qed.

(** σ order 1 = gap/t₀ = 289/336 *)
Lemma sigma_order_1 : string_tension 1 1 == 289 # 336.
Proof.
  unfold string_tension.
  rewrite taylor_order_1. exact gap_over_t0_beta_1.
Qed.

(** σ order 2 = gap/t₀ + (gap/t₀)²/2 *)
Lemma sigma_order_2 : string_tension 1 2 ==
  (289 # 336) + ((289 # 336) * (289 # 336) / (2#1)).
Proof.
  unfold string_tension.
  rewrite taylor_order_2. rewrite gap_over_t0_beta_1. reflexivity.
Qed.

(** σ order 3 *)
Lemma sigma_order_3 : string_tension 1 3 ==
  (289 # 336) + ((289 # 336) * (289 # 336) / (2#1)) +
  ((289 # 336) * ((289 # 336) * (289 # 336)) / (3#1)).
Proof.
  unfold string_tension.
  rewrite taylor_order_3. rewrite gap_over_t0_beta_1. reflexivity.
Qed.

(** gap/t₀ > 0 at β=1 *)
Lemma gap_over_t0_positive : 0 < gap_M0 1 / t0_M0 1.
Proof. rewrite gap_over_t0_beta_1. lra. Qed.

(** σ is increasing in order *)
Lemma sigma_increasing : forall N,
  string_tension 1 N <= string_tension 1 (S N).
Proof.
  intros N. unfold string_tension.
  apply taylor_increasing. exact gap_over_t0_positive.
Qed.

(** σ is nonneg *)
Lemma sigma_nonneg : forall N,
  0 <= string_tension 1 N.
Proof.
  intros N. unfold string_tension.
  apply taylor_nonneg. apply Qlt_le_weak. exact gap_over_t0_positive.
Qed.

(** σ at order 1 is positive *)
Lemma sigma_order_1_positive : 0 < string_tension 1 1.
Proof.
  assert (H := sigma_order_1).
  assert (H2 : (0:Q) < 289 # 336) by lra. lra.
Qed.

(** ★ The string tension as a process (in Taylor order) *)
Definition sigma_process : RealProcess :=
  fun N => string_tension 1 (S N).

(** Sigma process is increasing *)
Lemma sigma_process_increasing : monotone_increasing sigma_process.
Proof.
  intro n. unfold sigma_process.
  apply sigma_increasing.
Qed.

(** gap/t₀ < 1 at β=1 *)
Lemma gap_over_t0_lt_1 : gap_M0 1 / t0_M0 1 < 1.
Proof.
  rewrite gap_over_t0_beta_1. lra.
Qed.

(** Sigma process is Cauchy *)
Theorem sigma_cauchy : is_Cauchy sigma_process.
Proof.
  unfold sigma_process.
  assert (Hcauchy := ln_process_cauchy _ gap_over_t0_positive gap_over_t0_lt_1).
  unfold ln_process in Hcauchy.
  intros eps Heps. destruct (Hcauchy eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  unfold string_tension in *.
  exact HN.
Qed.

(* ================================================================== *)
(*  Part III: Physical Value and Bounds  (~5 lemmas)                  *)
(* ================================================================== *)

(** Lower bound: any partial sum *)
Lemma sigma_lower_bound : forall N,
  string_tension 1 N <= string_tension 1 (S N).
Proof. exact sigma_increasing. Qed.

(** Upper bound from geometric series: (gap/t₀) / (1 − gap/t₀) *)
Definition sigma_upper_bound : Q :=
  (289 # 336) / (1 - (289 # 336)).

(** sigma_upper_bound = 289/47 *)
Lemma sigma_upper_bound_value : sigma_upper_bound == 289 # 47.
Proof.
  unfold sigma_upper_bound. unfold Qdiv.
  assert (H : 1 - (289 # 336) == 47 # 336) by (unfold Qeq; simpl; lia).
  rewrite H. unfold Qeq. simpl. lia.
Qed.

(** Sigma bounded above *)
Lemma sigma_bounded_above : forall N,
  string_tension 1 N <= sigma_upper_bound.
Proof.
  intros N. unfold string_tension.
  assert (Hgap := gap_over_t0_positive).
  assert (Hlt := gap_over_t0_lt_1).
  assert (Hbnd := taylor_bounded _ N Hgap Hlt).
  unfold sigma_upper_bound.
  assert (Heq : gap_M0 1 / t0_M0 1 / (1 - gap_M0 1 / t0_M0 1) ==
    (289 # 336) / (1 - (289 # 336))).
  { rewrite gap_over_t0_beta_1. reflexivity. }
  lra.
Qed.

(** σ₁ ≈ 0.860 — concrete lower bound *)
Lemma sigma_ge_half : 289 # 336 <= string_tension 1 1.
Proof.
  rewrite sigma_order_1. lra.
Qed.

(** σ is bracketed: 289/336 <= σ <= 289/47 *)
Lemma sigma_bracketed : forall N,
  (1 <= N)%nat ->
  289 # 336 <= string_tension 1 N /\
  string_tension 1 N <= 289 # 47.
Proof.
  intros N HN. split.
  - assert (H1 : 289 # 336 <= string_tension 1 1).
    { rewrite sigma_order_1. lra. }
    assert (Hmono : forall k, string_tension 1 k <= string_tension 1 (S k)).
    { exact sigma_increasing. }
    induction N as [| m IH].
    + lia.
    + destruct (Nat.eq_dec m 0).
      * subst. exact H1.
      * assert (Hm : (1 <= m)%nat) by lia.
        specialize (IH Hm). specialize (Hmono m). lra.
  - assert (Hub := sigma_bounded_above N).
    assert (Hval := sigma_upper_bound_value). lra.
Qed.

(* ================================================================== *)
(*  Part IV: β-Dependence  (~5 lemmas)                                *)
(* ================================================================== *)

(** String tension at different β *)
Definition sigma_at_beta (beta : Q) (order : nat) : Q :=
  string_tension beta order.

(** Confinement: σ > 0 for β = 1 at any positive order *)
Theorem confinement_beta_1 : forall N,
  (1 <= N)%nat ->
  0 < string_tension 1 N.
Proof.
  intros N HN.
  assert (H := sigma_bracketed N HN).
  lra.
Qed.

(** String tension increases with gap *)
Lemma sigma_monotone_in_gap : forall g1 g2,
  0 <= g1 -> g1 <= g2 ->
  forall N, neg_ln_taylor g1 N <= neg_ln_taylor g2 N.
Proof.
  intros g1 g2 Hg1 Hg12 N.
  induction N as [| k IH].
  - simpl. lra.
  - change (neg_ln_taylor g1 (S k)) with
      (neg_ln_taylor g1 k + Qpow g1 (S k) / inject_Z (Z.of_nat (S k))).
    change (neg_ln_taylor g2 (S k)) with
      (neg_ln_taylor g2 k + Qpow g2 (S k) / inject_Z (Z.of_nat (S k))).
    assert (Hpk : Qpow g1 (S k) <= Qpow g2 (S k)).
    { clear IH. induction k as [| j IHj].
      + simpl Qpow. lra.
      + assert (Qpow g1 (S (S j)) == g1 * Qpow g1 (S j)) by (simpl Qpow; ring).
        assert (Qpow g2 (S (S j)) == g2 * Qpow g2 (S j)) by (simpl Qpow; ring).
        assert (Hp1 : 0 <= Qpow g1 (S j)) by (apply Qpow_nonneg; lra).
        assert (Hp2 : 0 <= Qpow g2 (S j)) by (apply Qpow_nonneg; lra).
        assert (g1 * Qpow g1 (S j) <= g2 * Qpow g2 (S j)).
        { apply Qle_trans with (g2 * Qpow g1 (S j)).
          - apply Qmult_le_compat_r; lra.
          - assert (g2 * Qpow g1 (S j) <= g2 * Qpow g2 (S j)).
            { apply Qmult_le_compat_nonneg.
              split; [lra | lra].
              split; [exact Hp1 | exact IHj]. }
            lra. }
        lra. }
    assert (Hkp : 0 < inject_Z (Z.of_nat (S k))) by (apply inject_Z_of_nat_pos; lia).
    assert (Hdiv : Qpow g1 (S k) / inject_Z (Z.of_nat (S k)) <=
                   Qpow g2 (S k) / inject_Z (Z.of_nat (S k))).
    { unfold Qdiv. apply Qmult_le_compat_r.
      - exact Hpk.
      - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hkp. }
    lra.
Qed.

(** At β=2: gap/t₀ = (1/24)/(1/2) = 1/12, σ is smaller *)
Lemma gap_over_t0_beta_2 : gap_M0 2 / t0_M0 2 == 1 # 12.
Proof.
  rewrite gap_at_beta_2. rewrite t0_at_beta_2.
  unfold Qdiv. unfold Qeq. simpl. lia.
Qed.

Lemma sigma_beta_2_order_1 : string_tension 2 1 == 1 # 12.
Proof.
  unfold string_tension.
  rewrite taylor_order_1. exact gap_over_t0_beta_2.
Qed.

(** σ(β=2) < σ(β=1) at order 1 *)
Lemma sigma_beta_2_lt_beta_1 :
  string_tension 2 1 < string_tension 1 1.
Proof.
  rewrite sigma_beta_2_order_1. rewrite sigma_order_1. lra.
Qed.

(** ★ W8: String tension computed — first experimentally comparable number *)
Theorem w8_string_tension :
  (* σ(β=1) > 0 — confinement *)
  0 < string_tension 1 1 /\
  (* σ(β=1) = 289/336 at first order (gap/t₀) *)
  string_tension 1 1 == 289 # 336 /\
  (* σ process is Cauchy — convergent *)
  is_Cauchy sigma_process /\
  (* σ(β=2) < σ(β=1) — weaker coupling, less tension *)
  string_tension 2 1 < string_tension 1 1.
Proof.
  split; [| split; [| split]].
  - exact sigma_order_1_positive.
  - exact sigma_order_1.
  - exact sigma_cauchy.
  - exact sigma_beta_2_lt_beta_1.
Qed.
