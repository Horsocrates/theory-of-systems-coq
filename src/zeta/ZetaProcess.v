(* ========================================================================= *)
(*            ZETA PROCESS: z AS A CAUCHY PROCESS                          *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Formalize the Riemann zeta function z(k) for integer k >= 2   *)
(*    as a Cauchy process (sequence of partial sums over Q).                *)
(*                                                                          *)
(*  KEY RESULTS:                                                            *)
(*    - nat_power: exact integer powers over Q                              *)
(*    - zeta_term / zeta_partial: z partial sums                            *)
(*    - Telescoping comparison: 1/(n+1)^2 <= 1/(n*(n+1)) for n >= 1        *)
(*    - zeta_process_cauchy: z(k) converges for k >= 2                      *)
(*    - zeta_1_not_cauchy: harmonic series diverges                         *)
(*                                                                          *)
(*  DESIGN: Integer exponents only -- exact Q arithmetic, no approximation. *)
(*  Over Q we cannot compute n^s for non-integer s (requires roots).        *)
(*                                                                          *)
(*  AXIOMS: classic (via MonotoneConvergence -- q_inc_bounded_cauchy)        *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

From ToS Require Import ToS_Axioms.
From ToS Require Import CauchyReal.
From ToS Require Import MonotoneConvergence.
From ToS Require Import SeriesConvergence.
From ToS Require Import ProcessGeneral.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: INTEGER POWERS OVER Q                                          *)
(*                                                                           *)
(* nat_power n k = (inject_Z (Z.of_nat n))^k -- exact Q arithmetic          *)
(* ========================================================================= *)

(** Inverse monotonicity: 0 < a <= b -> /b <= /a *)
Lemma Qinv_le_compat : forall a b : Q,
  0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab.
  assert (Hb : 0 < b) by lra.
  assert (Ha_inv : 0 < / a) by (apply Qinv_lt_0_compat; exact Ha).
  assert (Hb_inv : 0 < / b) by (apply Qinv_lt_0_compat; exact Hb).
  (* /b <= /a iff a <= b (multiply both sides by a*b) *)
  (* /b * (a * b) = a and /a * (a * b) = b *)
  assert (Hprod : 0 < a * b) by (apply Qmult_lt_0_compat; lra).
  assert (Hlhs : / b * (a * b) == a).
  { field. lra. }
  assert (Hrhs : / a * (a * b) == b).
  { field. lra. }
  (* From Hab: a <= b, i.e., /b * (a*b) <= /a * (a*b) *)
  (* So /b <= /a (divide by a*b > 0) *)
  destruct (Qle_lt_or_eq _ _ Hab) as [Hlt | Heq].
  - assert (Hdiff : 0 < (/ a - / b) * (a * b)).
    { setoid_replace ((/ a - / b) * (a * b)) with (b - a) by (field; split; lra).
      lra. }
    assert (Hdiff2 : 0 < / a - / b).
    { destruct (Qlt_le_dec 0 (/ a - / b)); [lra|].
      assert (Hle : (/ a - / b) * (a * b) <= 0 * (a * b)).
      { apply Qmult_le_compat_r; lra. }
      lra. }
    lra.
  - (* a == b -> /a == /b *)
    assert (Hinveq : / a == / b) by (apply Qinv_comp; exact Heq).
    lra.
Qed.

(** Integer power: n^k as a rational number *)
Definition nat_power (n k : nat) : Q := Qpow (inject_Z (Z.of_nat n)) k.

(** S n as a positive rational *)
Lemma inject_Z_Sn_pos : forall n : nat,
  0 < inject_Z (Z.of_nat (S n)).
Proof.
  intros n. unfold Qlt, inject_Z. simpl. lia.
Qed.

(** S n as nonzero rational *)
Lemma inject_Z_Sn_neq_0 : forall n : nat,
  ~ inject_Z (Z.of_nat (S n)) == 0.
Proof.
  intros n H. assert (Hpos := inject_Z_Sn_pos n). lra.
Qed.

(** nat_power of S n is positive *)
Lemma nat_power_Sn_pos : forall n k : nat,
  0 < nat_power (S n) k.
Proof.
  intros n k. unfold nat_power. apply Qpow_pos. apply inject_Z_Sn_pos.
Qed.

(** nat_power of S n is nonzero *)
Lemma nat_power_Sn_neq_0 : forall n k : nat,
  ~ nat_power (S n) k == 0.
Proof.
  intros n k H. assert (Hpos := nat_power_Sn_pos n k). lra.
Qed.

(** nat_power of S n is >= 1 *)
Lemma nat_power_Sn_ge_1 : forall n k : nat,
  1 <= nat_power (S n) k.
Proof.
  intros n k. unfold nat_power.
  induction k; simpl.
  - lra.
  - assert (H1 : 1 <= inject_Z (Z.of_nat (S n))).
    { unfold Qle, inject_Z. simpl. lia. }
    assert (Hpow_pos : 0 < Qpow (inject_Z (Z.of_nat (S n))) k).
    { apply Qpow_pos. apply inject_Z_Sn_pos. }
    (* Sn * pow >= pow >= 1 *)
    apply Qle_trans with (y := Qpow (inject_Z (Z.of_nat (S n))) k).
    + exact IHk.
    + setoid_replace (Qpow (inject_Z (Z.of_nat (S n))) k)
        with (1 * Qpow (inject_Z (Z.of_nat (S n))) k) at 1 by ring.
      apply Qmult_le_compat_r.
      * exact H1.
      * apply Qlt_le_weak. exact Hpow_pos.
Qed.

(* ========================================================================= *)
(* SECTION 2: ZETA TERMS AND PARTIAL SUMS                                   *)
(* ========================================================================= *)

(** Zeta term: 1/(n+1)^k -- index shifted so that a(0) = 1/1^k = 1 *)
Definition zeta_term (k : nat) (n : nat) : Q :=
  / nat_power (S n) k.

(** Zeta partial sum *)
Definition zeta_partial (k N : nat) : Q :=
  partial_sum (zeta_term k) N.

(** The zeta process: z(k) as a sequence of partial sums *)
Definition zeta_process (k : nat) : nat -> Q :=
  zeta_partial k.

(** Zeta terms are positive *)
Lemma zeta_term_pos : forall k n : nat,
  0 < zeta_term k n.
Proof.
  intros k n. unfold zeta_term.
  apply Qinv_lt_0_compat. apply nat_power_Sn_pos.
Qed.

(** Zeta terms are nonneg *)
Lemma zeta_term_nonneg : forall k n : nat,
  0 <= zeta_term k n.
Proof.
  intros k n. assert (H := zeta_term_pos k n). lra.
Qed.

(** Zeta terms are <= 1 *)
Lemma zeta_term_le_1 : forall k n : nat,
  zeta_term k n <= 1.
Proof.
  intros k n. unfold zeta_term.
  assert (H : 1 <= nat_power (S n) k) by (apply nat_power_Sn_ge_1).
  assert (Hpos : 0 < nat_power (S n) k) by (apply nat_power_Sn_pos).
  assert (Hinv : / nat_power (S n) k <= / 1).
  { apply Qinv_le_compat; lra. }
  assert (H1 : / 1 == 1) by (unfold Qeq; simpl; lia).
  lra.
Qed.

(** Higher k gives smaller terms: k1 <= k2 -> zeta_term k2 n <= zeta_term k1 n *)
Lemma zeta_term_k_monotone : forall k1 k2 n : nat,
  (k1 <= k2)%nat ->
  zeta_term k2 n <= zeta_term k1 n.
Proof.
  intros k1 k2 n Hk. unfold zeta_term.
  assert (H : nat_power (S n) k1 <= nat_power (S n) k2).
  { unfold nat_power.
    induction k2.
    - assert (Hk1_0 : k1 = 0%nat) by lia. subst. simpl. lra.
    - destruct (Nat.eq_dec k1 (S k2)) as [->|Hne].
      + lra.
      + assert (Hk1_le : (k1 <= k2)%nat) by lia.
        assert (IH := IHk2 Hk1_le).
        simpl.
        assert (Hbase : 1 <= inject_Z (Z.of_nat (S n))).
        { unfold Qle, inject_Z. simpl. lia. }
        assert (Hpow_pos : 0 < Qpow (inject_Z (Z.of_nat (S n))) k2).
        { apply Qpow_pos. apply inject_Z_Sn_pos. }
        (* Qpow k1 <= Qpow k2 <= Sn * Qpow k2 *)
        apply Qle_trans with (y := Qpow (inject_Z (Z.of_nat (S n))) k2).
        * exact IH.
        * setoid_replace (Qpow (inject_Z (Z.of_nat (S n))) k2)
            with (1 * Qpow (inject_Z (Z.of_nat (S n))) k2) at 1 by ring.
          apply Qmult_le_compat_r.
          -- exact Hbase.
          -- apply Qlt_le_weak. exact Hpow_pos. }
  assert (Hpos1 : 0 < nat_power (S n) k1) by (apply nat_power_Sn_pos).
  assert (Hpos2 : 0 < nat_power (S n) k2) by (apply nat_power_Sn_pos).
  apply Qinv_le_compat; lra.
Qed.

(** The first zeta term equals 1 *)
Lemma zeta_term_0_eq_1 : forall k : nat,
  zeta_term k 0 == 1.
Proof.
  intros k. unfold zeta_term, nat_power.
  assert (H1 : inject_Z (Z.of_nat 1) == 1).
  { unfold Qeq, inject_Z. simpl. lia. }
  assert (Hp1 : Qpow (inject_Z (Z.of_nat 1)) k == 1).
  { rewrite (Qpow_wd _ 1 k H1). apply Qpow_1. }
  rewrite Hp1. unfold Qeq. simpl. lia.
Qed.

(* ========================================================================= *)
(* SECTION 3: TELESCOPING COMPARISON                                         *)
(*                                                                           *)
(* Key idea: for n >= 1, 1/(n+1)^2 <= 1/(n*(n+1)) = 1/n - 1/(n+1)          *)
(* because n <= n+1 implies n*(n+1) <= (n+1)^2.                             *)
(* Telescoping sum: Sum_{i=1}^{N} 1/(i*(i+1)) = 1 - 1/(N+1) < 1.           *)
(* So zeta_partial k N <= 1 + 1 = 2 for k >= 2.                             *)
(* ========================================================================= *)

(** For n >= 1: n*(n+1) <= (n+1)^2, so 1/(n+1)^2 <= 1/(n*(n+1)) *)
Lemma sq_ge_consec_product : forall n : nat,
  (1 <= n)%nat ->
  inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n)) <=
  inject_Z (Z.of_nat (S n)) * inject_Z (Z.of_nat (S n)).
Proof.
  intros n Hn.
  assert (Hle : inject_Z (Z.of_nat n) <= inject_Z (Z.of_nat (S n))).
  { unfold Qle, inject_Z. simpl. lia. }
  assert (Hpos : 0 < inject_Z (Z.of_nat (S n))) by (apply inject_Z_Sn_pos).
  (* n * Sn <= Sn * Sn since n <= Sn *)
  assert (H : inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n)) <=
              inject_Z (Z.of_nat (S n)) * inject_Z (Z.of_nat (S n))).
  { apply Qmult_le_compat_r; [exact Hle | lra]. }
  exact H.
Qed.

(** Shifted telescoping: 1/(n*(n+1)) = 1/n - 1/(n+1) for n >= 1 *)
Lemma shifted_tele : forall n : nat,
  (1 <= n)%nat ->
  / (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))) ==
  / inject_Z (Z.of_nat n) - / inject_Z (Z.of_nat (S n)).
Proof.
  intros n Hn.
  assert (Ha : ~ inject_Z (Z.of_nat n) == 0).
  { destruct n; [lia|]. apply inject_Z_Sn_neq_0. }
  assert (Hb : ~ inject_Z (Z.of_nat (S n)) == 0) by (apply inject_Z_Sn_neq_0).
  (* 1/(n * Sn) == 1/n - 1/Sn *)
  (* Multiply both sides by n * Sn, reduces to Sn - n == 1 *)
  assert (Hprod_pos : 0 < inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))).
  { apply Qmult_lt_0_compat.
    - destruct n; [lia|]. apply inject_Z_Sn_pos.
    - apply inject_Z_Sn_pos. }
  assert (Hprod_neq : ~ inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n)) == 0).
  { lra. }
  (* LHS * (n * Sn) == 1 *)
  assert (Hlhs : / (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))) *
                 (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))) == 1).
  { field. split; assumption. }
  (* RHS * (n * Sn) == Sn - n == 1 *)
  assert (Hrhs : (/ inject_Z (Z.of_nat n) - / inject_Z (Z.of_nat (S n))) *
                 (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))) ==
                 inject_Z (Z.of_nat (S n)) - inject_Z (Z.of_nat n)).
  { field. split; assumption. }
  assert (Hdiff_eq : inject_Z (Z.of_nat (S n)) - inject_Z (Z.of_nat n) == 1).
  { rewrite Nat2Z.inj_succ.
    setoid_replace (inject_Z (Z.succ (Z.of_nat n)))
      with (inject_Z (Z.of_nat n) + 1)
      by (unfold inject_Z, Qeq, Qplus; simpl; lia).
    ring. }
  (* Both sides * (n * Sn) are equal *)
  assert (Hboth : / (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))) *
                  (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))) ==
                  (/ inject_Z (Z.of_nat n) - / inject_Z (Z.of_nat (S n))) *
                  (inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n)))).
  { rewrite Hlhs. rewrite Hrhs. symmetry. exact Hdiff_eq. }
  (* Cancel the nonzero factor *)
  assert (Hcancel : forall a b c : Q, ~ c == 0 -> a * c == b * c -> a == b).
  { intros a b c Hc Hac.
    assert (Hinv : c * / c == 1) by (field; exact Hc).
    setoid_replace a with (a * c * / c) by (field; exact Hc).
    setoid_replace b with (b * c * / c) by (field; exact Hc).
    apply Qmult_comp; [exact Hac | reflexivity]. }
  apply Hcancel with (c := inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))).
  - exact Hprod_neq.
  - exact Hboth.
Qed.

(** For n >= 1: 1/(n+1)^2 <= 1/n - 1/(n+1) *)
Lemma zeta_term_2_le_shifted_tele : forall n : nat,
  (1 <= n)%nat ->
  zeta_term 2 n <=
  / inject_Z (Z.of_nat n) - / inject_Z (Z.of_nat (S n)).
Proof.
  intros n Hn. unfold zeta_term, nat_power. simpl.
  assert (Hprod1 : 0 < inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))).
  { apply Qmult_lt_0_compat.
    - destruct n; [lia|]. apply inject_Z_Sn_pos.
    - apply inject_Z_Sn_pos. }
  assert (Hprod2 : 0 < inject_Z (Z.of_nat (S n)) * (inject_Z (Z.of_nat (S n)) * 1)).
  { assert (H := inject_Z_Sn_pos n).
    assert (H1 : inject_Z (Z.of_nat (S n)) * 1 == inject_Z (Z.of_nat (S n))) by ring.
    rewrite H1. apply Qmult_lt_0_compat; exact H. }
  rewrite <- shifted_tele by exact Hn.
  apply Qinv_le_compat; [lra|].
  setoid_replace (inject_Z (Z.of_nat (S n)) * (inject_Z (Z.of_nat (S n)) * 1))
    with (inject_Z (Z.of_nat (S n)) * inject_Z (Z.of_nat (S n))) by ring.
  apply sq_ge_consec_product. exact Hn.
Qed.

(** MAIN BOUND: zeta_partial k N <= 2 for k >= 2.
    Split: term 0 = 1, tail terms bounded by telescoping sum < 1. *)
Lemma zeta_partial_bounded : forall k N : nat,
  (2 <= k)%nat ->
  zeta_partial k N <= 2.
Proof.
  intros k N Hk. unfold zeta_partial.
  destruct N.
  - (* N = 0: single term = 1 *)
    simpl.
    assert (H := zeta_term_0_eq_1 k). lra.
  - (* N = S N': by induction on the partial sum *)
    assert (Hterm0 := zeta_term_0_eq_1 k).
    (* Bound tail terms: for i >= 1, zeta_term k i <= 1/i - 1/(i+1) *)
    assert (Htail : forall i, (1 <= i)%nat ->
      zeta_term k i <= / inject_Z (Z.of_nat i) - / inject_Z (Z.of_nat (S i))).
    { intros i Hi.
      assert (H2 : zeta_term k i <= zeta_term 2 i) by (apply zeta_term_k_monotone; exact Hk).
      assert (Htele : zeta_term 2 i <= / inject_Z (Z.of_nat i) - / inject_Z (Z.of_nat (S i)))
        by (apply zeta_term_2_le_shifted_tele; exact Hi).
      lra. }
    (* Prove: partial_sum (zeta_term k) (S M) <= 1 + (1 - 1/(S(S M))) *)
    assert (Hinduct : forall M,
      partial_sum (zeta_term k) (S M) <= 1 + (1 - / inject_Z (Z.of_nat (S (S M))))).
    { induction M.
      - (* M = 0: partial_sum (zeta_term k) (S 0) = zeta_term k 0 + zeta_term k (S 0) *)
        cbn [partial_sum].
        assert (Ht0_le : zeta_term k 0 <= 1).
        { assert (H := zeta_term_0_eq_1 k). lra. }
        assert (Ht1 := Htail 1%nat ltac:(lia)).
        assert (Hinv1 : / inject_Z (Z.of_nat 1) == 1).
        { unfold Qeq, inject_Z. simpl. lia. }
        setoid_replace (/ inject_Z (Z.of_nat 1)) with 1 in Ht1 by exact Hinv1.
        (* Ht1: zeta_term k 1 <= 1 - / inject_Z (Z.of_nat 2) *)
        (* Goal: zeta_term k 0 + zeta_term k 1 <= 1 + (1 - / inject_Z (Z.of_nat 2)) *)
        lra.
      - (* M = S M': inductive step *)
        replace (partial_sum (zeta_term k) (S (S M)))
          with (partial_sum (zeta_term k) (S M) + zeta_term k (S (S M)))
          by reflexivity.
        assert (Ht := Htail (S (S M)) ltac:(lia)).
        assert (Hpos_old : 0 < / inject_Z (Z.of_nat (S (S M)))).
        { apply Qinv_lt_0_compat. apply inject_Z_Sn_pos. }
        assert (Hpos_new : 0 < / inject_Z (Z.of_nat (S (S (S M))))).
        { apply Qinv_lt_0_compat. apply inject_Z_Sn_pos. }
        lra. }
    specialize (Hinduct N).
    assert (Hfrac_pos : 0 < / inject_Z (Z.of_nat (S (S N)))).
    { apply Qinv_lt_0_compat. apply inject_Z_Sn_pos. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: ZETA CONVERGENCE                                               *)
(* ========================================================================= *)

(** z(k) converges for k >= 2: the zeta process is Cauchy *)
Theorem zeta_process_cauchy : forall k : nat,
  (2 <= k)%nat ->
  is_cauchy (zeta_process k).
Proof.
  intros k Hk. unfold zeta_process.
  apply partial_sum_nonneg_bound with 2.
  - intros n. apply zeta_term_nonneg.
  - intros n. apply zeta_partial_bounded. exact Hk.
Qed.

(** Construct the Cauchy real z(k) for k >= 2 *)
Definition zeta_real (k : nat) (Hk : (2 <= k)%nat) : CauchySeq :=
  mkCauchy (zeta_process k) (zeta_process_cauchy k Hk).

(** z(k) >= 1 for all k *)
Lemma zeta_ge_1 : forall k N : nat,
  1 <= zeta_partial k N.
Proof.
  intros k N. unfold zeta_partial. induction N.
  - simpl. assert (H := zeta_term_0_eq_1 k). lra.
  - simpl. assert (Hnn := zeta_term_nonneg k (S N)). lra.
Qed.

(** z(k) is strictly increasing *)
Lemma zeta_partial_increasing : forall k N : nat,
  zeta_partial k N <= zeta_partial k (S N).
Proof.
  intros k N. unfold zeta_partial. simpl.
  assert (H := zeta_term_nonneg k (S N)). lra.
Qed.

(** z(k+2) <= z(k) pointwise *)
Lemma zeta_process_monotone_k : forall k1 k2 N : nat,
  (k1 <= k2)%nat ->
  zeta_partial k2 N <= zeta_partial k1 N.
Proof.
  intros k1 k2 N Hk. unfold zeta_partial.
  apply partial_sum_monotone.
  intros n. apply zeta_term_k_monotone. exact Hk.
Qed.

(* ========================================================================= *)
(* SECTION 5: HARMONIC DIVERGENCE                                            *)
(*                                                                           *)
(* z(1) = harmonic series diverges.                                          *)
(* Strategy: take eps = 1/4, get N0. Block from N0 to 2*N0+1 has            *)
(* N0+1 terms each >= 1/(2*(N0+1)), so block >= 1/2 > 1/4.                  *)
(* ========================================================================= *)

(** Harmonic term simplified: 1/(n+1) *)
Lemma harmonic_term_eq : forall n : nat,
  zeta_term 1 n == / inject_Z (Z.of_nat (S n)).
Proof.
  intros n. unfold zeta_term, nat_power. simpl.
  apply Qinv_comp. ring.
Qed.

(** Block sum bound: sum of K steps from N0, each term >= 1/(2*(N0+1)).
    partial_sum(N0+K) - partial_sum(N0) >= K/(2*(N0+1)). *)
Lemma harmonic_block_lower_bound : forall N0 K : nat,
  (K <= S N0)%nat ->
  partial_sum (zeta_term 1) (N0 + K) - partial_sum (zeta_term 1) N0 >=
  inject_Z (Z.of_nat K) * / inject_Z (Z.of_nat (2 * S N0)).
Proof.
  intros N0 K HK.
  induction K.
  - replace (N0 + 0)%nat with N0 by lia.
    setoid_replace (partial_sum (zeta_term 1) N0 - partial_sum (zeta_term 1) N0)
      with 0 by ring.
    assert (Hz : inject_Z (Z.of_nat 0) == 0) by (unfold Qeq, inject_Z; simpl; lia).
    setoid_replace (inject_Z (Z.of_nat 0) * / inject_Z (Z.of_nat (2 * S N0)))
      with 0 by (rewrite Hz; ring).
    lra.
  - assert (HK' : (K <= S N0)%nat) by lia.
    specialize (IHK HK').
    assert (Hrewrite : (N0 + S K = S (N0 + K))%nat) by lia.
    rewrite Hrewrite.
    simpl partial_sum.
    (* partial_sum(S(N0+K)) = partial_sum(N0+K) + zeta_term 1 (S(N0+K)) *)
    assert (Hterm_bound : zeta_term 1 (S (N0 + K)) >= / inject_Z (Z.of_nat (2 * S N0))).
    { rewrite harmonic_term_eq.
      assert (Hle : inject_Z (Z.of_nat (S (S (N0 + K)))) <=
                    inject_Z (Z.of_nat (2 * S N0))).
      { unfold Qle, inject_Z. simpl. lia. }
      assert (Hpos1 : 0 < inject_Z (Z.of_nat (S (S (N0 + K)))))
        by (apply inject_Z_Sn_pos).
      assert (Hpos2 : 0 < inject_Z (Z.of_nat (2 * S N0))).
      { unfold Qlt, inject_Z. simpl. lia. }
      apply Qinv_le_compat; lra. }
    assert (Hstep_eq : inject_Z (Z.of_nat (S K)) == inject_Z (Z.of_nat K) + 1).
    { rewrite Nat2Z.inj_succ.
      unfold Qeq, inject_Z, Qplus. simpl. lia. }
    assert (Hexpand : inject_Z (Z.of_nat (S K)) * / inject_Z (Z.of_nat (2 * S N0)) ==
                      inject_Z (Z.of_nat K) * / inject_Z (Z.of_nat (2 * S N0)) +
                      / inject_Z (Z.of_nat (2 * S N0))).
    { setoid_replace (inject_Z (Z.of_nat (S K)))
        with (inject_Z (Z.of_nat K) + 1) by exact Hstep_eq.
      ring. }
    rewrite Hexpand.
    lra.
Qed.

(** Harmonic series diverges: z(1) is NOT Cauchy *)
Theorem zeta_1_not_cauchy : ~ is_cauchy (partial_sum (zeta_term 1)).
Proof.
  intro Hcauchy.
  destruct (Hcauchy (1#4) ltac:(lra)) as [N0 HN0].
  (* Block from N0 to N0 + (S N0) = 2*N0+1 *)
  set (M := (2 * N0 + 1)%nat).
  specialize (HN0 M N0 ltac:(unfold M; lia) ltac:(lia)).
  apply Qabs_Qlt_condition in HN0. destruct HN0 as [Hlo Hhi].
  (* Block = partial_sum M - partial_sum N0 *)
  (* Use lemma with K = S N0: block >= (S N0)/(2*(S N0)) = 1/2 *)
  assert (HK_val : (N0 + S N0 = M)%nat) by (unfold M; lia).
  assert (Hblock := harmonic_block_lower_bound N0 (S N0) (Nat.le_refl (S N0))).
  rewrite HK_val in Hblock.
  (* RHS: (S N0) / (2 * S N0) = 1/2 *)
  assert (Hhalf : inject_Z (Z.of_nat (S N0)) * / inject_Z (Z.of_nat (2 * S N0)) == 1#2).
  { assert (H2sn : inject_Z (Z.of_nat (2 * S N0)) ==
                   2 * inject_Z (Z.of_nat (S N0))).
    { unfold Qeq, inject_Z. simpl. lia. }
    assert (Hpos : ~ inject_Z (Z.of_nat (S N0)) == 0).
    { apply inject_Z_Sn_neq_0. }
    rewrite H2sn. field. exact Hpos. }
  lra.
Qed.

(** Divergence restated for the zeta_process wrapper *)
Theorem zeta_diverges_at_1 : ~ is_cauchy (zeta_process 1).
Proof.
  exact zeta_1_not_cauchy.
Qed.

(* ========================================================================= *)
(* SECTION 6: ZETA PROCESS STRUCTURE                                         *)
(* ========================================================================= *)

(** z(k) as a GenProcess over Q *)
Definition zeta_gen_process (k : nat) : GenProcess Q :=
  zeta_process k.

(** z(k) is a Cauchy general process for k >= 2 *)
Lemma zeta_gen_cauchy : forall k : nat,
  (2 <= k)%nat ->
  is_cauchy_gen Qdist (zeta_gen_process k).
Proof.
  intros k Hk. unfold is_cauchy_gen, Qdist, zeta_gen_process.
  exact (zeta_process_cauchy k Hk).
Qed.

(** z(k) is monotone increasing *)
Lemma zeta_gen_monotone : forall k : nat,
  gen_monotone Qle (zeta_gen_process k).
Proof.
  intros k. unfold gen_monotone, zeta_gen_process, zeta_process.
  intros n. apply zeta_partial_increasing.
Qed.

(* ========================================================================= *)
(* SECTION 7: SUMMARY AND CHECKS                                             *)
(* ========================================================================= *)

Check nat_power.
Check nat_power_Sn_pos.
Check nat_power_Sn_neq_0.
Check nat_power_Sn_ge_1.
Check zeta_term.
Check zeta_term_pos.
Check zeta_term_nonneg.
Check zeta_term_le_1.
Check zeta_term_k_monotone.
Check zeta_term_0_eq_1.
Check sq_ge_consec_product.
Check shifted_tele.
Check zeta_term_2_le_shifted_tele.
Check zeta_partial_bounded.
Check zeta_process_cauchy.
Check zeta_real.
Check zeta_ge_1.
Check zeta_partial_increasing.
Check zeta_process_monotone_k.
Check harmonic_term_eq.
Check harmonic_block_lower_bound.
Check zeta_1_not_cauchy.
Check zeta_diverges_at_1.
Check zeta_gen_process.
Check zeta_gen_cauchy.
Check zeta_gen_monotone.

Print Assumptions zeta_process_cauchy.
Print Assumptions zeta_1_not_cauchy.
