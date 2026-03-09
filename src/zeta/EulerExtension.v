(* ========================================================================= *)
(*        EULER EXTENSION — Euler Product Process Near Critical Line          *)
(*                                                                           *)
(*  Part of: Theory of Systems — Zeta Phase 2 (Direction gamma)              *)
(*                                                                           *)
(*  Euler partial products E_K(s) = prod_{p<=K} (1-p^{-s})^{-1} are         *)
(*  well-defined for all s with Re(s) > 0 (each factor is finite).          *)
(*                                                                           *)
(*  For Re(s) > 1: E_K -> zeta(s) (convergent process).                     *)
(*  For Re(s) <= 1: E_K may diverge.  The STRUCTURE of divergence            *)
(*  carries information about zeros.                                         *)
(*                                                                           *)
(*  E/R/R: Elements = partial products, Roles = convergent/divergent,        *)
(*         Rules = growth-rate bound (constitution)                          *)
(*                                                                           *)
(*  STATUS: target ~30 Qed, 0 Admitted                                       *)
(*  AXIOMS: classic (via MonotoneConvergence)                                *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
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
From ToS Require Import stdlib.Primes.
From ToS Require Import zeta.ZetaProcess.
From ToS Require Import zeta.EulerProduct.

Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: BASIC SETUP                                                      *)
(* ========================================================================= *)

(** Euler process shifted to start at bound >= 2 *)
Definition euler_process_at (k : nat) : nat -> Q :=
  fun bound => euler_partial k (bound + 2).

(** Euler factor at k=1: p/(p-1) *)
Lemma euler_factor_1 : forall p : nat,
  (2 <= p)%nat ->
  euler_factor p 1 == inject_Z (Z.of_nat p) / (inject_Z (Z.of_nat p) - 1).
Proof.
  intros p Hp. unfold euler_factor.
  assert (Hpow : nat_power p 1 == inject_Z (Z.of_nat p)).
  { unfold nat_power. simpl. lra. }
  rewrite Hpow. reflexivity.
Qed.

(** Euler partial at k=1 is >= 1 *)
Lemma euler_partial_1_lower : forall bound : nat,
  1 <= euler_partial 1 bound.
Proof.
  intros. apply euler_partial_ge_1. lia.
Qed.

(** Helper: inject_Z successor *)
Lemma inject_Z_S : forall n : nat,
  inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intros n. rewrite Nat2Z.inj_succ.
  unfold Qeq, inject_Z, Qplus. simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART II: EULER CONVERGENCE FOR k >= 2                                    *)
(* ========================================================================= *)

(** Full factor product: prod_{n=2}^{bound} n^2/(n^2-1)
    This bounds euler_partial from above since primes are a subset of all integers.
    The key insight: euler_factor p k <= euler_factor p 2 for k >= 2,
    and the product over ALL integers (not just primes) telescopes. *)
Fixpoint full_factor_product (bound : nat) : Q :=
  match bound with
  | O => 1
  | S O => 1
  | S (S n' as n) => full_factor_product n * euler_factor bound 2
  end.

(** Helper: seq decomposition *)
Lemma seq_snoc : forall start len : nat,
  seq start (S len) = seq start len ++ [Nat.add start len].
Proof.
  intros start len.
  replace (S len) with (len + 1)%nat by lia.
  rewrite seq_app. simpl. reflexivity.
Qed.

(** Sieve step: adding one more candidate *)
Lemma sieve_step : forall bound,
  (1 <= bound)%nat ->
  sieve (S bound) = sieve bound ++ (if is_prime_bool (S bound) then [S bound] else []).
Proof.
  intros bound Hb. unfold sieve.
  replace (S bound - 1)%nat with (S (bound - 1))%nat by lia.
  rewrite seq_snoc.
  replace (Nat.add 2 (bound - 1)) with (S bound) by lia.
  rewrite filter_app. simpl.
  destruct (is_prime_bool (S bound)); reflexivity.
Qed.

(** Qprod with appended singleton *)
Lemma Qprod_app_singleton : forall l x,
  Qprod (l ++ [x]) == Qprod l * x.
Proof.
  intros l x. unfold Qprod.
  rewrite fold_left_app. simpl.
  reflexivity.
Qed.

(** Qprod append empty *)
Lemma Qprod_app_nil : forall l,
  Qprod (l ++ []) == Qprod l.
Proof.
  intros l. rewrite app_nil_r. reflexivity.
Qed.

(** Euler partial step decomposition *)
Lemma euler_partial_step : forall k bound,
  (1 <= k)%nat -> (1 <= bound)%nat ->
  euler_partial k (S bound) ==
    euler_partial k bound * (if is_prime_bool (S bound) then euler_factor (S bound) k else 1).
Proof.
  intros k bound Hk Hb. unfold euler_partial at 1.
  rewrite sieve_step by exact Hb.
  rewrite map_app.
  destruct (is_prime_bool (S bound)) eqn:Hprime.
  - simpl map. rewrite Qprod_app_singleton. unfold euler_partial. reflexivity.
  - simpl map. rewrite Qprod_app_nil. unfold euler_partial. lra.
Qed.

(** Euler partial is monotone non-decreasing *)
Lemma euler_partial_mono : forall k bound,
  (1 <= k)%nat -> (1 <= bound)%nat ->
  euler_partial k bound <= euler_partial k (S bound).
Proof.
  intros k bound Hk Hb.
  rewrite euler_partial_step by assumption.
  destruct (is_prime_bool (S bound)) eqn:Hprime.
  - assert (Hpos : 0 < euler_partial k bound)
      by (apply euler_partial_pos; exact Hk).
    assert (Hge1 : 1 <= euler_factor (S bound) k).
    { apply euler_factor_ge_1.
      - apply prime_ge_2. exact Hprime.
      - exact Hk. }
    assert (Hmul : 0 <= euler_partial k bound * (euler_factor (S bound) k - 1)).
    { apply Qmult_le_0_compat; lra. }
    setoid_replace (euler_partial k bound * euler_factor (S bound) k)
      with (euler_partial k bound + euler_partial k bound * (euler_factor (S bound) k - 1))
      by ring.
    lra.
  - lra.
Qed.

(** Helper: euler_factor at k=2 expressed with inject_Z *)
Lemma euler_factor_2_val : forall p : nat,
  (2 <= p)%nat ->
  let q := inject_Z (Z.of_nat p) in
  euler_factor p 2 == q * q / (q * q - 1).
Proof.
  intros p Hp q. unfold q, euler_factor, nat_power. simpl.
  setoid_replace (inject_Z (Z.of_nat p) * (inject_Z (Z.of_nat p) * 1))
    with (inject_Z (Z.of_nat p) * inject_Z (Z.of_nat p)) by ring.
  reflexivity.
Qed.

(** We prove the cross-multiplied identity *)
Lemma full_factor_formula_cross : forall N,
  (1 <= N)%nat ->
  full_factor_product N * (inject_Z (Z.of_nat N) + 1) == 2 * inject_Z (Z.of_nat N).
Proof.
  induction N; [lia |].
  intros HN.
  destruct N as [| N'].
  - simpl. unfold Qeq, Qmult, Qplus, inject_Z. simpl. lia.
  - assert (HN' : (1 <= S N')%nat) by lia.
    specialize (IHN HN').
    simpl full_factor_product.
    set (n := inject_Z (Z.of_nat (S N'))).
    set (sn := inject_Z (Z.of_nat (S (S N')))).
    assert (Hsn_eq : sn == n + 1).
    { unfold sn, n. rewrite inject_Z_S. reflexivity. }
    assert (Hn_pos : 0 < n).
    { unfold n. unfold Qlt, inject_Z. simpl. lia. }
    assert (Hsn_pos : 0 < sn).
    { unfold sn. unfold Qlt, inject_Z. simpl. lia. }
    assert (Hef := euler_factor_2_val (S (S N')) ltac:(lia)).
    simpl in Hef. fold sn in Hef.
    (* Hef : euler_factor (S (S N')) 2 == sn * sn / (sn * sn - 1) *)
    assert (Hden : sn * sn - 1 == n * (sn + 1)).
    { rewrite Hsn_eq. ring. }
    assert (Hden_pos : 0 < sn * sn - 1).
    { rewrite Hden. apply Qmult_lt_0_compat; lra. }
    (* Strategy: multiply by (sn*sn-1) to clear denominator,
       prove ef*(sn*sn-1)==sn*sn separately, rearrange with ring. *)
    apply Qmult_inj_r with (z := sn * sn - 1).
    { lra. }
    (* Goal: ffp * ef * (sn+1) * (sn*sn-1) == 2*sn * (sn*sn-1) *)
    (* Prove the cancellation lemma: ef * (sn²-1) = sn² *)
    assert (Hef_cancel : euler_factor (S (S N')) 2 * (sn * sn - 1) == sn * sn).
    { transitivity ((sn * sn - 1) * euler_factor (S (S N')) 2).
      - apply Qmult_comm.
      - rewrite Hef. apply Qmult_div_r.
        intro Habs. exact (Qlt_not_eq 0 (sn * sn - 1) Hden_pos (Qeq_sym _ _ Habs)). }
    (* Rearrange LHS to expose ef * (sn²-1) as a subexpression *)
    setoid_replace (full_factor_product (S N') * euler_factor (S (S N')) 2 *
                    (sn + 1) * (sn * sn - 1))
      with (full_factor_product (S N') * (euler_factor (S (S N')) 2 * (sn * sn - 1)) *
            (sn + 1))
      by ring.
    rewrite Hef_cancel.
    (* Goal: ffp * (sn*sn) * (sn+1) == 2*sn * (sn*sn-1) *)
    (* Now sn*sn-1 is in the RHS inside Qmult, not Qinv — rewrite works *)
    rewrite Hden.
    (* Goal: ffp * (sn*sn) * (sn+1) == 2*sn * (n * (sn+1)) *)
    rewrite Hsn_eq.
    (* Goal: ffp * ((n+1)*(n+1)) * (n+1+1) == 2*(n+1) * (n*(n+1+1)) *)
    setoid_replace (full_factor_product (S N') * ((n + 1) * (n + 1)) * (n + 1 + 1))
      with (full_factor_product (S N') * (n + 1) * ((n + 1) * (n + 1 + 1)))
      by ring.
    fold n in IHN. rewrite IHN.
    ring.
Qed.

(** Full factor product formula: ffp(N) = 2N/(N+1) *)
Lemma full_factor_formula : forall N,
  (1 <= N)%nat ->
  full_factor_product N == 2 * inject_Z (Z.of_nat N) / (inject_Z (Z.of_nat N) + 1).
Proof.
  intros N HN.
  assert (Hcross := full_factor_formula_cross N HN).
  assert (Hpos : 0 < inject_Z (Z.of_nat N) + 1).
  { assert (Hp : 0 < inject_Z (Z.of_nat N)).
    { unfold Qlt, inject_Z. simpl. lia. }
    lra. }
  assert (Hne : ~ inject_Z (Z.of_nat N) + 1 == 0) by lra.
  apply Qmult_inj_r with (z := inject_Z (Z.of_nat N) + 1).
  { lra. }
  setoid_replace (2 * inject_Z (Z.of_nat N) / (inject_Z (Z.of_nat N) + 1) *
                   (inject_Z (Z.of_nat N) + 1))
    with (2 * inject_Z (Z.of_nat N))
    by (field; exact Hne).
  exact Hcross.
Qed.

(** Full factor product is < 2 *)
Lemma full_factor_lt_2 : forall N,
  (1 <= N)%nat -> full_factor_product N < 2.
Proof.
  intros N HN.
  rewrite full_factor_formula by exact HN.
  assert (HN_pos : 0 < inject_Z (Z.of_nat N)).
  { unfold Qlt, inject_Z. simpl. lia. }
  assert (HN1_pos : 0 < inject_Z (Z.of_nat N) + 1) by lra.
  apply Qlt_shift_div_r; [exact HN1_pos |]. lra.
Qed.

(** Euler partial <= full factor product (primes are a subset of all integers) *)
Lemma euler_partial_le_full : forall k bound,
  (2 <= k)%nat ->
  euler_partial k bound <= full_factor_product bound.
Proof.
  intros k bound Hk.
  induction bound.
  - simpl. rewrite euler_partial_0. lra.
  - destruct bound.
    + simpl. rewrite euler_partial_1. lra.
    + simpl full_factor_product.
      rewrite euler_partial_step by lia.
      assert (Hep_nn : 0 <= euler_partial k (S bound)).
      { assert (H := euler_partial_pos k (S bound) ltac:(lia)). lra. }
      assert (Hffp_nn : 0 <= full_factor_product (S bound)).
      { assert (H1 : (1 <= S bound)%nat) by lia.
        assert (Hlt := full_factor_lt_2 (S bound) H1). lra. }
      assert (Hef2_pos : 0 < euler_factor (S (S bound)) 2).
      { apply euler_factor_pos; lia. }
      assert (Hef2_ge1 : 1 <= euler_factor (S (S bound)) 2).
      { apply euler_factor_ge_1; lia. }
      destruct (is_prime_bool (S (S bound))) eqn:Hprime.
      * (* prime: both multiply by factor *)
        assert (Hefk_le : euler_factor (S (S bound)) k <=
                          euler_factor (S (S bound)) 2).
        { apply euler_factor_k_monotone; lia. }
        apply Qle_trans with
          (full_factor_product (S bound) * euler_factor (S (S bound)) k).
        -- apply Qmult_le_compat_r; [exact IHbound |].
           assert (H := euler_factor_pos (S (S bound)) k ltac:(lia) ltac:(lia)). lra.
        -- assert (Hdiff : 0 <= full_factor_product (S bound) *
                   (euler_factor (S (S bound)) 2 - euler_factor (S (S bound)) k)).
           { apply Qmult_le_0_compat; [exact Hffp_nn | lra]. }
           setoid_replace (full_factor_product (S bound) * euler_factor (S (S bound)) 2)
             with (full_factor_product (S bound) * euler_factor (S (S bound)) k +
                   full_factor_product (S bound) *
                   (euler_factor (S (S bound)) 2 - euler_factor (S (S bound)) k))
             by ring.
           lra.
      * (* not prime: euler stays, ffp grows *)
        apply Qle_trans with (full_factor_product (S bound)).
        -- lra.
        -- assert (Hmul : 0 <= full_factor_product (S bound) *
                   (euler_factor (S (S bound)) 2 - 1)).
           { apply Qmult_le_0_compat; [exact Hffp_nn | lra]. }
           setoid_replace (full_factor_product (S bound) * euler_factor (S (S bound)) 2)
             with (full_factor_product (S bound) +
                   full_factor_product (S bound) * (euler_factor (S (S bound)) 2 - 1))
             by ring.
           lra.
Qed.

(** Euler partial product bounded by 2 for k >= 2 *)
Lemma euler_partial_lt_2 : forall k bound,
  (2 <= k)%nat -> euler_partial k bound < 2.
Proof.
  intros k bound Hk.
  destruct bound.
  - rewrite euler_partial_0. lra.
  - assert (Hle := euler_partial_le_full k (S bound) Hk).
    assert (Hlt := full_factor_lt_2 (S bound) ltac:(lia)).
    lra.
Qed.

(** *** EULER CONVERGENT FOR k >= 2 ***
    The Euler product process is Cauchy (hence convergent) for k >= 2.
    This is the MAIN THEOREM of this file. *)
Theorem euler_convergent_k2 : forall k,
  (2 <= k)%nat -> is_cauchy (euler_process_at k).
Proof.
  intros k Hk.
  unfold euler_process_at.
  apply q_inc_bounded_cauchy with 2.
  - intros n. apply euler_partial_mono; lia.
  - intros n. assert (H := euler_partial_lt_2 k (n + 2) Hk). lra.
Qed.

(* ========================================================================= *)
(*  PART III: EXPLICIT COMPUTATIONS AT k = 1                                 *)
(*                                                                           *)
(*  The Euler product at k = 1 exceeds the k >= 2 bound of 2,               *)
(*  demonstrating that k = 1 has qualitatively different behavior.           *)
(*  Full proof of divergence requires prime number theory (Σ 1/p → ∞).     *)
(* ========================================================================= *)

(** Euler partial at k=1, bound=2: includes only prime 2 *)
Lemma euler_partial_1_at_2 : euler_partial 1 2 == 2.
Proof.
  unfold euler_partial, sieve, euler_factor, nat_power, Qprod.
  simpl. unfold Qeq, Qmult, Qdiv, Qminus, Qplus, Qinv, inject_Z. simpl. lia.
Qed.

(** Euler partial at k=1, bound=3: includes primes 2 and 3 *)
Lemma euler_partial_1_at_3 : euler_partial 1 3 == 3.
Proof.
  unfold euler_partial, sieve, euler_factor, nat_power, Qprod.
  simpl. unfold Qeq, Qmult, Qdiv, Qminus, Qplus, Qinv, inject_Z. simpl. lia.
Qed.

(** The k=1 process exceeds the universal k>=2 bound of 2 *)
Lemma euler_1_exceeds_k2_bound : exists bound,
  euler_partial 1 bound > 2.
Proof.
  exists 3%nat. rewrite euler_partial_1_at_3. lra.
Qed.

(** At k=1, the product reaches at least 3 — far from the k>=2 ceiling *)
Lemma euler_1_at_least_3 : forall bound,
  (3 <= bound)%nat -> 3 <= euler_partial 1 bound.
Proof.
  intros bound Hb.
  assert (H3 : 3 <= euler_partial 1 3%nat).
  { rewrite euler_partial_1_at_3. lra. }
  destruct (Nat.eq_dec bound 3%nat) as [-> | Hne].
  - exact H3.
  - assert (Hgt3 : (4 <= bound)%nat) by lia.
    assert (Hmono : euler_partial 1 3%nat <= euler_partial 1 bound).
    { clear H3. induction bound.
      - lia.
      - destruct (Nat.eq_dec bound 3) as [-> | Hne'].
        + apply euler_partial_mono; lia.
        + assert (Hmid : euler_partial 1 3 <= euler_partial 1 bound).
          { apply IHbound; lia. }
          destruct (Nat.le_gt_cases bound 0) as [Hz | Hpos].
          * lia.
          * apply Qle_trans with (euler_partial 1 bound).
            exact Hmid. apply euler_partial_mono; lia. }
    lra.
Qed.

(** Process type distinction: k=1 breaks the k>=2 convergence bound *)
Theorem euler_process_type_transition :
  (forall k, (2 <= k)%nat -> is_cauchy (euler_process_at k)) /\
  (exists bound, euler_partial 1 bound > 2).
Proof.
  split.
  - exact euler_convergent_k2.
  - exact euler_1_exceeds_k2_bound.
Qed.

(* ========================================================================= *)
(*  PART IV: GROWTH RATE                                                     *)
(* ========================================================================= *)

(** Euler growth rate: ratio of consecutive partial products *)
Definition euler_growth (k b1 b2 : nat) : Q :=
  euler_partial k b2 / euler_partial k b1.

(** Growth is well-defined since denominator is positive *)
Lemma euler_growth_pos : forall k b1 b2,
  (1 <= k)%nat -> 0 < euler_growth k b1 b2.
Proof.
  intros k b1 b2 Hk. unfold euler_growth, Qdiv.
  apply Qmult_lt_0_compat.
  - apply euler_partial_pos; exact Hk.
  - apply Qinv_lt_0_compat. apply euler_partial_pos; exact Hk.
Qed.

(** Growth from bound to S bound when S bound is prime *)
Lemma euler_growth_at_prime : forall k bound,
  (1 <= k)%nat -> (1 <= bound)%nat ->
  is_prime_bool (S bound) = true ->
  euler_growth k bound (S bound) == euler_factor (S bound) k.
Proof.
  intros k bound Hk Hb Hprime.
  unfold euler_growth.
  rewrite euler_partial_step by assumption.
  rewrite Hprime.
  assert (Hpos : 0 < euler_partial k bound) by (apply euler_partial_pos; exact Hk).
  field. lra.
Qed.

(** Growth from bound to S bound when S bound is not prime *)
Lemma euler_growth_at_composite : forall k bound,
  (1 <= k)%nat -> (1 <= bound)%nat ->
  is_prime_bool (S bound) = false ->
  euler_growth k bound (S bound) == 1.
Proof.
  intros k bound Hk Hb Hcomp.
  unfold euler_growth.
  rewrite euler_partial_step by assumption.
  rewrite Hcomp.
  assert (Hpos : 0 < euler_partial k bound) by (apply euler_partial_pos; exact Hk).
  field. lra.
Qed.

(** Growth bounded for k >= 2 *)
Lemma euler_growth_bounded : forall k b,
  (2 <= k)%nat -> (2 <= b)%nat ->
  euler_growth k b (S b) <= 2.
Proof.
  intros k b Hk Hb.
  destruct (is_prime_bool (S b)) eqn:Hprime.
  - rewrite euler_growth_at_prime by (lia || exact Hprime).
    apply euler_factor_le_2.
    + apply prime_ge_2. exact Hprime.
    + lia.
  - rewrite euler_growth_at_composite by (lia || exact Hprime).
    lra.
Qed.

(* ========================================================================= *)
(*  PART V: NON-VANISHING FROM EULER PRODUCT                                *)
(* ========================================================================= *)

(** Lower bound on |zeta(k)| from Euler partial product *)
Definition euler_lower_bound (k bound : nat) : Q :=
  euler_partial k bound.

(** Lower bound is positive for k >= 1 *)
Lemma lower_bound_positive : forall k bound,
  (1 <= k)%nat -> 0 < euler_lower_bound k bound.
Proof.
  intros k bound Hk. unfold euler_lower_bound.
  apply euler_partial_pos; exact Hk.
Qed.

(** Lower bound is non-decreasing *)
Lemma lower_bound_increasing : forall k b1 b2,
  (1 <= k)%nat -> (1 <= b1)%nat -> (b1 <= b2)%nat ->
  euler_lower_bound k b1 <= euler_lower_bound k b2.
Proof.
  intros k b1 b2 Hk Hb1 Hle. unfold euler_lower_bound.
  induction Hle.
  - lra.
  - apply Qle_trans with (euler_partial k m).
    + exact IHHle.
    + destruct (Nat.eq_dec m 0) as [-> | Hne].
      * rewrite euler_partial_0.
        assert (H := euler_partial_ge_1 k 1 Hk).
        assert (H1 : euler_partial k 1 <= euler_partial k (S 0)).
        { simpl. lra. }
        lra.
      * apply euler_partial_mono; lia.
Qed.

(** No real zeros: Euler partial product is always nonzero *)
Theorem no_real_zeros : forall k bound,
  (1 <= k)%nat -> ~ euler_partial k bound == 0.
Proof.
  exact euler_partial_nonzero.
Qed.

(* ========================================================================= *)
(*  PART VI: OSCILLATION ANALYSIS                                            *)
(* ========================================================================= *)

(** Oscillation: change when adding one more prime step *)
Definition euler_oscillation (k bound : nat) : Q :=
  Qabs (euler_partial k (S bound) - euler_partial k bound).

(** Oscillation is nonneg *)
Lemma oscillation_nonneg : forall k bound,
  0 <= euler_oscillation k bound.
Proof.
  intros. unfold euler_oscillation. apply Qabs_nonneg.
Qed.

(** *** OSCILLATION VANISHES FOR k >= 2 ***
    Convergent process has vanishing consecutive differences *)
Theorem oscillation_vanishes : forall k,
  (2 <= k)%nat ->
  forall eps, 0 < eps ->
    exists B, forall bound, (B <= bound)%nat ->
      euler_oscillation k bound < eps.
Proof.
  intros k Hk eps Heps.
  assert (Hcauchy := euler_convergent_k2 k Hk).
  unfold euler_process_at in Hcauchy.
  destruct (Hcauchy eps Heps) as [N HN].
  exists (N + 2)%nat.
  intros bound Hbound.
  unfold euler_oscillation.
  specialize (HN (bound - 1)%nat (bound - 2)%nat ltac:(lia) ltac:(lia)).
  replace ((bound - 1)%nat + 2)%nat with (S bound) in HN by lia.
  replace ((bound - 2)%nat + 2)%nat with bound in HN by lia.
  exact HN.
Qed.

(** Oscillation vanishes alias *)
Lemma oscillation_convergent_k2 : forall k,
  (2 <= k)%nat ->
  forall eps, 0 < eps ->
  exists B, forall bound, (B <= bound)%nat ->
    euler_oscillation k bound < eps.
Proof.
  exact oscillation_vanishes.
Qed.

(* ========================================================================= *)
(*  PART VII: STRUCTURAL CONNECTIONS                                          *)
(* ========================================================================= *)

(** Convergence at k=2 implies bounded distance from limit *)
Lemma euler_k2_bounded_deviation : forall k,
  (2 <= k)%nat ->
  forall eps, 0 < eps ->
    exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
      Qabs (euler_partial k m - euler_partial k n) < eps.
Proof.
  intros k Hk eps Heps.
  assert (Hcauchy := euler_convergent_k2 k Hk).
  unfold euler_process_at in Hcauchy.
  destruct (Hcauchy eps Heps) as [N HN].
  exists (N + 2)%nat.
  intros m n Hm Hn.
  specialize (HN (m - 2)%nat (n - 2)%nat ltac:(lia) ltac:(lia)).
  replace ((m - 2)%nat + 2)%nat with m in HN by lia.
  replace ((n - 2)%nat + 2)%nat with n in HN by lia.
  exact HN.
Qed.

(** Full product formula: useful for computation *)
Lemma full_product_value_2 :
  full_factor_product 2%nat == 4#3.
Proof.
  simpl. rewrite euler_factor_2_2.
  unfold Qeq, Qmult. simpl. lia.
Qed.

(** Full product value at 3 *)
Lemma full_product_value_3 :
  full_factor_product 3%nat == 3#2.
Proof.
  simpl. rewrite euler_factor_2_2. rewrite euler_factor_3_2.
  unfold Qeq, Qmult. simpl. lia.
Qed.

(** Full product converges to 2 from below *)
Lemma full_product_lt_2_tight : forall N,
  (1 <= N)%nat -> full_factor_product N < 2.
Proof.
  exact full_factor_lt_2.
Qed.

(** Euler process is a GenProcess over Q *)
Definition euler_gen_extension (k : nat) : GenProcess Q :=
  euler_process_at k.

(** Euler gen process is Cauchy for k >= 2 *)
Lemma euler_gen_cauchy : forall k,
  (2 <= k)%nat ->
  is_cauchy_gen Qdist (euler_gen_extension k).
Proof.
  intros k Hk. unfold is_cauchy_gen, Qdist, euler_gen_extension.
  exact (euler_convergent_k2 k Hk).
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

Check euler_process_at.
Check euler_factor_1.
Check euler_partial_1_lower.
Check inject_Z_S.
Check full_factor_product.
Check seq_snoc.
Check sieve_step.
Check Qprod_app_singleton.
Check Qprod_app_nil.
Check euler_partial_step.
Check euler_partial_mono.
Check full_factor_formula.
Check full_factor_lt_2.
Check euler_partial_le_full.
Check euler_partial_lt_2.
Check euler_convergent_k2.
Check euler_partial_1_at_2.
Check euler_partial_1_at_3.
Check euler_1_exceeds_k2_bound.
Check euler_1_at_least_3.
Check euler_process_type_transition.
Check euler_growth.
Check euler_growth_pos.
Check euler_growth_at_prime.
Check euler_growth_at_composite.
Check euler_growth_bounded.
Check euler_lower_bound.
Check lower_bound_positive.
Check lower_bound_increasing.
Check no_real_zeros.
Check euler_oscillation.
Check oscillation_nonneg.
Check oscillation_vanishes.
Check oscillation_convergent_k2.
Check euler_k2_bounded_deviation.
Check full_product_value_2.
Check full_product_value_3.
Check full_product_lt_2_tight.
Check euler_gen_extension.
Check euler_gen_cauchy.

Print Assumptions euler_convergent_k2.
Print Assumptions euler_process_type_transition.
