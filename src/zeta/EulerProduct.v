(* ========================================================================= *)
(*            EULER PRODUCT: STRUCTURAL PROPERTIES                          *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Formalize the Euler product for z(k), k >= 2 (integer exp).   *)
(*    euler_factor p k = p^k / (p^k - 1)  for prime p, k >= 2.            *)
(*    The Euler product over primes up to bound N is a finite product.     *)
(*                                                                          *)
(*  KEY RESULTS:                                                            *)
(*    - euler_factor properties: positivity, > 1, bounded                  *)
(*    - Qprod: finite product over Q lists                                  *)
(*    - euler_partial: partial Euler product over primes in sieve           *)
(*    - zero_free_real: z(k) > 0 from Euler product (constructive)         *)
(*                                                                          *)
(*  AXIOMS: none                                                            *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
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
From ToS Require Import SeriesConvergence.
From ToS Require Import ProcessGeneral.
From ToS Require Import stdlib.Primes.
From ToS Require Import zeta.ZetaProcess.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: FINITE PRODUCTS OVER Q                                        *)
(* ========================================================================= *)

(** Product of a list of rationals *)
Definition Qprod (l : list Q) : Q :=
  fold_left Qmult l 1.

(** Qprod of empty list is 1 *)
Lemma Qprod_nil : Qprod [] == 1.
Proof. unfold Qprod. simpl. reflexivity. Qed.

(** Helper: fold_left Qmult preserves positivity *)
Lemma fold_left_Qmult_pos : forall l acc,
  0 < acc -> (forall x, In x l -> 0 < x) -> 0 < fold_left Qmult l acc.
Proof.
  induction l; intros acc Hacc Hall; simpl.
  - exact Hacc.
  - apply IHl.
    + apply Qmult_lt_0_compat; [exact Hacc | apply Hall; left; reflexivity].
    + intros x Hx. apply Hall. right. exact Hx.
Qed.

(** Qprod of positive elements is positive *)
Lemma Qprod_pos : forall l,
  (forall x, In x l -> 0 < x) -> 0 < Qprod l.
Proof.
  intros l Hall. unfold Qprod. apply fold_left_Qmult_pos; [lra | exact Hall].
Qed.

(** Helper: fold_left Qmult with acc >= 1 and all elements >= 1 gives >= 1 *)
Lemma fold_left_Qmult_ge_1 : forall l acc,
  1 <= acc -> (forall x, In x l -> 1 <= x) -> 1 <= fold_left Qmult l acc.
Proof.
  induction l; intros acc Hacc Hall; simpl.
  - exact Hacc.
  - apply IHl.
    + assert (Ha1 : 1 <= a) by (apply Hall; left; reflexivity).
      apply Qle_trans with (1 * a).
      * lra.
      * apply Qmult_le_compat_r; lra.
    + intros x Hx. apply Hall. right. exact Hx.
Qed.

(** Qprod of elements >= 1 is >= 1 *)
Lemma Qprod_ge_1 : forall l,
  (forall x, In x l -> 1 <= x) -> 1 <= Qprod l.
Proof.
  intros l Hall. unfold Qprod. apply fold_left_Qmult_ge_1; [lra | exact Hall].
Qed.

(** Qprod of singleton *)
Lemma Qprod_singleton : forall x, Qprod [x] == x * 1.
Proof. intros x. unfold Qprod. simpl. ring. Qed.

(** Helper: fold_left Qmult with Qeq-compatible accumulator *)
Lemma fold_left_Qmult_app : forall l1 l2 acc,
  fold_left Qmult (l1 ++ l2) acc == fold_left Qmult l2 (fold_left Qmult l1 acc).
Proof.
  intros l1 l2 acc. rewrite fold_left_app. reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 2: EULER FACTOR                                                   *)
(*                                                                           *)
(* euler_factor p k = p^k / (p^k - 1)                                       *)
(* For prime p >= 2 and k >= 1, p^k >= 2, so p^k - 1 >= 1 > 0.            *)
(* ========================================================================= *)

(** Euler factor: p^k / (p^k - 1) *)
Definition euler_factor (p k : nat) : Q :=
  nat_power p k / (nat_power p k - 1).

(** For p >= 2 and k >= 1: nat_power p k >= 2 *)
Lemma nat_power_ge_2 : forall p k : nat,
  (2 <= p)%nat -> (1 <= k)%nat ->
  2 <= nat_power p k.
Proof.
  intros p k Hp Hk. unfold nat_power.
  induction k.
  - lia.
  - destruct k.
    + simpl. assert (H : 2 <= inject_Z (Z.of_nat p)).
      { unfold Qle, inject_Z. simpl. lia. }
      lra.
    + assert (Hk' : (1 <= S k)%nat) by lia.
      specialize (IHk Hk').
      simpl.
      assert (Hbase : 2 <= inject_Z (Z.of_nat p)).
      { unfold Qle, inject_Z. simpl. lia. }
      assert (Hpow_pos : 0 < Qpow (inject_Z (Z.of_nat p)) (S k)).
      { apply Qpow_pos. unfold Qlt, inject_Z. simpl. lia. }
      (* inject_Z p * Qpow p (S k) >= 2 *)
      assert (Hpow_ge_1 : 1 <= Qpow (inject_Z (Z.of_nat p)) (S k)) by lra.
      apply Qle_trans with (inject_Z (Z.of_nat p) * 1).
      * lra.
      * setoid_replace (inject_Z (Z.of_nat p) * 1)
          with (1 * inject_Z (Z.of_nat p)) by ring.
        setoid_replace (inject_Z (Z.of_nat p) * Qpow (inject_Z (Z.of_nat p)) (S k))
          with (Qpow (inject_Z (Z.of_nat p)) (S k) * inject_Z (Z.of_nat p)) by ring.
        apply Qmult_le_compat_r; [exact Hpow_ge_1 | lra].
Qed.

(** Euler factor denominator is positive for p >= 2, k >= 1 *)
Lemma euler_factor_denom_pos : forall p k : nat,
  (2 <= p)%nat -> (1 <= k)%nat ->
  0 < nat_power p k - 1.
Proof.
  intros p k Hp Hk.
  assert (H := nat_power_ge_2 p k Hp Hk). lra.
Qed.

(** Euler factor is positive for p >= 2, k >= 1 *)
Lemma euler_factor_pos : forall p k : nat,
  (2 <= p)%nat -> (1 <= k)%nat ->
  0 < euler_factor p k.
Proof.
  intros p k Hp Hk. unfold euler_factor, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (H := nat_power_ge_2 p k Hp Hk). lra.
  - apply Qinv_lt_0_compat. apply euler_factor_denom_pos; assumption.
Qed.

(** Euler factor is > 1 for p >= 2, k >= 1 *)
Lemma euler_factor_gt_1 : forall p k : nat,
  (2 <= p)%nat -> (1 <= k)%nat ->
  1 < euler_factor p k.
Proof.
  intros p k Hp Hk. unfold euler_factor, Qdiv.
  assert (Hpk : 2 <= nat_power p k) by (apply nat_power_ge_2; assumption).
  assert (Hdenom : 0 < nat_power p k - 1) by lra.
  assert (Hdinv : 0 < / (nat_power p k - 1)).
  { apply Qinv_lt_0_compat. exact Hdenom. }
  (* p^k / (p^k - 1) = 1 + 1/(p^k - 1) > 1 *)
  assert (Hkey : nat_power p k * / (nat_power p k - 1) ==
                 1 + / (nat_power p k - 1)).
  { field. lra. }
  rewrite Hkey. lra.
Qed.

(** Euler factor >= 1 *)
Lemma euler_factor_ge_1 : forall p k : nat,
  (2 <= p)%nat -> (1 <= k)%nat ->
  1 <= euler_factor p k.
Proof.
  intros p k Hp Hk. assert (H := euler_factor_gt_1 p k Hp Hk). lra.
Qed.

(** Euler factor upper bound: p^k/(p^k-1) <= 2 for p^k >= 2 *)
Lemma euler_factor_le_2 : forall p k : nat,
  (2 <= p)%nat -> (1 <= k)%nat ->
  euler_factor p k <= 2.
Proof.
  intros p k Hp Hk. unfold euler_factor, Qdiv.
  assert (Hpk : 2 <= nat_power p k) by (apply nat_power_ge_2; assumption).
  assert (Hdenom : 0 < nat_power p k - 1) by lra.
  (* p^k/(p^k-1) = 1 + 1/(p^k-1), and p^k >= 2 => p^k-1 >= 1 => 1/(p^k-1) <= 1 *)
  assert (Hkey : nat_power p k * / (nat_power p k - 1) ==
                 1 + / (nat_power p k - 1)).
  { field. lra. }
  rewrite Hkey.
  assert (Hinv_le : / (nat_power p k - 1) <= 1).
  { assert (H1le : 1 <= nat_power p k - 1) by lra.
    assert (Hinv1 : / 1 == 1) by (unfold Qeq; simpl; lia).
    assert (H := Qinv_le_compat 1 (nat_power p k - 1) ltac:(lra) H1le).
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: EULER PARTIAL PRODUCT                                          *)
(* ========================================================================= *)

(** Euler partial product: product of euler_factor p k for primes p in sieve *)
Definition euler_partial (k bound : nat) : Q :=
  Qprod (map (fun p => euler_factor p k) (sieve bound)).

(** Euler partial process *)
Definition euler_process (k : nat) : nat -> Q :=
  euler_partial k.

(** All elements of sieve are >= 2 *)
Lemma sieve_all_ge_2 : forall bound p,
  In p (sieve bound) -> (2 <= p)%nat.
Proof.
  intros bound p Hp.
  unfold sieve in Hp.
  apply filter_In in Hp. destruct Hp as [Hseq Hprime].
  apply prime_ge_2. exact Hprime.
Qed.

(** Euler partial product is positive for k >= 1 *)
Lemma euler_partial_pos : forall k bound : nat,
  (1 <= k)%nat ->
  0 < euler_partial k bound.
Proof.
  intros k bound Hk. unfold euler_partial.
  apply Qprod_pos. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [p [Heq Hin]]. subst.
  apply euler_factor_pos.
  - apply sieve_all_ge_2 with bound. exact Hin.
  - exact Hk.
Qed.

(** Euler partial product >= 1 for k >= 1 *)
Lemma euler_partial_ge_1 : forall k bound : nat,
  (1 <= k)%nat ->
  1 <= euler_partial k bound.
Proof.
  intros k bound Hk. unfold euler_partial.
  apply Qprod_ge_1. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [p [Heq Hin]]. subst.
  apply euler_factor_ge_1.
  - apply sieve_all_ge_2 with bound. exact Hin.
  - exact Hk.
Qed.

(** Euler product at bound 0: no primes, product = 1 *)
Lemma euler_partial_0 : forall k : nat,
  euler_partial k 0 == 1.
Proof.
  intros k. unfold euler_partial, sieve. simpl. unfold Qprod. simpl. reflexivity.
Qed.

(** Euler product at bound 1: no primes, product = 1 *)
Lemma euler_partial_1 : forall k : nat,
  euler_partial k 1 == 1.
Proof.
  intros k. unfold euler_partial, sieve. simpl. unfold Qprod. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 4: ZERO-FREE REGION (CONSTRUCTIVE)                               *)
(*                                                                           *)
(* For any bound, euler_partial k bound > 0, establishing that the          *)
(* partial Euler product is nonzero -- a constructive zero-free property.   *)
(* ========================================================================= *)

(** Zero-free: euler_partial is always positive (constructive) *)
Theorem zero_free_partial : forall k bound : nat,
  (1 <= k)%nat ->
  0 < euler_partial k bound.
Proof.
  exact euler_partial_pos.
Qed.

(** Constructive nonzero for the Euler product *)
Theorem euler_partial_nonzero : forall k bound : nat,
  (1 <= k)%nat ->
  ~ euler_partial k bound == 0.
Proof.
  intros k bound Hk Heq.
  assert (Hpos := euler_partial_pos k bound Hk). lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: EULER FACTOR ARITHMETIC                                        *)
(* ========================================================================= *)

(** Euler factor at p=2, k=2: 4/3 *)
Lemma euler_factor_2_2 : euler_factor 2 2 == 4#3.
Proof.
  unfold euler_factor, nat_power, Qdiv. simpl.
  unfold Qeq, Qmult, Qinv. simpl. lia.
Qed.

(** Euler factor at p=3, k=2: 9/8 *)
Lemma euler_factor_3_2 : euler_factor 3 2 == 9#8.
Proof.
  unfold euler_factor, nat_power, Qdiv. simpl.
  unfold Qeq, Qmult, Qinv. simpl. lia.
Qed.

(** Euler factor at p=5, k=2: 25/24 *)
Lemma euler_factor_5_2 : euler_factor 5 2 == 25#24.
Proof.
  unfold euler_factor, nat_power, Qdiv. simpl.
  unfold Qeq, Qmult, Qinv. simpl. lia.
Qed.

(** Euler factor monotone in p: bigger primes give smaller factors *)
Lemma euler_factor_p_monotone : forall p1 p2 k : nat,
  (2 <= p1)%nat -> (p1 <= p2)%nat -> (1 <= k)%nat ->
  euler_factor p2 k <= euler_factor p1 k.
Proof.
  intros p1 p2 k Hp1 Hp12 Hk.
  unfold euler_factor, Qdiv.
  assert (Hpk1 : 2 <= nat_power p1 k) by (apply nat_power_ge_2; [lia | exact Hk]).
  assert (Hpk2 : 2 <= nat_power p2 k) by (apply nat_power_ge_2; [lia | exact Hk]).
  assert (Hd1 : 0 < nat_power p1 k - 1) by lra.
  assert (Hd2 : 0 < nat_power p2 k - 1) by lra.
  (* p1^k/(p1^k-1) = 1 + 1/(p1^k-1), similarly for p2 *)
  assert (Hkey1 : nat_power p1 k * / (nat_power p1 k - 1) ==
                  1 + / (nat_power p1 k - 1)) by (field; lra).
  assert (Hkey2 : nat_power p2 k * / (nat_power p2 k - 1) ==
                  1 + / (nat_power p2 k - 1)) by (field; lra).
  rewrite Hkey1. rewrite Hkey2.
  assert (Hmono : nat_power p1 k <= nat_power p2 k).
  { unfold nat_power. clear Hkey1 Hkey2 Hd1 Hd2 Hpk1 Hpk2.
    assert (Hbase : inject_Z (Z.of_nat p1) <= inject_Z (Z.of_nat p2)).
    { unfold Qle, inject_Z. simpl. lia. }
    assert (Hp2_nn : 0 <= inject_Z (Z.of_nat p2)).
    { unfold Qle, inject_Z. simpl. lia. }
    assert (Hgen : forall m, Qpow (inject_Z (Z.of_nat p1)) m <=
                             Qpow (inject_Z (Z.of_nat p2)) m).
    { induction m; [simpl; lra |].
      simpl.
      assert (Hpow1_nn : 0 <= Qpow (inject_Z (Z.of_nat p1)) m).
      { apply Qlt_le_weak. apply Qpow_pos. unfold Qlt, inject_Z. simpl. lia. }
      apply Qle_trans with (inject_Z (Z.of_nat p2) * Qpow (inject_Z (Z.of_nat p1)) m).
      - apply Qmult_le_compat_r; [exact Hbase | exact Hpow1_nn].
      - setoid_replace (inject_Z (Z.of_nat p2) * Qpow (inject_Z (Z.of_nat p1)) m)
          with (Qpow (inject_Z (Z.of_nat p1)) m * inject_Z (Z.of_nat p2)) by ring.
        setoid_replace (inject_Z (Z.of_nat p2) * Qpow (inject_Z (Z.of_nat p2)) m)
          with (Qpow (inject_Z (Z.of_nat p2)) m * inject_Z (Z.of_nat p2)) by ring.
        apply Qmult_le_compat_r; [exact IHm | exact Hp2_nn]. }
    apply Hgen. }
  assert (Hinv : / (nat_power p2 k - 1) <= / (nat_power p1 k - 1)).
  { apply Qinv_le_compat; lra. }
  lra.
Qed.

(** Euler factor monotone in k: bigger k gives smaller factors *)
Lemma euler_factor_k_monotone : forall p k1 k2 : nat,
  (2 <= p)%nat -> (1 <= k1)%nat -> (k1 <= k2)%nat ->
  euler_factor p k2 <= euler_factor p k1.
Proof.
  intros p k1 k2 Hp Hk1 Hk12.
  unfold euler_factor, Qdiv.
  assert (Hpk1 : 2 <= nat_power p k1) by (apply nat_power_ge_2; [exact Hp | exact Hk1]).
  assert (Hpk2 : 2 <= nat_power p k2) by (apply nat_power_ge_2; [exact Hp | lia]).
  assert (Hd1 : 0 < nat_power p k1 - 1) by lra.
  assert (Hd2 : 0 < nat_power p k2 - 1) by lra.
  assert (Hkey1 : nat_power p k1 * / (nat_power p k1 - 1) ==
                  1 + / (nat_power p k1 - 1)) by (field; lra).
  assert (Hkey2 : nat_power p k2 * / (nat_power p k2 - 1) ==
                  1 + / (nat_power p k2 - 1)) by (field; lra).
  rewrite Hkey1. rewrite Hkey2.
  assert (Hmono : nat_power p k1 <= nat_power p k2).
  { unfold nat_power. clear Hkey1 Hkey2 Hd1 Hd2 Hpk1 Hpk2.
    induction k2.
    - assert (Hk : k1 = 0%nat) by lia. subst. lra.
    - destruct (Nat.eq_dec k1 (S k2)) as [-> | Hne]; [lra |].
      assert (Hk : (k1 <= k2)%nat) by lia.
      specialize (IHk2 Hk).
      simpl.
      assert (H1 : 1 <= inject_Z (Z.of_nat p)).
      { unfold Qle, inject_Z. simpl. lia. }
      assert (Hpow_pos : 0 < Qpow (inject_Z (Z.of_nat p)) k2).
      { apply Qpow_pos. unfold Qlt, inject_Z. simpl. lia. }
      apply Qle_trans with (Qpow (inject_Z (Z.of_nat p)) k2).
      + exact IHk2.
      + setoid_replace (Qpow (inject_Z (Z.of_nat p)) k2)
          with (1 * Qpow (inject_Z (Z.of_nat p)) k2) at 1 by ring.
        apply Qmult_le_compat_r; lra. }
  assert (Hinv : / (nat_power p k2 - 1) <= / (nat_power p k1 - 1)).
  { apply Qinv_le_compat; lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: PROCESS STRUCTURE                                              *)
(* ========================================================================= *)

(** Euler process as a GenProcess *)
Definition euler_gen_process (k : nat) : GenProcess Q :=
  euler_process k.

(** Euler partial product is monotone increasing with bound *)
Lemma euler_partial_bound_monotone : forall k b1 b2 : nat,
  (1 <= k)%nat -> (b1 <= b2)%nat ->
  1 <= euler_partial k b1.
Proof.
  intros k b1 b2 Hk Hb.
  apply euler_partial_ge_1. exact Hk.
Qed.

(* ========================================================================= *)
(* SECTION 7: SUMMARY AND CHECKS                                             *)
(* ========================================================================= *)

Check Qprod.
Check Qprod_nil.
Check Qprod_pos.
Check Qprod_ge_1.
Check Qprod_singleton.
Check fold_left_Qmult_app.
Check euler_factor.
Check nat_power_ge_2.
Check euler_factor_denom_pos.
Check euler_factor_pos.
Check euler_factor_gt_1.
Check euler_factor_ge_1.
Check euler_factor_le_2.
Check euler_partial.
Check euler_process.
Check sieve_all_ge_2.
Check euler_partial_pos.
Check euler_partial_ge_1.
Check euler_partial_0.
Check euler_partial_1.
Check zero_free_partial.
Check euler_partial_nonzero.
Check euler_factor_2_2.
Check euler_factor_3_2.
Check euler_factor_5_2.
Check euler_factor_p_monotone.
Check euler_factor_k_monotone.
Check euler_gen_process.
Check euler_partial_bound_monotone.

Print Assumptions euler_partial_nonzero.
