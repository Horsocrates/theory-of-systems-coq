(**
  BernoulliNumbers.v — Exact Rational Bernoulli Numbers
  =====================================================

  File 1 of 4 in the Experimental Verification module.

  Bernoulli numbers B_n defined by the recursion:
    B₀ = 1
    Σ_{k=0}^{n} C(n+1,k) · B_k = 0  for n ≥ 1

  All Bernoulli numbers are RATIONAL — exact in our Q framework.
  No approximation needed.

  Key values:
    B₀ = 1, B₁ = -1/2, B₂ = 1/6, B₃ = 0, B₄ = -1/30,
    B₅ = 0, B₆ = 1/42, B₇ = 0, B₈ = -1/30

  Connection to ζ: ζ(-k) = -B_{k+1}/(k+1) for k ≥ 0.
  Connection to Casimir: energy involves ζ(-3) = 1/120.

  Depends on: stdlib/Combinatorics, SeriesConvergence, CauchyReal
  STATUS: target ~30 Qed, 0 Admitted
  AXIOMS: none (exact rational computation)
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import stdlib.Combinatorics.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyReal.
From ToS Require Import MonotoneConvergence.

(* ========================================================================= *)
(*                PART I: Q-VALUED HELPERS                                    *)
(* ========================================================================= *)

(** Binomial coefficient as Q *)
Definition qbinom (n k : nat) : Q :=
  inject_Z (Z.of_nat (binomial n k)).

(** Factorial as Q *)
Definition qfact (n : nat) : Q :=
  inject_Z (Z.of_nat (fact n)).

(** qfact is always positive *)
Lemma qfact_pos : forall n, 0 < qfact n.
Proof.
  intros n. unfold qfact.
  assert (H : (1 <= fact n)%nat) by apply fact_pos.
  unfold Qlt. simpl. lia.
Qed.

(** qbinom n 0 = 1 *)
Lemma qbinom_0_r : forall n, qbinom n 0 == 1.
Proof.
  intros n. unfold qbinom. rewrite binomial_0_r. reflexivity.
Qed.

(** qbinom n n = 1 *)
Lemma qbinom_n_n : forall n, qbinom n n == 1.
Proof.
  intros n. unfold qbinom. rewrite binomial_n_n. reflexivity.
Qed.

(** qbinom when k > n is 0 *)
Lemma qbinom_gt : forall n k, (n < k)%nat -> qbinom n k == 0.
Proof.
  intros n k H. unfold qbinom. rewrite binomial_gt by exact H. reflexivity.
Qed.

(* ========================================================================= *)
(*                PART II: BERNOULLI NUMBERS VIA RECURSION                    *)
(* ========================================================================= *)

(**
  Bernoulli numbers computed iteratively.
  bernoulli_list n returns [B_0, B_1, ..., B_n].

  The recursion: B_0 = 1, and for n >= 1:
    B_n = -1/(n+1) * Σ_{k=0}^{n-1} C(n+1,k) * B_k
*)

Fixpoint bernoulli_list (n : nat) : list Q :=
  match n with
  | O => [1]
  | S m =>
    let prev := bernoulli_list m in
    let new_b := -(1) / inject_Z (Z.of_nat (S (S m))) *
      partial_sum (fun k => inject_Z (Z.of_nat (binomial (S (S m)) k)) *
                            nth k prev 0) m
    in prev ++ [new_b]
  end.

(** Extract the n-th Bernoulli number *)
Definition bernoulli (n : nat) : Q := nth n (bernoulli_list n) 0.

(** bernoulli_list n has length S n *)
Lemma bernoulli_list_length : forall n,
  length (bernoulli_list n) = S n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite app_length. rewrite IH. simpl. lia.
Qed.

(* ========================================================================= *)
(*                PART III: VERIFIED CONCRETE VALUES                          *)
(* ========================================================================= *)

(** B₀ = 1 *)
Lemma B0_value : bernoulli 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** B₁ = -1/2 *)
Lemma B1_value : bernoulli 1 == -(1#2).
Proof. vm_compute. reflexivity. Qed.

(** B₂ = 1/6 *)
Lemma B2_value : bernoulli 2 == (1#6).
Proof. vm_compute. reflexivity. Qed.

(** B₃ = 0 *)
Lemma B3_value : bernoulli 3 == 0.
Proof. vm_compute. reflexivity. Qed.

(** B₄ = -1/30 *)
Lemma B4_value : bernoulli 4 == -(1#30).
Proof. vm_compute. reflexivity. Qed.

(** B₅ = 0 *)
Lemma B5_value : bernoulli 5 == 0.
Proof. vm_compute. reflexivity. Qed.

(** B₆ = 1/42 *)
Lemma B6_value : bernoulli 6 == (1#42).
Proof. vm_compute. reflexivity. Qed.

(** B₇ = 0 *)
Lemma B7_value : bernoulli 7 == 0.
Proof. vm_compute. reflexivity. Qed.

(** B₈ = -1/30 *)
Lemma B8_value : bernoulli 8 == -(1#30).
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*                PART IV: PROPERTIES OF BERNOULLI NUMBERS                    *)
(* ========================================================================= *)

(** Odd Bernoulli numbers vanish for n ≥ 3 *)
Lemma B_odd_3 : bernoulli 3 == 0.
Proof. exact B3_value. Qed.

Lemma B_odd_5 : bernoulli 5 == 0.
Proof. exact B5_value. Qed.

Lemma B_odd_7 : bernoulli 7 == 0.
Proof. exact B7_value. Qed.

(** Signs alternate for even Bernoulli numbers *)
Lemma B2_pos : 0 < bernoulli 2.
Proof.
  assert (H : bernoulli 2 == (1#6)) by (vm_compute; reflexivity).
  setoid_rewrite H. lra.
Qed.

Lemma B4_neg : bernoulli 4 < 0.
Proof.
  assert (H : bernoulli 4 == -(1#30)) by (vm_compute; reflexivity).
  setoid_rewrite H. lra.
Qed.

Lemma B6_pos : 0 < bernoulli 6.
Proof.
  assert (H : bernoulli 6 == (1#42)) by (vm_compute; reflexivity).
  setoid_rewrite H. lra.
Qed.

(** The Bernoulli recursion identity:
    Σ_{k=0}^{n} C(n+1,k) * B_k = 0 for n >= 1 *)
Theorem bernoulli_recursion_1 :
  partial_sum (fun k => qbinom 2 k * bernoulli k) 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem bernoulli_recursion_2 :
  partial_sum (fun k => qbinom 3 k * bernoulli k) 2 == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem bernoulli_recursion_3 :
  partial_sum (fun k => qbinom 4 k * bernoulli k) 3 == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem bernoulli_recursion_4 :
  partial_sum (fun k => qbinom 5 k * bernoulli k) 4 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*                PART V: POWER SUMS AND FAULHABER                           *)
(* ========================================================================= *)

(** Power sum: Σ_{k=1}^{N} k^p *)
Definition power_sum (p N : nat) : Q :=
  partial_sum (fun k => Qpow (inject_Z (Z.of_nat (S k))) p) N.

(** Power sum examples *)
Lemma power_sum_1_example : power_sum 1 3 == 10.
Proof. vm_compute. reflexivity. Qed.

(** Faulhaber for p=1: Σ_{k=1}^{N+1} k = (N+1)(N+2)/2
    Note: power_sum 1 N = 1 + 2 + ... + (N+1) *)
Theorem faulhaber_1 : forall N : nat,
  2 * power_sum 1 N ==
  inject_Z (Z.of_nat (S N)) * inject_Z (Z.of_nat (S (S N))).
Proof.
  induction N as [| N' IH].
  - vm_compute. reflexivity.
  - unfold power_sum.
    change (partial_sum (fun k => Qpow (inject_Z (Z.of_nat (S k))) 1) (S N'))
      with (partial_sum (fun k => Qpow (inject_Z (Z.of_nat (S k))) 1) N' +
            Qpow (inject_Z (Z.of_nat (S (S N')))) 1).
    fold (power_sum 1 N').
    assert (Hpow : Qpow (inject_Z (Z.of_nat (S (S N')))) 1 ==
                   inject_Z (Z.of_nat (S (S N')))).
    { simpl. ring. }
    setoid_rewrite Hpow.
    set (ps := power_sum 1 N') in *.
    set (x := inject_Z (Z.of_nat (S (S N')))) in *.
    (* IH:  2 * ps == inject_Z(S N') * x *)
    (* Goal: 2 * (ps + x) == x * inject_Z(S(S(S N'))) *)
    transitivity (2 * ps + 2 * x).
    + ring.
    + setoid_rewrite IH.
      (* inject_Z(S N') * x + 2 * x == x * inject_Z(S(S(S N'))) *)
      set (a := inject_Z (Z.of_nat (S N'))).
      assert (Ha : a + 2 == inject_Z (Z.of_nat (S (S (S N'))))).
      { subst a. change 2 with (inject_Z 2). rewrite <- inject_Z_plus.
        unfold Qeq. simpl. lia. }
      setoid_rewrite <- Ha. ring.
Qed.

(** Power sums grow: concrete examples *)
Lemma power_sum_grows_1 : power_sum 1 10 > 50.
Proof. unfold Qgt, Qlt. vm_compute. reflexivity. Qed.

Lemma power_sum_grows_3 : power_sum 3 5 > 400.
Proof. unfold Qgt, Qlt. vm_compute. reflexivity. Qed.

(** Each term (k+1)^p >= 1 for p >= 1 and all k *)
Lemma qpow_ge_1 : forall (q : Q) (p : nat),
  1 <= q -> (1 <= p)%nat -> 1 <= Qpow q p.
Proof.
  intros q p Hq Hp.
  induction p as [|p' IHp].
  - lia.
  - simpl. destruct p' as [|p''].
    + simpl. lra.
    + assert (IH : 1 <= Qpow q (S p'')) by (apply IHp; lia).
      assert (H0 : 0 <= Qpow q (S p'')).
      { apply Qle_trans with 1; [lra | exact IH]. }
      apply Qle_trans with (1 * Qpow q (S p'')).
      * lra.
      * apply Qmult_le_compat_r; lra.
Qed.

(** Power sums diverge: for p >= 1, Σk^p can exceed any bound.
    Each of the N+1 terms satisfies (k+1)^p >= 1,
    so power_sum p N >= N+1 → ∞ as N → ∞. *)
Theorem power_sum_diverges : forall p : nat,
  (1 <= p)%nat ->
  forall B : Q, exists N : nat, power_sum p N > B.
Proof.
  intros p Hp B.
  destruct (nat_archimedean B 1 ltac:(lra)) as [K HK].
  exists K. unfold power_sum.
  (* Show partial_sum >= K+1 by showing each term >= 1 *)
  assert (Hlower : forall n, inject_Z (Z.of_nat (S n)) <=
    partial_sum (fun k => Qpow (inject_Z (Z.of_nat (S k))) p) n).
  { induction n as [| n' IHn].
    - simpl. apply qpow_ge_1; [unfold Qle; simpl; lia | exact Hp].
    - change (partial_sum (fun k => Qpow (inject_Z (Z.of_nat (S k))) p) (S n'))
        with (partial_sum (fun k => Qpow (inject_Z (Z.of_nat (S k))) p) n' +
              Qpow (inject_Z (Z.of_nat (S (S n')))) p).
      assert (H1 : 1 <= Qpow (inject_Z (Z.of_nat (S (S n')))) p).
      { apply qpow_ge_1; [unfold Qle; simpl; lia | exact Hp]. }
      apply Qle_trans with (inject_Z (Z.of_nat (S n')) + 1).
      + unfold Qle. simpl. lia.
      + apply Qplus_le_compat; [exact (IHn) | exact H1]. }
  specialize (Hlower K).
  assert (Hsk : inject_Z (Z.of_nat K) < inject_Z (Z.of_nat (S K))).
  { unfold Qlt. simpl. lia. }
  lra.
Qed.

(* ========================================================================= *)
(*                PART VI: ZETA AT NEGATIVE INTEGERS                          *)
(* ========================================================================= *)

(**
  ζ(-k) = -B_{k+1}/(k+1) for k ≥ 0.
  These are EXACT RATIONAL NUMBERS.
*)

Definition zeta_neg (k : nat) : Q :=
  -(bernoulli (S k)) / inject_Z (Z.of_nat (S k)).

(** ζ(0) = -B₁/1 = -(-1/2)/1 = 1/2 *)
Theorem zeta_neg_0 : zeta_neg 0 == (1#2).
Proof. unfold zeta_neg. vm_compute. reflexivity. Qed.

(** ★ ζ(-1) = -B₂/2 = -(1/6)/2 = -1/12 ★
    THE Casimir 1D number *)
Theorem zeta_neg_1 : zeta_neg 1 == -(1#12).
Proof. unfold zeta_neg. vm_compute. reflexivity. Qed.

(** ζ(-2) = -B₃/3 = 0/3 = 0 (trivial zero) *)
Theorem zeta_neg_2 : zeta_neg 2 == 0.
Proof. unfold zeta_neg. vm_compute. reflexivity. Qed.

(** ★ ζ(-3) = -B₄/4 = -(-1/30)/4 = 1/120 ★
    THE Casimir 3D number *)
Theorem zeta_neg_3 : zeta_neg 3 == (1#120).
Proof. unfold zeta_neg. vm_compute. reflexivity. Qed.

(** Summary:

  STATUS: Qed count below, 0 Admitted

  Part I   — Q-valued helpers:
    qfact_pos, qbinom_0_r, qbinom_n_n, qbinom_gt

  Part II  — Bernoulli definition:
    bernoulli_list_length

  Part III — Concrete values:
    B0_value, B1_value, B2_value, B3_value, B4_value,
    B5_value, B6_value, B7_value, B8_value

  Part IV  — Properties:
    B_odd_3, B_odd_5, B_odd_7, B2_pos, B4_neg, B6_pos,
    bernoulli_recursion_1..4

  Part V   — Power sums:
    power_sum_1_example, faulhaber_1, power_sum_diverges

  Part VI  — Zeta at negative integers:
    zeta_neg_0, zeta_neg_1, zeta_neg_2, zeta_neg_3
*)
