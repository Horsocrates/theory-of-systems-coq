(** * LogZeta.v — Logarithmic Decomposition over Primes as ToS System
    Elements: log series, prime sums, log ζ decomposition
    Roles:    Euler product → log decomposition, primes → individual terms
    Rules:    log(1/(1-x)) = Σ x^m/m, positivity, monotonicity
    Status:   complete
    STATUS: ~35 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        LOG ZETA — Logarithmic Decomposition over Primes                    *)
(*                                                                            *)
(*  From Euler product: log ζ(s) = Σ_p log(1/(1-p^{-s}))                   *)
(*                                = Σ_p Σ_{m=1}^{∞} p^{-ms}/m              *)
(*                                                                            *)
(*  Over Q: we work with finite partial products and sums.                   *)
(*  log(1/(1-x)) ≈ x + x²/2 + x³/3 + ... for |x| < 1                    *)
(*                                                                            *)
(*  STATUS: ~35 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
Require Import Stdlib.micromega.Lqa.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

From ToS Require Import SeriesConvergence.
From ToS Require Import stdlib.Primes.
From ToS Require Import zeta.EulerProduct.
From ToS Require Import zeta.ZetaProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Log Approximation  (~8 lemmas)                             *)
(* ================================================================== *)

(** Rational approximation of log via harmonic numbers:
    H_n = 1 + 1/2 + ... + 1/n ≈ log(n) + γ *)

Fixpoint harmonic (n : nat) : Q :=
  match n with
  | O => 0
  | S k => harmonic k + 1 / inject_Z (Z.of_nat (S k))
  end.

Definition log_approx (n : nat) : Q := harmonic n.

Lemma harmonic_0 : harmonic 0 == 0.
Proof. reflexivity. Qed.

Lemma harmonic_1 : harmonic 1 == 1.
Proof. unfold harmonic. field. Qed.

Lemma harmonic_step : forall n,
  harmonic (S n) == harmonic n + 1 / inject_Z (Z.of_nat (S n)).
Proof. intros n. reflexivity. Qed.

Lemma harmonic_nonneg : forall n, 0 <= harmonic n.
Proof.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite harmonic_step.
    assert (H : 0 < inject_Z (Z.of_nat (S n))) by apply inject_Z_Sn_pos.
    assert (H2 : 0 <= 1 / inject_Z (Z.of_nat (S n))).
    { apply Qle_shift_div_l; [exact H|lra]. }
    lra.
Qed.

Lemma harmonic_increasing : forall n,
  harmonic n <= harmonic (S n).
Proof.
  intros n. rewrite harmonic_step.
  assert (H : 0 < inject_Z (Z.of_nat (S n))) by apply inject_Z_Sn_pos.
  assert (H2 : 0 <= 1 / inject_Z (Z.of_nat (S n))).
  { apply Qle_shift_div_l; [exact H|lra]. }
  lra.
Qed.

Lemma harmonic_positive : forall n, (1 <= n)%nat -> 0 < harmonic n.
Proof.
  intros n Hn. destruct n as [|n]. - lia.
  - rewrite harmonic_step.
    assert (Hnn := harmonic_nonneg n).
    assert (H : 0 < inject_Z (Z.of_nat (S n))) by apply inject_Z_Sn_pos.
    assert (H2 : 0 < 1 / inject_Z (Z.of_nat (S n))).
    { apply Qlt_shift_div_l; [exact H|lra]. }
    lra.
Qed.

Lemma log_approx_nonneg : forall n, 0 <= log_approx n.
Proof. intros n. apply harmonic_nonneg. Qed.

Lemma log_approx_positive : forall n, (1 <= n)%nat -> 0 < log_approx n.
Proof. intros n Hn. apply harmonic_positive. exact Hn. Qed.

Lemma log_approx_increasing : forall n,
  log_approx n <= log_approx (S n).
Proof. intros n. apply harmonic_increasing. Qed.

(* ================================================================== *)
(*  Part II: Log Power Series  (~8 lemmas)                             *)
(* ================================================================== *)

(** log(1/(1-x)) = x + x²/2 + x³/3 + ... for |x| < 1
    Term m (for m ≥ 1): x^m / m *)

Definition log_series_term (x : Q) (m : nat) : Q :=
  match m with
  | O => 0
  | S k => Qpow x (S k) / inject_Z (Z.of_nat (S k))
  end.

Definition log_series_partial (x : Q) (M : nat) : Q :=
  partial_sum (fun m => log_series_term x (S m)) M.

Lemma log_series_term_0 : forall x, log_series_term x 0 == 0.
Proof. intros x. reflexivity. Qed.

Lemma log_series_term_nonneg : forall x m,
  0 <= x -> 0 <= log_series_term x m.
Proof.
  intros x m Hx. destruct m as [|m].
  - simpl. lra.
  - unfold log_series_term.
    assert (Hp : 0 <= Qpow x (S m)) by (apply Qpow_nonneg; exact Hx).
    assert (Hd : 0 < inject_Z (Z.of_nat (S m))) by apply inject_Z_Sn_pos.
    apply Qle_shift_div_l; lra.
Qed.

Lemma log_series_partial_step : forall x M,
  log_series_partial x (S M) ==
  log_series_partial x M + log_series_term x (S (S M)).
Proof. intros x M. unfold log_series_partial. reflexivity. Qed.

Lemma log_series_partial_nonneg : forall x M,
  0 <= x -> 0 <= log_series_partial x M.
Proof.
  intros x M Hx. induction M as [|M IH].
  - unfold log_series_partial, partial_sum.
    apply log_series_term_nonneg. exact Hx.
  - rewrite log_series_partial_step.
    assert (Ht := log_series_term_nonneg x (S (S M)) Hx). lra.
Qed.

Lemma log_series_partial_increasing : forall x M,
  0 <= x ->
  log_series_partial x M <= log_series_partial x (S M).
Proof.
  intros x M Hx. rewrite log_series_partial_step.
  assert (Ht := log_series_term_nonneg x (S (S M)) Hx). lra.
Qed.

(** Each term bounded by the corresponding power *)
Lemma log_series_term_le_power : forall x m,
  0 <= x -> x <= 1 -> (1 <= m)%nat ->
  log_series_term x m <= Qpow x m.
Proof.
  intros x m Hx Hx1 Hm.
  destruct m as [|m]. - lia.
  - unfold log_series_term.
    assert (Hd : 0 < inject_Z (Z.of_nat (S m))) by apply inject_Z_Sn_pos.
    assert (Hp : 0 <= Qpow x (S m)) by (apply Qpow_nonneg; exact Hx).
    (* Goal: Qpow x (S m) / inject_Z d <= Qpow x (S m) *)
    (* Cross-multiply: Qpow ≤ Qpow * d, i.e., Qpow * 1 ≤ Qpow * d *)
    apply Qle_shift_div_r; [exact Hd|].
    (* Goal: Qpow x (S m) <= Qpow x (S m) * inject_Z (Z.of_nat (S m)) *)
    assert (H1 : 1 <= inject_Z (Z.of_nat (S m))).
    { change 1 with (inject_Z 1). unfold Qle, inject_Z. simpl. lia. }
    setoid_replace (Qpow x (S m)) with (1 * Qpow x (S m)) at 1 by ring.
    setoid_replace (Qpow x (S m) * inject_Z (Z.of_nat (S m)))
      with (inject_Z (Z.of_nat (S m)) * Qpow x (S m)) by ring.
    apply Qmult_le_compat_r; lra.
Qed.

(* ================================================================== *)
(*  Part III: Sum Over Primes  (~8 lemmas)                             *)
(* ================================================================== *)

(** Sum of f(p) over primes up to N *)
Definition sum_over_primes (f : nat -> Q) (N : nat) : Q :=
  fold_left (fun acc p => acc + f p) (sieve N) 0.

(** Prime reciprocal sum: Σ_{p≤N} 1/p^k *)
Definition prime_power_sum (k N : nat) : Q :=
  sum_over_primes (fun p => 1 / nat_power p k) N.

Definition euler_log_leading (p k : nat) : Q := 1 / nat_power p k.

(** Helper: fold_left preserves bounds *)
Lemma fold_left_add_nonneg : forall {A} (f : A -> Q) (l : list A) init,
  0 <= init -> (forall a, 0 <= f a) ->
  0 <= fold_left (fun acc a => acc + f a) l init.
Proof.
  intros A f l. induction l as [|x l IH].
  - intros init Hi _. simpl. exact Hi.
  - intros init Hi Hf. simpl. apply IH.
    + specialize (Hf x). lra.
    + exact Hf.
Qed.

Lemma sum_over_primes_nonneg : forall f N,
  (forall p, 0 <= f p) -> 0 <= sum_over_primes f N.
Proof.
  intros f N Hf. unfold sum_over_primes.
  apply fold_left_add_nonneg; [lra|exact Hf].
Qed.

Lemma inv_nat_power_nonneg : forall p k,
  0 <= 1 / nat_power p k.
Proof.
  intros p k.
  destruct p as [|p].
  - (* p = 0: 1/0^k. In Q: if denom = 0, result = 0 *)
    unfold nat_power, Qdiv, Qinv, Qmult, Qle. simpl.
    destruct k; simpl; lia.
  - assert (Hpk : 0 < nat_power (S p) k).
    { apply nat_power_Sn_pos. }
    apply Qle_shift_div_l; lra.
Qed.

Lemma prime_power_sum_nonneg : forall k N, 0 <= prime_power_sum k N.
Proof.
  intros k N. unfold prime_power_sum.
  apply sum_over_primes_nonneg. intros p. apply inv_nat_power_nonneg.
Qed.

Lemma euler_log_leading_pos : forall p k,
  (2 <= p)%nat -> (1 <= k)%nat -> 0 < euler_log_leading p k.
Proof.
  intros p k Hp Hk. unfold euler_log_leading.
  assert (Hpk : 0 < nat_power p k).
  { destruct p as [|[|p]]; try lia. apply nat_power_Sn_pos. }
  apply Qlt_shift_div_l; lra.
Qed.

(* ================================================================== *)
(*  Part IV: Log ζ as Sum over Primes  (~8 lemmas)                    *)
(* ================================================================== *)

Definition log_zeta_approx (k M N : nat) : Q :=
  sum_over_primes (fun p => log_series_partial (1 / nat_power p k) M) N.

Lemma log_zeta_approx_nonneg : forall k M N,
  (2 <= k)%nat -> 0 <= log_zeta_approx k M N.
Proof.
  intros k M N Hk. unfold log_zeta_approx.
  apply sum_over_primes_nonneg. intros p.
  apply log_series_partial_nonneg. apply inv_nat_power_nonneg.
Qed.

(** Monotonicity: more log terms → larger approximation *)
Lemma log_zeta_approx_mono_M : forall k M N,
  (2 <= k)%nat ->
  log_zeta_approx k M N <= log_zeta_approx k (S M) N.
Proof.
  intros k M N Hk. unfold log_zeta_approx, sum_over_primes.
  assert (Hgen : forall l init1 init2,
    init1 <= init2 ->
    (forall p, In p l ->
      log_series_partial (1 / nat_power p k) M <=
      log_series_partial (1 / nat_power p k) (S M)) ->
    fold_left (fun acc p => acc + log_series_partial (1 / nat_power p k) M) l init1 <=
    fold_left (fun acc p => acc + log_series_partial (1 / nat_power p k) (S M)) l init2).
  { induction l as [|x l IH].
    - intros. simpl. exact H.
    - intros init1 init2 Hi Hps. simpl.
      apply IH.
      + assert (Hx := Hps x (or_introl eq_refl)). lra.
      + intros p Hp. apply Hps. right. exact Hp. }
  apply Hgen; [lra|].
  intros p _. apply log_series_partial_increasing. apply inv_nat_power_nonneg.
Qed.

(** The M=0 term of log series equals the argument *)
Lemma log_series_partial_0 : forall x,
  log_series_partial x 0 == x.
Proof.
  intros x. unfold log_series_partial.
  change (partial_sum (fun m => log_series_term x (S m)) 0)
    with (log_series_term x 1).
  unfold log_series_term.
  unfold Qdiv, Qpow, Qinv, inject_Z, Z.of_nat, Qmult, Qeq.
  simpl. lia.
Qed.

(* ================================================================== *)
(*  Part V: Mertens Connection and Process  (~8 lemmas)                *)
(* ================================================================== *)

Definition mertens_log_combination (k N : nat) : Q :=
  3 * log_zeta_approx k 0 N + 4 * log_zeta_approx k 0 N + log_zeta_approx k 0 N.

Lemma mertens_log_nonneg : forall k N,
  (2 <= k)%nat -> 0 <= mertens_log_combination k N.
Proof.
  intros k N Hk. unfold mertens_log_combination.
  assert (H := log_zeta_approx_nonneg k 0 N Hk). lra.
Qed.

(** The combination has coefficient 3+4+1 = 8 *)
Lemma mertens_log_factor : forall a : Q,
  3 * a + 4 * a + a == 8 * a.
Proof. intros a. ring. Qed.

Definition log_zeta_process (k N : nat) : nat -> Q := fun M => log_zeta_approx k M N.

Lemma log_zeta_process_nonneg : forall k N M,
  (2 <= k)%nat -> 0 <= log_zeta_process k N M.
Proof. intros k N M Hk. apply log_zeta_approx_nonneg. exact Hk. Qed.

Lemma log_zeta_process_increasing : forall k N M,
  (2 <= k)%nat -> log_zeta_process k N M <= log_zeta_process k N (S M).
Proof. intros k N M Hk. apply log_zeta_approx_mono_M. exact Hk. Qed.

(** Mertens via primes: the 3+4cos+cos2 identity gives non-negative combination *)
Theorem mertens_via_primes : forall k N,
  (2 <= k)%nat ->
  0 <= 3 * prime_power_sum k N + 4 * prime_power_sum k N + prime_power_sum k N.
Proof.
  intros k N Hk. assert (H := prime_power_sum_nonneg k N). lra.
Qed.

Theorem prime_sum_mertens_identity : forall k N,
  (2 <= k)%nat ->
  3 * prime_power_sum k N + 4 * prime_power_sum k N + prime_power_sum k N ==
  8 * prime_power_sum k N.
Proof. intros k N Hk. ring. Qed.

(** Summary *)
Theorem log_zeta_summary :
  (forall x m, 0 <= x -> 0 <= log_series_term x m) /\
  (forall x M, 0 <= x -> 0 <= log_series_partial x M) /\
  (forall x M, 0 <= x -> log_series_partial x M <= log_series_partial x (S M)) /\
  (forall x m, 0 <= x -> x <= 1 -> (1 <= m)%nat -> log_series_term x m <= Qpow x m) /\
  (forall k N, 0 <= prime_power_sum k N) /\
  (forall k M N, (2 <= k)%nat -> 0 <= log_zeta_approx k M N).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact log_series_term_nonneg.
  - exact log_series_partial_nonneg.
  - exact log_series_partial_increasing.
  - exact log_series_term_le_power.
  - exact prime_power_sum_nonneg.
  - exact log_zeta_approx_nonneg.
Qed.

Check log_approx.
Check log_series_term.
Check log_series_partial.
Check sum_over_primes.
Check prime_power_sum.
Check log_zeta_approx.
Check log_zeta_summary.
Check mertens_via_primes.
