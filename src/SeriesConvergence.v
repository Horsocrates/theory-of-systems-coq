(* ========================================================================= *)
(*            SERIES CONVERGENCE                                             *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove convergence of series via MCT:                           *)
(*    - Q powers (Qpow) and Bernoulli's inequality                         *)
(*    - Geometric series convergence (division-free)                        *)
(*    - Comparison test and absolute convergence                            *)
(*    - CauchySeq constructions from convergent series                      *)
(*                                                                          *)
(*  AXIOMS: classic (inherited from MonotoneConvergence)                    *)
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

From ToS Require Import CauchyReal.
From ToS Require Import Completeness.
From ToS Require Import MonotoneConvergence.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: Q POWERS                                                       *)
(* ========================================================================= *)

Fixpoint Qpow (r : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1
  | S k => r * Qpow r k
  end.

Lemma Qpow_nonneg : forall (r : Q) (n : nat),
  0 <= r -> 0 <= Qpow r n.
Proof.
  intros r n Hr. induction n; simpl.
  - lra.
  - apply Qmult_le_0_compat; assumption.
Qed.

Lemma Qpow_monotone_dec : forall (r : Q) (n : nat),
  0 <= r -> r <= 1 -> Qpow r (S n) <= Qpow r n.
Proof.
  intros r n Hr Hr1. simpl.
  assert (Hpow : 0 <= Qpow r n) by (apply Qpow_nonneg; assumption).
  (* r * Qpow r n <= 1 * Qpow r n = Qpow r n *)
  assert (H : r * Qpow r n <= 1 * Qpow r n).
  { apply Qmult_le_compat_r; assumption. }
  lra.
Qed.

Lemma Qpow_bound_1 : forall (r : Q) (n : nat),
  0 <= r -> r <= 1 -> Qpow r n <= 1.
Proof.
  intros r n Hr Hr1. induction n; simpl.
  - lra.
  - assert (Hpow : 0 <= Qpow r n) by (apply Qpow_nonneg; assumption).
    assert (H : r * Qpow r n <= 1 * Qpow r n).
    { apply Qmult_le_compat_r; assumption. }
    lra.
Qed.

(** Qpow respects Qeq *)
Lemma Qpow_wd : forall (r s : Q) (n : nat),
  r == s -> Qpow r n == Qpow s n.
Proof.
  intros r s n Hrs. induction n; cbn [Qpow].
  - reflexivity.
  - apply Qmult_comp; [exact Hrs | exact IHn].
Qed.

(** Qpow 1 = 1 *)
Lemma Qpow_1 : forall n, Qpow 1 n == 1.
Proof.
  induction n; cbn [Qpow].
  - reflexivity.
  - transitivity (1 * 1).
    + apply Qmult_comp; [reflexivity | exact IHn].
    + ring.
Qed.

(** Qpow distributes over multiplication *)
Lemma Qpow_mul_distr : forall (r s : Q) (n : nat),
  Qpow (r * s) n == Qpow r n * Qpow s n.
Proof.
  intros r s n. induction n; cbn [Qpow].
  - ring.
  - transitivity ((r * s) * (Qpow r n * Qpow s n)).
    + apply Qmult_comp; [reflexivity | exact IHn].
    + ring.
Qed.

(** r^n * (1/r)^n = 1 *)
Lemma Qpow_inv_cancel : forall (r : Q) (n : nat),
  ~ r == 0 -> Qpow r n * Qpow (/ r) n == 1.
Proof.
  intros r n Hr0.
  transitivity (Qpow (r * / r) n).
  - apply Qeq_sym. apply Qpow_mul_distr.
  - transitivity (Qpow 1 n).
    + apply Qpow_wd. field. exact Hr0.
    + apply Qpow_1.
Qed.

Lemma Qpow_pos : forall (r : Q) (n : nat),
  0 < r -> 0 < Qpow r n.
Proof.
  intros r n Hr. induction n; simpl.
  - lra.
  - apply Qmult_lt_0_compat; assumption.
Qed.

(* ========================================================================= *)
(* SECTION 2: BERNOULLI'S INEQUALITY + POWER VANISHING                      *)
(* ========================================================================= *)

(** Bernoulli's inequality: (1 + x)^n >= 1 + n*x for x >= 0 *)
Lemma bernoulli_ineq : forall (x : Q) (n : nat),
  0 <= x -> 1 + inject_Z (Z.of_nat n) * x <= Qpow (1 + x) n.
Proof.
  intros x n Hx. induction n.
  - simpl. setoid_replace (inject_Z (Z.of_nat 0) * x) with 0
      by (simpl Z.of_nat; unfold inject_Z; ring).
    lra.
  - simpl Qpow.
    (* (1+x)^(S n) = (1+x) * (1+x)^n >= (1+x) * (1 + n*x) *)
    assert (H1x : 0 <= 1 + x) by lra.
    assert (H1nx : 1 + inject_Z (Z.of_nat n) * x <= Qpow (1 + x) n) by exact IHn.
    assert (Hpow_nn : 0 <= Qpow (1 + x) n).
    { apply Qpow_nonneg. lra. }
    (* (1+x)(1+nx) = 1 + nx + x + nx^2 = 1 + (n+1)x + nx^2 >= 1 + (n+1)x *)
    assert (Hexpand : (1 + x) * (1 + inject_Z (Z.of_nat n) * x) ==
                      1 + inject_Z (Z.of_nat (S n)) * x +
                      inject_Z (Z.of_nat n) * x * x).
    { rewrite Nat2Z.inj_succ.
      setoid_replace (inject_Z (Z.succ (Z.of_nat n)))
        with (inject_Z (Z.of_nat n) + 1)
        by (unfold inject_Z, Qeq, Qplus; simpl; lia).
      ring. }
    assert (Hnx2 : 0 <= inject_Z (Z.of_nat n) * x * x).
    { apply Qmult_le_0_compat.
      - apply Qmult_le_0_compat; [|exact Hx].
        assert (Hnn : (0 <= Z.of_nat n)%Z) by lia.
        unfold Qle, inject_Z. simpl. lia.
      - exact Hx. }
    (* (1+x)^{S n} = (1+x) * (1+x)^n >= (1+x)(1+nx) = 1+(n+1)x + nx^2 >= 1+(n+1)x *)
    assert (Hmul : (1 + x) * (1 + inject_Z (Z.of_nat n) * x) <=
                   (1 + x) * Qpow (1 + x) n).
    { assert (Hdiff : 0 <= (1 + x) * (Qpow (1 + x) n - (1 + inject_Z (Z.of_nat n) * x))).
      { apply Qmult_le_0_compat; lra. }
      lra. }
    lra.
Qed.

(** Q powers vanish: r^n -> 0 for 0 < r < 1 *)
Lemma Qpow_vanish : forall (r : Q) (eps : Q),
  0 < r -> r < 1 -> 0 < eps ->
  exists N : nat, Qpow r N < eps.
Proof.
  intros r eps Hr Hr1 Heps.
  (* Strategy: (1/r)^n >= 1 + n*(1/r - 1) by Bernoulli *)
  (* So r^n <= 1/(1 + n*(1/r - 1)) = r/(r + n*(1-r)) *)
  (* For n large enough, r/(r + n*(1-r)) < eps *)
  (* i.e., r < eps * (r + n*(1-r)) *)
  (* i.e., r - eps*r < eps * n * (1-r) *)
  (* i.e., r*(1-eps) < eps * n * (1-r) *)
  (* For eps >= 1: r < 1 <= eps, so N = 0 works since r^0 = 1... no, 1 < eps only if eps > 1 *)
  (* Actually just use: r^n = r * r^{n-1} and since r < 1, r^n is eventually < eps *)
  (* Better: use Bernoulli directly *)
  set (delta := (1 - r) / r). (* delta > 0 since 0 < r < 1 *)
  assert (Hdelta : 0 < delta).
  { unfold delta. apply Qlt_shift_div_l; lra. }
  assert (Hr_inv : 1 + delta == / r).
  { unfold delta. field. lra. }
  (* Get N from nat_archimedean: N * delta > 1/eps - 1, i.e., 1 + N*delta > 1/eps *)
  destruct (nat_archimedean (/ eps) delta Hdelta) as [N HN].
  exists N.
  (* Need: r^N < eps *)
  (* (1/r)^N = (1+delta)^N >= 1 + N*delta > /eps *)
  (* So r^N < eps *)
  assert (Hbern : 1 + inject_Z (Z.of_nat N) * delta <= Qpow (1 + delta) N)
    by (apply bernoulli_ineq; lra).
  assert (Hpow_inv : Qpow (1 + delta) N == Qpow (/ r) N)
    by (apply Qpow_wd; exact Hr_inv).
  (* Qpow (/r) N > /eps, so Qpow r N < eps *)
  assert (Hpow_pos : 0 < Qpow r N) by (apply Qpow_pos; exact Hr).
  assert (Hinv_r_pos : 0 < / r) by (apply Qinv_lt_0_compat; exact Hr).
  assert (Hpow_inv_pos : 0 < Qpow (/ r) N) by (apply Qpow_pos; exact Hinv_r_pos).
  (* Key: Qpow r N * Qpow (/r) N == 1 *)
  assert (Hprod1 : Qpow r N * Qpow (/ r) N == 1)
    by (apply Qpow_inv_cancel; lra).
  (* Qpow (/r) N > /eps (from Bernoulli + archimedean) *)
  assert (Hinv_bound : Qpow (/ r) N > / eps).
  { assert (H : / eps < 1 + inject_Z (Z.of_nat N) * delta) by lra.
    assert (H2 : 1 + inject_Z (Z.of_nat N) * delta <= Qpow (/ r) N).
    { assert (Hb := Hbern). assert (Hp := Hpow_inv).
      lra. }
    lra. }
  (* eps * (1/r)^N > 1 = r^N * (1/r)^N, so eps > r^N *)
  assert (Heps_x_gt_1 : eps * Qpow (/ r) N > 1).
  { (* eps > 0 and Qpow(/r)N > /eps, so eps * (Qpow(/r)N - /eps) > 0 *)
    assert (Hdiff : 0 < Qpow (/ r) N - / eps) by lra.
    assert (Hprod : 0 < eps * (Qpow (/ r) N - / eps))
      by (apply Qmult_lt_0_compat; [exact Heps | exact Hdiff]).
    (* eps * Qpow(/r)N - eps * /eps > 0, and eps * /eps == 1 *)
    assert (Heps_inv : eps * / eps == 1) by (field; lra).
    lra. }
  (* Now: eps * Qpow(/r)N > 1 == Qpow r N * Qpow(/r)N *)
  (* So (eps - Qpow r N) * Qpow(/r)N > 0, and since Qpow(/r)N > 0, eps > Qpow r N *)
  assert (Hdiff2 : 0 < (eps - Qpow r N) * Qpow (/ r) N) by lra.
  (* (eps - r^N) > 0 since product with positive is positive *)
  destruct (Qlt_le_dec (Qpow r N) eps) as [Hdone | Habs].
  + exact Hdone.
  + (* r^N >= eps, contradiction with Hdiff2 *)
    assert (Hle : (eps - Qpow r N) <= 0) by lra.
    assert (Hle2 : (eps - Qpow r N) * Qpow (/ r) N <= 0).
    { assert (H : (eps - Qpow r N) * Qpow (/ r) N <= 0 * Qpow (/ r) N).
      { apply Qmult_le_compat_r; lra. }
      lra. }
    lra.
Qed.

(** Decreasing bounded: r^n is Cauchy for 0 <= r < 1 *)
Lemma Qpow_cauchy : forall r,
  0 <= r -> r < 1 -> is_cauchy (fun n => Qpow r n).
Proof.
  intros r Hr Hr1.
  destruct (Qlt_le_dec 0 r) as [Hrpos | Hrzero].
  - (* 0 < r < 1: decreasing + bounded below by 0 *)
    apply q_dec_bounded_cauchy with 0.
    + intros n. apply Qpow_monotone_dec; lra.
    + intros n. apply Qpow_nonneg; lra.
  - (* r = 0: constant 0 after index 0 *)
    assert (Hr0 : r == 0) by lra.
    intros eps Heps. exists 1%nat. intros m n Hm Hn.
    assert (Hm1 : (1 <= m)%nat) by lia.
    assert (Hn1 : (1 <= n)%nat) by lia.
    assert (Hpm : Qpow r m == 0).
    { destruct m; [lia|]. cbn [Qpow].
      transitivity (0 * Qpow r m).
      - apply Qmult_comp; [exact Hr0 | reflexivity].
      - ring. }
    assert (Hpn : Qpow r n == 0).
    { destruct n; [lia|]. cbn [Qpow].
      transitivity (0 * Qpow r n).
      - apply Qmult_comp; [exact Hr0 | reflexivity].
      - ring. }
    setoid_replace (Qpow r m - Qpow r n) with 0 by lra.
    rewrite Qabs_pos; lra.
Qed.

(** r^n eventually < eps for 0 <= r < 1, monotonically *)
Lemma Qpow_limit_zero : forall r,
  0 <= r -> r < 1 ->
  forall eps, 0 < eps ->
    exists N, forall n, (N <= n)%nat -> Qpow r n < eps.
Proof.
  intros r Hr Hr1 eps Heps.
  destruct (Qlt_le_dec 0 r) as [Hrpos | Hrzero].
  - (* 0 < r: use Qpow_vanish to get one N, then monotonicity *)
    destruct (Qpow_vanish r eps Hrpos Hr1 Heps) as [N HN].
    exists N. intros n Hn.
    assert (Hle : Qpow r n <= Qpow r N).
    { apply dec_le; [|exact Hn].
      intros k. apply Qpow_monotone_dec; lra. }
    lra.
  - (* r = 0 *)
    assert (Hr0 : r == 0) by lra.
    exists 1%nat. intros n Hn.
    destruct n; [lia|]. cbn [Qpow].
    assert (Hpow0 : r * Qpow r n == 0).
    { transitivity (0 * Qpow r n).
      - apply Qmult_comp; [exact Hr0 | reflexivity].
      - ring. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: PARTIAL SUMS                                                   *)
(* ========================================================================= *)

Fixpoint partial_sum (a : nat -> Q) (n : nat) : Q :=
  match n with
  | 0%nat => a 0%nat
  | S k => partial_sum a k + a (S k)
  end.

Lemma partial_sum_nonneg_inc : forall (a : nat -> Q),
  (forall n, 0 <= a n) ->
  forall n, partial_sum a n <= partial_sum a (S n).
Proof.
  intros a Ha n. simpl. specialize (Ha (S n)). lra.
Qed.

Lemma partial_sum_monotone : forall (a b : nat -> Q),
  (forall n, a n <= b n) ->
  forall n, partial_sum a n <= partial_sum b n.
Proof.
  intros a b Hab n. induction n; simpl.
  - apply Hab.
  - specialize (Hab (S n)). lra.
Qed.

(** Tail of partial sum: difference of partial sums *)
Lemma partial_sum_tail : forall (a : nat -> Q) (m n : nat),
  (m <= n)%nat ->
  partial_sum a n - partial_sum a m ==
  partial_sum (fun k => a (S m + k)%nat) (n - S m).
Proof.
  intros a m n Hmn.
  (* This is tricky to state cleanly. Instead, prove the Cauchy property directly. *)
  Abort.

(** Key property for Cauchy criterion: nonneg partial sums are bounded above *)
Lemma partial_sum_nonneg_bound : forall (a : nat -> Q) (B : Q),
  (forall n, 0 <= a n) ->
  (forall n, partial_sum a n <= B) ->
  is_cauchy (partial_sum a).
Proof.
  intros a B Ha Hbound.
  apply q_inc_bounded_cauchy with B.
  - intros n. apply partial_sum_nonneg_inc; exact Ha.
  - exact Hbound.
Qed.

(* ========================================================================= *)
(* SECTION 4: GEOMETRIC SERIES                                               *)
(* ========================================================================= *)

(** Division helper: a * c <= b -> a <= b * /c when c > 0 *)
Lemma Qle_div_r : forall a b c : Q,
  0 < c -> a * c <= b -> a <= b * / c.
Proof.
  intros a b c Hc Hle.
  assert (Hcinv : 0 < / c) by (apply Qinv_lt_0_compat; exact Hc).
  assert (H : a * c * / c <= b * / c).
  { apply Qmult_le_compat_r; [exact Hle | lra]. }
  assert (Heq : a * c * / c == a) by (field; lra).
  lra.
Qed.

(** Key identity: (1-r) * S_n = 1 - r^{n+1} (division-free) *)
Lemma geometric_sum_identity : forall (r : Q) (n : nat),
  (1 - r) * partial_sum (fun k => Qpow r k) n == 1 - Qpow r (S n).
Proof.
  intros r n. induction n.
  - simpl. ring.
  - simpl partial_sum.
    (* (1-r) * (S_n + r^{n+1}) = (1-r)*S_n + (1-r)*r^{n+1} *)
    (* = (1 - r^{n+1}) + r^{n+1} - r^{n+2} = 1 - r^{n+2} *)
    setoid_replace ((1 - r) * (partial_sum (fun k => Qpow r k) n + Qpow r (S n)))
      with ((1 - r) * partial_sum (fun k => Qpow r k) n + (1 - r) * Qpow r (S n))
      by ring.
    rewrite IHn. simpl Qpow. ring.
Qed.

(** Geometric partial sums are bounded: S_n <= 1/(1-r) *)
Lemma geometric_partial_sum_bound : forall (r : Q) (n : nat),
  0 <= r -> r < 1 ->
  partial_sum (fun k => Qpow r k) n <= / (1 - r).
Proof.
  intros r n Hr Hr1.
  assert (H1r : 0 < 1 - r) by lra.
  assert (Hid : (1 - r) * partial_sum (fun k => Qpow r k) n == 1 - Qpow r (S n))
    by (apply geometric_sum_identity).
  assert (Hpow_nn : 0 <= Qpow r (S n))
    by (apply Qpow_nonneg; exact Hr).
  (* S_n * (1-r) <= 1 *)
  assert (Hle1 : partial_sum (fun k => Qpow r k) n * (1 - r) <= 1) by lra.
  assert (Hinv_pos : 0 < / (1 - r)) by (apply Qinv_lt_0_compat; exact H1r).
  assert (H : partial_sum (fun k => Qpow r k) n * (1 - r) * / (1 - r) <= 1 * / (1 - r)).
  { apply Qmult_le_compat_r; [exact Hle1 | lra]. }
  assert (Heq : partial_sum (fun k => Qpow r k) n * (1 - r) * / (1 - r) ==
                partial_sum (fun k => Qpow r k) n)
    by (field; lra).
  assert (Heq2 : 1 * / (1 - r) == / (1 - r)) by ring.
  lra.
Qed.

(** Geometric series is Cauchy: partial sums of r^k converge for 0 <= r < 1 *)
Theorem geometric_series_cauchy : forall (r : Q),
  0 <= r -> r < 1 ->
  is_cauchy (partial_sum (fun k => Qpow r k)).
Proof.
  intros r Hr Hr1.
  apply partial_sum_nonneg_bound with (/ (1 - r)).
  - intros n. apply Qpow_nonneg; exact Hr.
  - intros n. apply geometric_partial_sum_bound; [exact Hr | exact Hr1].
Qed.

(* ========================================================================= *)
(* SECTION 5: COMPARISON TEST                                                *)
(* ========================================================================= *)

(** Comparison test: if 0 <= a(n) <= b(n) and Σb converges, then Σa converges *)
Theorem comparison_test : forall (a b : nat -> Q),
  (forall n, 0 <= a n) ->
  (forall n, 0 <= b n) ->
  (forall n, a n <= b n) ->
  is_cauchy (partial_sum b) ->
  is_cauchy (partial_sum a).
Proof.
  intros a b Ha Hb Hab Hcauchy_b.
  (* partial_sum a is increasing (terms nonneg) and bounded by sup of partial_sum b *)
  (* Get a bound B for partial_sum b *)
  assert (Hcb : exists B, forall n, partial_sum b n <= B).
  { (* From is_cauchy, the sequence is bounded *)
    destruct (Hcauchy_b 1 ltac:(lra)) as [N HN].
    exists (partial_sum b N + 1).
    intros n.
    destruct (Nat.le_gt_cases N n) as [Hle | Hgt].
    - (* n >= N: |S_b(n) - S_b(N)| < 1, so S_b(n) < S_b(N) + 1 *)
      specialize (HN n N Hle (Nat.le_refl N)).
      apply Qabs_Qlt_condition in HN. lra.
    - (* n < N: S_b(n) <= S_b(N) since terms nonneg *)
      assert (Hle : partial_sum b n <= partial_sum b N).
      { apply inc_le; [|lia].
        intros k. apply partial_sum_nonneg_inc. exact Hb. }
      lra. }
  destruct Hcb as [B HB].
  apply partial_sum_nonneg_bound with B.
  - exact Ha.
  - intros n.
    assert (H : partial_sum a n <= partial_sum b n)
      by (apply partial_sum_monotone; exact Hab).
    specialize (HB n). lra.
Qed.

(** Absolute convergence: if Σ|a(n)| converges, then Σa(n) is Cauchy *)
Theorem absolute_convergence : forall (a : nat -> Q) (b : nat -> Q),
  (forall n, Qabs (a n) <= b n) ->
  is_cauchy (partial_sum b) ->
  is_cauchy (partial_sum a).
Proof.
  intros a b Hab Hcauchy_b.
  (* Use Cauchy criterion: for eps > 0, get N from b,
     then |S_a(m) - S_a(n)| <= Σ_{k=n+1}^{m} |a(k)| <= S_b(m) - S_b(n) < eps *)
  intros eps Heps.
  destruct (Hcauchy_b eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  (* |partial_sum a m - partial_sum a n| <= |partial_sum b m - partial_sum b n| *)
  (* This isn't quite right: we need partial_sum |a| not partial_sum a *)
  (* The Cauchy criterion for Σa uses:
     |Σ_{k=n+1}^{m} a(k)| ≤ Σ_{k=n+1}^{m} |a(k)| ≤ Σ_{k=n+1}^{m} b(k) *)
  (* Approach: show |S_a(m) - S_a(n)| ≤ |S_b(m) - S_b(n)| *)
  (* But this requires handling the tail sums carefully *)
  (* Simpler: use is_cauchy of partial_sum b directly *)
  (* For m >= n >= N: |S_b(m) - S_b(n)| < eps *)
  (* And S_b(m) - S_b(n) >= 0 since b(k) >= 0 *)
  (* We need |S_a(m) - S_a(n)| <= S_b(m) - S_b(n) *)
  (* This is the triangle inequality on the tail sum *)
  (* Prove by induction on m - n *)
  destruct (Nat.le_gt_cases n m) as [Hnm | Hnm].
  - (* n <= m *)
    assert (HNn : (N <= n)%nat) by lia.
    assert (HNm : (N <= m)%nat) by lia.
    specialize (HN m n HNm HNn).
    (* Need: |S_a(m) - S_a(n)| <= S_b(m) - S_b(n) *)
    (* Prove: S_b(m) - S_b(n) >= 0 and |S_a(m) - S_a(n)| <= S_b(m) - S_b(n) *)
    assert (Hb_nn : 0 <= partial_sum b m - partial_sum b n).
    { assert (Hle : partial_sum b n <= partial_sum b m).
      { apply inc_le; [|exact Hnm].
        intros k. simpl.
        assert (Hbk : 0 <= b (S k)).
        { eapply Qle_trans; [apply Qabs_nonneg | exact (Hab (S k))]. }
        lra. }
      lra. }
    assert (Hab_tail : Qabs (partial_sum a m - partial_sum a n) <=
                       partial_sum b m - partial_sum b n).
    { (* By induction on the gap m - n *)
      clear HN Heps Hm Hn HNn HNm.
      revert n Hnm Hb_nn.
      induction m; intros n Hnm Hb_nn.
      - (* m = 0 *)
        replace n with 0%nat by lia. cbn [partial_sum].
        setoid_replace (a 0%nat - a 0%nat) with 0 by ring.
        rewrite Qabs_pos; lra.
      - destruct (Nat.eq_dec n (S m)) as [-> | Hne].
        + (* n = S m *)
          cbn [partial_sum].
          setoid_replace (partial_sum a m + a (S m) - (partial_sum a m + a (S m))) with 0 by ring.
          rewrite Qabs_pos; lra.
        + (* n < S m, so n <= m *)
          assert (Hnm' : (n <= m)%nat) by lia.
          change (partial_sum a (S m)) with (partial_sum a m + a (S m)).
          change (partial_sum b (S m)) with (partial_sum b m + b (S m)).
          (* S_a(S m) - S_a(n) = (S_a(m) - S_a(n)) + a(S m) *)
          setoid_replace (partial_sum a m + a (S m) - partial_sum a n)
            with ((partial_sum a m - partial_sum a n) + a (S m)) by ring.
          (* S_b(S m) - S_b(n) = (S_b(m) - S_b(n)) + b(S m) *)
          assert (Hb_nn' : 0 <= partial_sum b m - partial_sum b n).
          { assert (Hle : partial_sum b n <= partial_sum b m).
            { apply inc_le; [|exact Hnm'].
              intros k. cbn [partial_sum].
              assert (Hbk : 0 <= b (S k)).
              { eapply Qle_trans; [apply Qabs_nonneg | exact (Hab (S k))]. }
              lra. }
            lra. }
          assert (IH : Qabs (partial_sum a m - partial_sum a n) <=
                       partial_sum b m - partial_sum b n)
            by (apply IHm; [exact Hnm' | exact Hb_nn']).
          (* |x + y| <= |x| + |y| <= (S_b(m) - S_b(n)) + |a(S m)| <= (S_b(m) - S_b(n)) + b(S m) *)
          assert (Htri : Qabs ((partial_sum a m - partial_sum a n) + a (S m)) <=
                         Qabs (partial_sum a m - partial_sum a n) + Qabs (a (S m)))
            by (apply Qabs_triangle).
          specialize (Hab (S m)).
          lra. }
    assert (Habs_b : Qabs (partial_sum b m - partial_sum b n) < eps) by exact HN.
    apply Qabs_Qlt_condition in Habs_b.
    assert (Habs_bound : Qabs (partial_sum a m - partial_sum a n) < eps) by lra.
    exact Habs_bound.
  - (* m < n: symmetric case *)
    assert (HNn : (N <= n)%nat) by lia.
    assert (HNm : (N <= m)%nat) by lia.
    (* |S_a(m) - S_a(n)| = |S_a(n) - S_a(m)| *)
    setoid_replace (partial_sum a m - partial_sum a n)
      with (- (partial_sum a n - partial_sum a m)) by ring.
    rewrite Qabs_opp.
    (* Now same as above with n, m swapped *)
    specialize (HN n m HNn HNm).
    assert (Hb_nn : 0 <= partial_sum b n - partial_sum b m).
    { assert (Hle : partial_sum b m <= partial_sum b n).
      { apply inc_le; [|lia].
        intros k. cbn [partial_sum].
        assert (Hbk : 0 <= b (S k)).
        { eapply Qle_trans; [apply Qabs_nonneg | exact (Hab (S k))]. }
        lra. }
      lra. }
    assert (Hab_tail : Qabs (partial_sum a n - partial_sum a m) <=
                       partial_sum b n - partial_sum b m).
    { clear HN Heps Hm Hn HNn HNm.
      revert m Hnm Hb_nn.
      induction n; intros m' Hnm Hb_nn.
      - lia.
      - destruct (Nat.eq_dec m' n) as [-> | Hne].
        + (* m' = n *)
          change (partial_sum a (S n)) with (partial_sum a n + a (S n)).
          change (partial_sum b (S n)) with (partial_sum b n + b (S n)).
          setoid_replace (partial_sum a n + a (S n) - partial_sum a n)
            with (a (S n)) by ring.
          assert (HabSn := Hab (S n)).
          assert (Habs_bound : Qabs (a (S n)) <= b (S n)) by exact HabSn.
          lra.
        + (* m' <> n, so m' < n *)
          assert (Hnm' : (m' < n)%nat) by lia.
          change (partial_sum a (S n)) with (partial_sum a n + a (S n)).
          change (partial_sum b (S n)) with (partial_sum b n + b (S n)).
          setoid_replace (partial_sum a n + a (S n) - partial_sum a m')
            with ((partial_sum a n - partial_sum a m') + a (S n)) by ring.
          assert (Hb_nn' : 0 <= partial_sum b n - partial_sum b m').
          { assert (Hle : partial_sum b m' <= partial_sum b n).
            { apply inc_le; [|lia].
              intros k. cbn [partial_sum].
              assert (Hbk : 0 <= b (S k)).
              { eapply Qle_trans; [apply Qabs_nonneg | exact (Hab (S k))]. }
              lra. }
            lra. }
          assert (IH : Qabs (partial_sum a n - partial_sum a m') <=
                       partial_sum b n - partial_sum b m')
            by (apply IHn; [exact Hnm' | exact Hb_nn']).
          assert (Htri : Qabs ((partial_sum a n - partial_sum a m') + a (S n)) <=
                         Qabs (partial_sum a n - partial_sum a m') + Qabs (a (S n)))
            by (apply Qabs_triangle).
          specialize (Hab (S n)).
          lra. }
    assert (Habs_b : Qabs (partial_sum b n - partial_sum b m) < eps) by exact HN.
    apply Qabs_Qlt_condition in Habs_b.
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: CAUCHYSEQ CONSTRUCTIONS                                       *)
(* ========================================================================= *)

(** Build a CauchySeq from a convergent series *)
Definition series_limit (a : nat -> Q) (H : is_cauchy (partial_sum a)) : CauchySeq :=
  mkCauchy (partial_sum a) H.

(** Build a CauchySeq for the geometric series *)
Definition geometric_limit (r : Q) (Hr : 0 <= r) (Hr1 : r < 1) : CauchySeq :=
  series_limit (fun k => Qpow r k) (geometric_series_cauchy r Hr Hr1).

(** Nonneg series: partial sums bounded by the limit *)
Lemma series_nonneg_upper_bound : forall (a : nat -> Q) (H : is_cauchy (partial_sum a)),
  (forall n, 0 <= a n) ->
  forall n, cauchy_le (cauchy_const (partial_sum a n)) (series_limit a H).
Proof.
  intros a H Ha n.
  intros eps Heps.
  exists n. intros k Hk. simpl.
  assert (Hle : partial_sum a n <= partial_sum a k).
  { apply inc_le; [|exact Hk].
    intros m. apply partial_sum_nonneg_inc. exact Ha. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 7: VERIFICATION                                                    *)
(* ========================================================================= *)

Check Qpow_nonneg.
Check Qpow_monotone_dec.
Check Qpow_bound_1.
Check Qpow_pos.
Check bernoulli_ineq.
Check Qpow_vanish.
Check Qpow_cauchy.
Check Qpow_limit_zero.
Check partial_sum_nonneg_inc.
Check partial_sum_monotone.
Check partial_sum_nonneg_bound.
Check Qle_div_r.
Check geometric_sum_identity.
Check geometric_partial_sum_bound.
Check geometric_series_cauchy.
Check comparison_test.
Check absolute_convergence.
Check series_nonneg_upper_bound.

Print Assumptions geometric_series_cauchy.
Print Assumptions comparison_test.
Print Assumptions absolute_convergence.
Print Assumptions Qpow_vanish.
Print Assumptions bernoulli_ineq.
Print Assumptions Qpow_limit_zero.
Print Assumptions series_nonneg_upper_bound.
