(* ========================================================================= *)
(*            POWER SERIES AND EXPONENTIAL CONVERGENCE                       *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove convergence of power series and the exponential:         *)
(*    - Geometric domination from ratio bound                               *)
(*    - Ratio test (division-free formulation)                              *)
(*    - Power series convergence inside radius                              *)
(*    - Exponential series converges for all x (crown jewel)                *)
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
From ToS Require Import RealField.
From ToS Require Import MonotoneConvergence.
From ToS Require Import SeriesConvergence.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: HELPERS                                                        *)
(* ========================================================================= *)

(** |r^n| = |r|^n *)
Lemma Qabs_Qpow : forall (r : Q) (n : nat),
  Qabs (Qpow r n) == Qpow (Qabs r) n.
Proof.
  intros r n. induction n; cbn [Qpow].
  - rewrite Qabs_pos; lra.
  - rewrite Qabs_Qmult.
    apply Qmult_comp; [reflexivity | exact IHn].
Qed.

(** Scaling partial sums *)
Lemma partial_sum_scale : forall (C : Q) (a : nat -> Q) (n : nat),
  partial_sum (fun k => C * a k) n == C * partial_sum a n.
Proof.
  intros C a n. induction n; cbn [partial_sum].
  - reflexivity.
  - transitivity (C * partial_sum a n + C * a (S n)).
    + apply Qplus_comp; [exact IHn | reflexivity].
    + ring.
Qed.

(** Splitting partial sums at index N *)
Lemma partial_sum_split : forall (f : nat -> Q) (N m : nat),
  partial_sum f (N + S m) == partial_sum f N + partial_sum (fun j => f (S N + j)%nat) m.
Proof.
  intros f N m. induction m.
  - replace (N + 1)%nat with (S N) by lia. cbn [partial_sum].
    replace (S N + 0)%nat with (S N) by lia. ring.
  - replace (N + S (S m))%nat with (S (N + S m)) by lia.
    cbn [partial_sum].
    rewrite IHm.
    replace (S (N + S m)) with (S N + S m)%nat by lia.
    ring.
Qed.

(** Partial sums respect pointwise Qeq *)
Lemma partial_sum_Qeq : forall (f g : nat -> Q) (n : nat),
  (forall k, (k <= n)%nat -> f k == g k) ->
  partial_sum f n == partial_sum g n.
Proof.
  intros f g n Hfg. induction n; cbn [partial_sum].
  - apply Hfg. lia.
  - apply Qplus_comp.
    + apply IHn. intros k Hk. apply Hfg. lia.
    + apply Hfg. lia.
Qed.

(* ========================================================================= *)
(* SECTION 2: GEOMETRIC DOMINATION AND RATIO TEST                           *)
(* ========================================================================= *)

(** If |a(S n)| <= r * |a(n)| for n >= N, then |a(N+k)| <= |a(N)| * r^k *)
Lemma geometric_domination : forall (a : nat -> Q) (r : Q) (N : nat),
  0 <= r ->
  (forall n, (N <= n)%nat -> Qabs (a (S n)) <= r * Qabs (a n)) ->
  forall k, Qabs (a (N + k)%nat) <= Qabs (a N) * Qpow r k.
Proof.
  intros a r N Hr Hrat k. induction k.
  - replace (N + 0)%nat with N by lia. cbn [Qpow]. lra.
  - replace (N + S k)%nat with (S (N + k)) by lia.
    specialize (Hrat (N + k)%nat ltac:(lia)).
    assert (H : r * Qabs (a (N + k)%nat) <= r * (Qabs (a N) * Qpow r k)).
    { assert (Hdiff : 0 <= r * (Qabs (a N) * Qpow r k - Qabs (a (N + k)%nat))).
      { apply Qmult_le_0_compat; [exact Hr | lra]. }
      lra. }
    cbn [Qpow].
    assert (Heq : r * (Qabs (a N) * Qpow r k) == Qabs (a N) * (r * Qpow r k)) by ring.
    lra.
Qed.

(** Ratio test: if |a(S n)| <= r * |a(n)| eventually, then Σa converges *)
Theorem ratio_test_abs : forall (a : nat -> Q) (r : Q) (N : nat),
  0 <= r -> r < 1 ->
  (forall n, (N <= n)%nat -> Qabs (a (S n)) <= r * Qabs (a n)) ->
  is_cauchy (partial_sum a).
Proof.
  intros a r N Hr Hr1 Hrat.
  (* Build dominating sequence: b(n) = |a(n)| for n <= N, |a(N)| * r^{n-N} for n > N *)
  set (b := fun n => if (n <=? N)%nat then Qabs (a n)
                      else Qabs (a N) * Qpow r (n - N)).
  apply absolute_convergence with b.
  - (* |a(n)| <= b(n) *)
    intros n. unfold b.
    destruct (n <=? N)%nat eqn:E.
    + apply Nat.leb_le in E. apply Qle_refl.
    + apply Nat.leb_gt in E.
      assert (Hdom := geometric_domination a r N Hr Hrat (n - N)).
      replace (N + (n - N))%nat with n in Hdom by lia.
      exact Hdom.
  - (* is_cauchy (partial_sum b) *)
    apply partial_sum_nonneg_bound with
      (partial_sum (fun k => Qabs (a k)) N + Qabs (a N) * / (1 - r)).
    + (* b(n) >= 0 *)
      intros n. unfold b.
      destruct (n <=? N)%nat eqn:E.
      * apply Qabs_nonneg.
      * apply Qmult_le_0_compat; [apply Qabs_nonneg | apply Qpow_nonneg; exact Hr].
    + (* partial_sum b n <= B *)
      intros n. unfold b.
      destruct (Nat.le_gt_cases n N) as [HnN | HnN].
      * (* n <= N: partial_sum b n = partial_sum |a| n <= partial_sum |a| N *)
        assert (Hsame : partial_sum (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                         else Qabs (a N) * Qpow r (n0 - N)) n ==
                         partial_sum (fun k => Qabs (a k)) n).
        { apply partial_sum_Qeq. intros k Hk.
          assert (Hle : (k <=? N)%nat = true) by (apply Nat.leb_le; lia).
          rewrite Hle. reflexivity. }
        assert (Hinc : partial_sum (fun k => Qabs (a k)) n <=
                        partial_sum (fun k => Qabs (a k)) N).
        { apply inc_le; [|exact HnN].
          intros k0. cbn [partial_sum]. specialize (Qabs_nonneg (a (S k0))). lra. }
        assert (Hinv_pos : 0 < / (1 - r)) by (apply Qinv_lt_0_compat; lra).
        assert (Htail_nn : 0 <= Qabs (a N) * / (1 - r)).
        { apply Qmult_le_0_compat; [apply Qabs_nonneg | lra]. }
        lra.
      * (* n > N: split partial_sum at N, bound tail by geometric *)
        assert (Hsplit : exists m, n = (N + S m)%nat) by (exists (n - S N)%nat; lia).
        destruct Hsplit as [m Hm]. subst n.
        assert (Hps : partial_sum (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                       else Qabs (a N) * Qpow r (n0 - N)) (N + S m) ==
                       partial_sum (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                       else Qabs (a N) * Qpow r (n0 - N)) N +
                       partial_sum (fun j => (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                       else Qabs (a N) * Qpow r (n0 - N)) (S N + j)%nat) m).
        { apply partial_sum_split. }
        (* First part: partial_sum b N = partial_sum |a| N *)
        assert (Hfirst : partial_sum (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                          else Qabs (a N) * Qpow r (n0 - N)) N ==
                          partial_sum (fun k => Qabs (a k)) N).
        { apply partial_sum_Qeq. intros k Hk.
          assert (Hle : (k <=? N)%nat = true) by (apply Nat.leb_le; lia).
          rewrite Hle. reflexivity. }
        (* Tail terms: b(S N + j) = |a(N)| * r^{S j} *)
        assert (Htail_eq : forall j, (j <= m)%nat ->
                  (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                   else Qabs (a N) * Qpow r (n0 - N)) (S N + j)%nat ==
                  Qabs (a N) * Qpow r (S j)).
        { intros j Hj.
          assert (Hgt : (S N + j <=? N)%nat = false) by (apply Nat.leb_gt; lia).
          rewrite Hgt. replace (S N + j - N)%nat with (S j) by lia. reflexivity. }
        assert (Htail : partial_sum (fun j => (fun n0 => if (n0 <=? N)%nat then Qabs (a n0)
                         else Qabs (a N) * Qpow r (n0 - N)) (S N + j)%nat) m ==
                         partial_sum (fun j => Qabs (a N) * Qpow r (S j)) m).
        { apply partial_sum_Qeq. exact Htail_eq. }
        (* Qpow r (S j) = r * Qpow r j *)
        assert (Htail2 : partial_sum (fun j => Qabs (a N) * Qpow r (S j)) m ==
                          partial_sum (fun j => Qabs (a N) * r * Qpow r j) m).
        { apply partial_sum_Qeq. intros j Hj. cbn [Qpow]. ring. }
        (* Factor out: C * partial_sum (Qpow r) m *)
        assert (Htail3 : partial_sum (fun j => Qabs (a N) * r * Qpow r j) m ==
                          (Qabs (a N) * r) * partial_sum (fun j => Qpow r j) m).
        { apply partial_sum_scale. }
        (* Geometric bound: partial_sum (Qpow r) m <= /(1-r) *)
        assert (Hgeo : partial_sum (fun j => Qpow r j) m <= / (1 - r)).
        { apply geometric_partial_sum_bound; lra. }
        (* (|a(N)| * r) * partial_sum <= |a(N)| * r * /(1-r) <= |a(N)| * /(1-r) *)
        assert (Hann : 0 <= Qabs (a N)) by (apply Qabs_nonneg).
        assert (Hinv_pos : 0 < / (1 - r)) by (apply Qinv_lt_0_compat; lra).
        assert (Htail_bound : (Qabs (a N) * r) * partial_sum (fun j => Qpow r j) m <=
                               Qabs (a N) * / (1 - r)).
        { (* Step 1: C * ps <= C * inv  where C = |a(N)| * r *)
          assert (H1 : 0 <= (Qabs (a N) * r) * (/ (1 - r) - partial_sum (fun j => Qpow r j) m)).
          { apply Qmult_le_0_compat.
            - apply Qmult_le_0_compat; [exact Hann | exact Hr].
            - lra. }
          assert (H1' : (Qabs (a N) * r) * partial_sum (fun j => Qpow r j) m <=
                         (Qabs (a N) * r) * / (1 - r)) by lra.
          (* Step 2: |a(N)| * r * inv <= |a(N)| * 1 * inv *)
          assert (H2 : 0 <= (Qabs (a N) * (1 - r)) * / (1 - r)).
          { apply Qmult_le_0_compat.
            - apply Qmult_le_0_compat; [exact Hann | lra].
            - lra. }
          assert (H3 : Qabs (a N) * r * / (1 - r) <= Qabs (a N) * 1 * / (1 - r)) by lra.
          assert (H4 : Qabs (a N) * 1 * / (1 - r) == Qabs (a N) * / (1 - r)) by ring.
          lra. }
        lra.
Qed.

(** Ratio bound transfers from coefficients to a_n * x^n *)
Lemma power_term_ratio_bound : forall (a : nat -> Q) (x r : Q) (N : nat),
  0 <= r ->
  (forall n, (N <= n)%nat -> Qabs (a (S n)) * Qabs x <= r * Qabs (a n)) ->
  forall n, (N <= n)%nat ->
    Qabs (a (S n) * Qpow x (S n)) <= r * Qabs (a n * Qpow x n).
Proof.
  intros a x r N Hr Hrat n Hn.
  rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  (* LHS: |a(Sn)| * |x^{Sn}| = |a(Sn)| * (|x| * |x^n|) *)
  assert (Hxpow : Qabs (Qpow x (S n)) == Qabs x * Qabs (Qpow x n)).
  { cbn [Qpow]. apply Qabs_Qmult. }
  (* RHS: r * (|a(n)| * |x^n|) *)
  specialize (Hrat n Hn).
  assert (Hxn_nn : 0 <= Qabs (Qpow x n)) by (apply Qabs_nonneg).
  (* |a(Sn)| * (|x| * |x^n|) = (|a(Sn)| * |x|) * |x^n| <= (r * |a(n)|) * |x^n| *)
  assert (H1 : Qabs (a (S n)) * (Qabs x * Qabs (Qpow x n)) ==
                (Qabs (a (S n)) * Qabs x) * Qabs (Qpow x n)) by ring.
  assert (H2 : r * (Qabs (a n) * Qabs (Qpow x n)) ==
                (r * Qabs (a n)) * Qabs (Qpow x n)) by ring.
  assert (H3 : (Qabs (a (S n)) * Qabs x) * Qabs (Qpow x n) <=
                (r * Qabs (a n)) * Qabs (Qpow x n)).
  { apply Qmult_le_compat_r; [exact Hrat | exact Hxn_nn]. }
  assert (H4 : Qabs (a (S n)) * Qabs (Qpow x (S n)) ==
                Qabs (a (S n)) * (Qabs x * Qabs (Qpow x n))).
  { apply Qmult_comp; [reflexivity | exact Hxpow]. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: POWER SERIES                                                   *)
(* ========================================================================= *)

(** Power series convergence *)
Theorem power_series_converges : forall (a : nat -> Q) (x r : Q) (N : nat),
  0 <= r -> r < 1 ->
  (forall n, (N <= n)%nat -> Qabs (a (S n)) * Qabs x <= r * Qabs (a n)) ->
  is_cauchy (partial_sum (fun n => a n * Qpow x n)).
Proof.
  intros a x r N Hr Hr1 Hrat.
  apply ratio_test_abs with r N; [exact Hr | exact Hr1 |].
  intros n Hn.
  exact (power_term_ratio_bound a x r N Hr Hrat n Hn).
Qed.

(** Cauchy property transfers through pointwise Qeq *)
Lemma is_cauchy_Qeq_compat : forall (f g : nat -> Q),
  (forall n, f n == g n) ->
  is_cauchy f -> is_cauchy g.
Proof.
  intros f g Hfg Hf eps Heps.
  destruct (Hf eps Heps) as [N0 HN0].
  exists N0. intros m n Hm Hn.
  assert (Heq : g m - g n == f m - f n).
  { assert (H1 := Hfg m). assert (H2 := Hfg n). lra. }
  qabs_rw Heq. exact (HN0 m n Hm Hn).
Qed.

(** Build CauchySeq from convergent power series *)
Definition power_series_limit (a : nat -> Q) (x r : Q) (N : nat)
  (Hr : 0 <= r) (Hr1 : r < 1)
  (Hrat : forall n, (N <= n)%nat -> Qabs (a (S n)) * Qabs x <= r * Qabs (a n))
  : CauchySeq :=
  series_limit (fun n => a n * Qpow x n) (power_series_converges a x r N Hr Hr1 Hrat).

(* ========================================================================= *)
(* SECTION 4: FACTORIAL AND EXPONENTIAL TERM                                 *)
(* ========================================================================= *)

Fixpoint Qfact (n : nat) : Q :=
  match n with
  | 0%nat => 1
  | S k => inject_Z (Z.of_nat (S k)) * Qfact k
  end.

Definition exp_term (x : Q) (n : nat) : Q := Qpow x n * / Qfact n.

Definition exp_series (x : Q) : nat -> Q := partial_sum (exp_term x).

Lemma Qfact_pos : forall n, 0 < Qfact n.
Proof.
  induction n; cbn [Qfact].
  - lra.
  - apply Qmult_lt_0_compat; [| exact IHn].
    assert (Hz : (0 < Z.of_nat (S n))%Z) by lia.
    unfold Qlt, inject_Z. simpl. lia.
Qed.

Lemma Qfact_nonzero : forall n, ~ Qfact n == 0.
Proof.
  intros n Heq. assert (Hpos := Qfact_pos n). lra.
Qed.

(** Multiplicative ratio relation: (n+1) * exp_term(x, n+1) = x * exp_term(x, n) *)
Lemma exp_term_ratio : forall (x : Q) (n : nat),
  inject_Z (Z.of_nat (S n)) * exp_term x (S n) == x * exp_term x n.
Proof.
  intros x n. unfold exp_term. cbn [Qpow Qfact].
  field.
  split.
  - (* denominator <> 0 *)
    intro Heq.
    assert (Hpos1 : 0 < inject_Z (Z.of_nat (S n))).
    { unfold Qlt, inject_Z. simpl. lia. }
    assert (Hpos2 := Qfact_pos n).
    assert (Hprod : 0 < inject_Z (Z.of_nat (S n)) * Qfact n).
    { apply Qmult_lt_0_compat; [exact Hpos1 | exact Hpos2]. }
    lra.
  - intro Heq2.
    assert (Hpos : 0 < inject_Z (Z.of_nat (S n))).
    { unfold Qlt, inject_Z. simpl. lia. }
    lra.
Qed.

(** |exp_term(x, n+1)| * (n+1) = |x| * |exp_term(x, n)| *)
Lemma exp_term_abs_ratio : forall (x : Q) (n : nat),
  Qabs (exp_term x (S n)) * inject_Z (Z.of_nat (S n)) ==
  Qabs x * Qabs (exp_term x n).
Proof.
  intros x n.
  assert (Hratio := exp_term_ratio x n).
  (* Take Qabs of both sides *)
  assert (Habs := Qabs_wd _ _ Hratio).
  (* |inject_Z(Sn) * exp_term x (Sn)| = |x * exp_term x n| *)
  rewrite Qabs_Qmult in Habs.
  rewrite Qabs_Qmult in Habs.
  (* |inject_Z(Sn)| = inject_Z(Sn) since Sn > 0 *)
  assert (Hsn_pos : 0 < inject_Z (Z.of_nat (S n))).
  { assert (Hz : (0 < Z.of_nat (S n))%Z) by lia.
    unfold Qlt, inject_Z. simpl. lia. }
  rewrite Qabs_pos in Habs by lra.
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: EXPONENTIAL CONVERGENCE                                        *)
(* ========================================================================= *)

(** For any 0 < r < 1, eventually |exp_term x (S n)| <= r * |exp_term x n| *)
Lemma exp_ratio_bound : forall (x : Q) (r : Q),
  0 < r -> r < 1 ->
  exists N : nat, forall n, (N <= n)%nat ->
    Qabs (exp_term x (S n)) <= r * Qabs (exp_term x n).
Proof.
  intros x r Hr Hr1.
  (* Get N such that |x| < r * N, i.e., N > |x|/r *)
  destruct (nat_archimedean (Qabs x) r Hr) as [K HK].
  (* HK : Qabs x < inject_Z (Z.of_nat K) * r *)
  exists K. intros n Hn.
  (* From exp_term_abs_ratio: |et(Sn)| * (Sn) = |x| * |et(n)| *)
  assert (Habs_ratio := exp_term_abs_ratio x n).
  (* Need: |x| <= r * (Sn) *)
  assert (Hsn_pos : 0 < inject_Z (Z.of_nat (S n))).
  { assert (Hz : (0 < Z.of_nat (S n))%Z) by lia.
    unfold Qlt, inject_Z. simpl. lia. }
  assert (HK_le_Sn : inject_Z (Z.of_nat K) <= inject_Z (Z.of_nat (S n))).
  { unfold Qle, inject_Z. simpl. lia. }
  assert (Hx_bound : Qabs x <= r * inject_Z (Z.of_nat (S n))).
  { assert (H1 : inject_Z (Z.of_nat K) * r <= inject_Z (Z.of_nat (S n)) * r).
    { apply Qmult_le_compat_r; [exact HK_le_Sn | lra]. }
    assert (H2 : inject_Z (Z.of_nat (S n)) * r == r * inject_Z (Z.of_nat (S n))) by ring.
    lra. }
  (* |et(Sn)| * (Sn) = |x| * |et(n)| <= r * (Sn) * |et(n)| *)
  assert (Het_nn : 0 <= Qabs (exp_term x n)) by (apply Qabs_nonneg).
  assert (Hprod_bound : Qabs x * Qabs (exp_term x n) <=
                         r * inject_Z (Z.of_nat (S n)) * Qabs (exp_term x n)).
  { apply Qmult_le_compat_r; [exact Hx_bound | exact Het_nn]. }
  (* So |et(Sn)| * (Sn) <= r * (Sn) * |et(n)| *)
  assert (Hle : Qabs (exp_term x (S n)) * inject_Z (Z.of_nat (S n)) <=
                r * inject_Z (Z.of_nat (S n)) * Qabs (exp_term x n)) by lra.
  (* Cancel (Sn): |et(Sn)| * (Sn) <= (r * |et(n)|) * (Sn), divide both sides *)
  assert (Hinv_nn : 0 <= / inject_Z (Z.of_nat (S n))).
  { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hsn_pos. }
  assert (Hle2 : Qabs (exp_term x (S n)) * inject_Z (Z.of_nat (S n)) <=
                  (r * Qabs (exp_term x n)) * inject_Z (Z.of_nat (S n))).
  { assert (Heq : r * inject_Z (Z.of_nat (S n)) * Qabs (exp_term x n) ==
                  (r * Qabs (exp_term x n)) * inject_Z (Z.of_nat (S n))) by ring. lra. }
  assert (Hmul : Qabs (exp_term x (S n)) * inject_Z (Z.of_nat (S n)) *
                  / inject_Z (Z.of_nat (S n)) <=
                  (r * Qabs (exp_term x n)) * inject_Z (Z.of_nat (S n)) *
                  / inject_Z (Z.of_nat (S n))).
  { apply Qmult_le_compat_r; [exact Hle2 | exact Hinv_nn]. }
  assert (Hsn_nz : ~ inject_Z (Z.of_nat (S n)) == 0).
  { intro Heq. lra. }
  assert (Hlhs : Qabs (exp_term x (S n)) * inject_Z (Z.of_nat (S n)) *
                  / inject_Z (Z.of_nat (S n)) ==
                  Qabs (exp_term x (S n))).
  { field. exact Hsn_nz. }
  assert (Hrhs : (r * Qabs (exp_term x n)) * inject_Z (Z.of_nat (S n)) *
                  / inject_Z (Z.of_nat (S n)) ==
                  r * Qabs (exp_term x n)).
  { field. exact Hsn_nz. }
  lra.
Qed.

(** Crown jewel: exp(x) = Σ x^n/n! converges for all x *)
Theorem exp_series_cauchy : forall (x : Q),
  is_cauchy (partial_sum (exp_term x)).
Proof.
  intros x.
  destruct (exp_ratio_bound x (1#2) ltac:(lra) ltac:(lra)) as [N HN].
  exact (ratio_test_abs (exp_term x) (1#2) N ltac:(lra) ltac:(lra) HN).
Qed.

(** exp_series as CauchySeq *)
Definition exp_limit (x : Q) : CauchySeq :=
  series_limit (exp_term x) (exp_series_cauchy x).

(** exp_term 0 (S n) = 0 *)
Lemma exp_term_zero : forall n,
  exp_term 0 (S n) == 0.
Proof.
  intros n. unfold exp_term. cbn [Qpow].
  assert (H : 0 * Qpow 0 n == 0) by ring.
  transitivity (0 * / Qfact (S n)).
  - apply Qmult_comp; [exact H | reflexivity].
  - ring.
Qed.

(** exp(0) = 1: partial_sum (exp_term 0) n = 1 for all n *)
Lemma exp_partial_sum_zero : forall n,
  partial_sum (exp_term 0) n == 1.
Proof.
  induction n; cbn [partial_sum].
  - (* exp_term 0 0 = 1 * /1 = 1 *)
    unfold exp_term. cbn [Qpow Qfact]. field.
  - rewrite exp_term_zero. lra.
Qed.

(** exp(0) ~ const 1 *)
Lemma exp_series_zero :
  cauchy_equiv (exp_limit 0) (cauchy_const 1).
Proof.
  intros eps Heps.
  exists 0%nat. intros n Hn. simpl.
  assert (Heq : partial_sum (exp_term 0) n - 1 == 0).
  { assert (H := exp_partial_sum_zero n). lra. }
  qabs_rw Heq. rewrite Qabs_pos; lra.
Qed.

(** exp_term is positive for positive x *)
Lemma exp_term_pos : forall (x : Q) (n : nat),
  0 < x -> 0 < exp_term x n.
Proof.
  intros x n Hx. unfold exp_term.
  apply Qmult_lt_0_compat.
  - exact (Qpow_pos x n Hx).
  - apply Qinv_lt_0_compat. exact (Qfact_pos n).
Qed.

(* ========================================================================= *)
(* SECTION 6: VERIFICATION                                                    *)
(* ========================================================================= *)

Check Qabs_Qpow.
Check partial_sum_scale.
Check partial_sum_split.
Check partial_sum_Qeq.
Check geometric_domination.
Check ratio_test_abs.
Check power_term_ratio_bound.
Check power_series_converges.
Check is_cauchy_Qeq_compat.
Check Qfact_pos.
Check Qfact_nonzero.
Check exp_term_ratio.
Check exp_term_abs_ratio.
Check exp_ratio_bound.
Check exp_series_cauchy.
Check exp_term_zero.
Check exp_partial_sum_zero.
Check exp_series_zero.
Check exp_term_pos.

Print Assumptions ratio_test_abs.
Print Assumptions power_series_converges.
Print Assumptions exp_series_cauchy.
Print Assumptions exp_series_zero.
