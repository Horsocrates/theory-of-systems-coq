(* ========================================================================= *)
(*            FIXED POINT THEORY                                            *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Banach contraction mapping theorem over Q:                     *)
(*    - Contraction mapping definition and iterate properties               *)
(*    - Convergence of iterates to Cauchy fixed point                       *)
(*    - Uniqueness and error bounds                                         *)
(*    - Composition, powers, and perturbation stability                     *)
(*                                                                          *)
(*  AXIOMS: classic (inherited from MonotoneConvergence via Qpow_vanish)    *)
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
From ToS Require Import SeriesConvergence.

Open Scope Q_scope.

(** Helper: left multiplication preserves <= (not in Rocq 9.0 stdlib) *)
Lemma Qmult_le_compat_l : forall x y z : Q,
  x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros x y z Hxy Hz.
  setoid_replace (z * x) with (x * z) by ring.
  setoid_replace (z * y) with (y * z) by ring.
  apply Qmult_le_compat_r; assumption.
Qed.

(* ========================================================================= *)
(* DEFINITIONS                                                               *)
(* ========================================================================= *)

(** A contraction mapping on [a,b] with contraction factor c *)
Definition is_contraction (f : Q -> Q) (a b c : Q) : Prop :=
  0 <= c /\ c < 1 /\
  (forall x, a <= x -> x <= b -> a <= f x /\ f x <= b) /\
  (forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
    Qabs (f x - f y) <= c * Qabs (x - y)).

(** Iterate: f^n(x) *)
Fixpoint iterate (f : Q -> Q) (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => x
  | S k => f (iterate f x k)
  end.

(* ========================================================================= *)
(* SECTION 1: ITERATE PROPERTIES                                            *)
(* ========================================================================= *)

(** 1. Iterates stay in [a,b] *)
Lemma iterate_in_interval : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  forall n, a <= iterate f x n /\ iterate f x n <= b.
Proof.
  intros f a b c x [_ [_ [Hself _]]] Hxa Hxb.
  induction n as [|n IHn].
  - simpl. split; assumption.
  - simpl. apply Hself; [apply IHn | apply IHn].
Qed.

(** 2. Helper: iterate f (f x) n = iterate f x (S n) *)
Lemma iterate_shift : forall f x n,
  iterate f (f x) n = iterate f x (S n).
Proof.
  intros f x n. induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** 3. Contraction of iterates: |f^n(x) - f^n(y)| <= c^n |x-y| *)
Lemma iterate_contraction : forall f a b c,
  is_contraction f a b c ->
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
  forall n, Qabs (iterate f x n - iterate f y n) <= Qpow c n * Qabs (x - y).
Proof.
  intros f a b c Hc x y Hxa Hxb Hya Hyb.
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  assert (Hc_full : is_contraction f a b c)
    by (unfold is_contraction; auto).
  induction n as [|n IHn].
  - simpl. lra.
  - simpl.
    assert (Hin_x := iterate_in_interval f a b c x Hc_full Hxa Hxb n).
    assert (Hin_y := iterate_in_interval f a b c y Hc_full Hya Hyb n).
    apply Qle_trans with (c * Qabs (iterate f x n - iterate f y n)).
    + apply Hcontr; [apply Hin_x | apply Hin_x | apply Hin_y | apply Hin_y].
    + setoid_replace (c * Qpow c n * Qabs (x - y))
        with (c * (Qpow c n * Qabs (x - y))) by ring.
      apply Qmult_le_compat_l; [exact IHn | exact Hc0].
Qed.

(** 4. Step shrink: |x_{n+1} - x_n| <= c^n |f(x)-x| *)
Lemma iterate_step_shrink : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  forall n, Qabs (iterate f x (S n) - iterate f x n) <=
            Qpow c n * Qabs (f x - x).
Proof.
  intros f a b c x Hc Hxa Hxb n.
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  assert (Hc_full : is_contraction f a b c)
    by (unfold is_contraction; auto).
  assert (Hfx := Hself x Hxa Hxb).
  (* iterate f x (S n) = f(iterate f x n) = iterate f (f x) n via shift *)
  rewrite <- iterate_shift.
  apply (iterate_contraction f a b c Hc_full (f x) x);
    [apply Hfx | apply Hfx | exact Hxa | exact Hxb].
Qed.

(* ========================================================================= *)
(* SECTION 2: GEOMETRIC INFRASTRUCTURE                                      *)
(* ========================================================================= *)

(** 5. Qpow monotone: c^m <= c^n for n <= m when 0 <= c <= 1 *)
Lemma qpow_le_mono : forall c n m,
  0 <= c -> c <= 1 -> (n <= m)%nat -> Qpow c m <= Qpow c n.
Proof.
  intros c n m Hc0 Hc1 Hnm.
  apply (dec_le (fun k => Qpow c k)).
  - intro k. apply Qpow_monotone_dec; assumption.
  - exact Hnm.
Qed.

(** 6. Qabs x <= 0 implies x == 0 *)
Lemma Qabs_0 : forall x, Qabs x <= 0 -> x == 0.
Proof.
  intros x Habs.
  assert (Hnn : 0 <= Qabs x) by apply Qabs_nonneg.
  assert (Habs0 : Qabs x == 0) by lra.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - assert (Hneg_abs : Qabs x == - x) by (apply Qabs_neg; lra).
    lra.
  - assert (Hpos_abs : Qabs x == x) by (apply Qabs_pos; exact Hpos).
    lra.
Qed.

(** 7. Contraction has at most one fixed point *)
Lemma contraction_unique_fixed : forall f a b c p q,
  is_contraction f a b c ->
  a <= p -> p <= b -> a <= q -> q <= b ->
  f p == p -> f q == q ->
  p == q.
Proof.
  intros f a b c p q [Hc0 [Hc1 [Hself Hcontr]]] Hpa Hpb Hqa Hqb Hfp Hfq.
  (* |p - q| = |f(p) - f(q)| <= c * |p - q| *)
  assert (Habs_eq : Qabs (f p - f q) == Qabs (p - q)).
  { apply Qabs_wd. lra. }
  assert (Hle : Qabs (f p - f q) <= c * Qabs (p - q))
    by (apply Hcontr; assumption).
  assert (Hle2 : Qabs (p - q) <= c * Qabs (p - q)) by lra.
  (* Case analysis: |p - q| > 0 gives contradiction *)
  destruct (Qlt_le_dec 0 (Qabs (p - q))) as [Hpos | Hzero].
  - (* |p-q| > 0 so c * |p-q| < |p-q| *)
    assert (Hlt : c * Qabs (p - q) < 1 * Qabs (p - q)).
    { apply Qmult_lt_compat_r; assumption. }
    lra.
  - (* |p-q| <= 0, so p - q = 0 *)
    apply Qabs_0 in Hzero. lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: CONVERGENCE OF ITERATES                                       *)
(* ========================================================================= *)

(** 8. Telescope bound: (1-c)|x_m - x_n| <= d*(c^n - c^m) for m >= n *)
Lemma iterate_diff_bound : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  forall n m, (n <= m)%nat ->
  (1 - c) * Qabs (iterate f x m - iterate f x n) <=
  Qabs (f x - x) * (Qpow c n - Qpow c m).
Proof.
  intros f a b c x Hc Hxa Hxb n.
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  assert (Hc_full : is_contraction f a b c)
    by (unfold is_contraction; auto).
  set (d := Qabs (f x - x)).
  induction m as [|m IHm]; intros Hnm.
  - (* m = 0, so n = 0 *)
    assert (Hn : n = 0%nat) by lia. subst n.
    simpl iterate. simpl Qpow.
    assert (Habs0 : Qabs (x - x) == 0).
    { assert (Hx0 : x - x == 0) by lra. rewrite (Qabs_wd _ _ Hx0). apply Qabs_pos. lra. }
    assert (Hd_nn : 0 <= d) by (unfold d; apply Qabs_nonneg).
    assert (Hlhs : (1 - c) * Qabs (x - x) <= 0).
    { apply Qeq_Qle. setoid_rewrite Habs0. ring. }
    assert (Hrhs : d * (Qpow c 0 - Qpow c 0) == 0).
    { simpl Qpow. ring. }
    lra.
  - destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
    + (* n = S m: trivial *)
      subst n.
      assert (Habs0 : Qabs (iterate f x (S m) - iterate f x (S m)) == 0).
      { assert (Hx0 : iterate f x (S m) - iterate f x (S m) == 0) by lra.
        rewrite (Qabs_wd _ _ Hx0). apply Qabs_pos. lra. }
      assert (Hd_nn : 0 <= d) by (unfold d; apply Qabs_nonneg).
      assert (Hpow_nn : 0 <= Qpow c (S m)) by (apply Qpow_nonneg; exact Hc0).
      assert (Hlhs : (1 - c) * Qabs (iterate f x (S m) - iterate f x (S m)) <= 0).
      { apply Qeq_Qle. setoid_rewrite Habs0. ring. }
      assert (Hrhs : d * (Qpow c (S m) - Qpow c (S m)) == 0) by ring.
      lra.
    + (* n < S m, so n <= m *)
      assert (Hnm' : (n <= m)%nat) by lia.
      specialize (IHm Hnm').
      (* Triangle: |x_{S m} - x_n| <= |x_{S m} - x_m| + |x_m - x_n| *)
      assert (Htri : Qabs (iterate f x (S m) - iterate f x n) <=
                      Qabs (iterate f x (S m) - iterate f x m) +
                      Qabs (iterate f x m - iterate f x n)).
      { setoid_replace (iterate f x (S m) - iterate f x n) with
          ((iterate f x (S m) - iterate f x m) + (iterate f x m - iterate f x n))
          by ring.
        apply Qabs_triangle. }
      (* Step shrink: |x_{S m} - x_m| <= c^m * d *)
      assert (Hstep : Qabs (iterate f x (S m) - iterate f x m) <= Qpow c m * d).
      { apply (iterate_step_shrink f a b c x Hc_full Hxa Hxb m). }
      (* Multiply triangle by (1-c) and bound each term *)
      assert (H1c : 0 < 1 - c) by lra.
      (* (1-c) * step <= (1-c) * c^m * d *)
      assert (Hstep_mul : (1 - c) * Qabs (iterate f x (S m) - iterate f x m) <=
                          (1 - c) * (Qpow c m * d)).
      { apply Qmult_le_compat_l; [exact Hstep | lra]. }
      (* From IH: (1-c) * |tail| <= d * (c^n - c^m) *)
      (* Combine: (1-c) * |total| <= (1-c)(step + tail) *)
      assert (Htotal : (1 - c) * Qabs (iterate f x (S m) - iterate f x n) <=
                        (1 - c) * Qabs (iterate f x (S m) - iterate f x m) +
                        (1 - c) * Qabs (iterate f x m - iterate f x n)).
      { assert (Hmul : (1 - c) * Qabs (iterate f x (S m) - iterate f x n) <=
                        (1 - c) * (Qabs (iterate f x (S m) - iterate f x m) +
                                   Qabs (iterate f x m - iterate f x n))).
        { apply Qmult_le_compat_l; [exact Htri | lra]. }
        lra. }
      (* Sum of bounds: (1-c)*c^m*d + d*(c^n - c^m) = d*(c^n - c*c^m) *)
      simpl Qpow.
      assert (Halg : (1 - c) * (Qpow c m * d) + d * (Qpow c n - Qpow c m) ==
                     d * (Qpow c n - c * Qpow c m)) by ring.
      lra.
Qed.

(** Helper: Qabs symmetry *)
Lemma Qabs_minus_sym : forall x y, Qabs (x - y) == Qabs (y - x).
Proof.
  intros x y.
  setoid_replace (x - y) with (- (y - x)) by ring.
  apply Qabs_opp.
Qed.

(** 9. MAIN: iterate sequence is Cauchy *)
Lemma iterate_is_cauchy : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  is_cauchy (fun n => iterate f x n).
Proof.
  intros f a b c x Hc Hxa Hxb eps Heps.
  assert (Hc_copy := Hc).
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  set (d := Qabs (f x - x)).
  assert (Hd_nn : 0 <= d) by (unfold d; apply Qabs_nonneg).
  assert (H1c : 0 < 1 - c) by lra.
  (* Strategy: (1-c)*|x_m - x_n| <= d * c^min(m,n), so enough that d*c^N < eps*(1-c) *)
  (* If d = 0 or c = 0: N = 1 suffices *)
  (* If d > 0 and c > 0: use Qpow_vanish *)
  destruct (Qlt_le_dec 0 (d * c)) as [Hdc_pos | Hdc_zero].
  - (* d*c > 0, so d > 0 and c > 0 *)
    assert (Hd_pos : 0 < d).
    { destruct (Qlt_le_dec 0 d) as [Hp|Hn]; [exact Hp|].
      exfalso. assert (Hd0 : d == 0) by lra.
      assert (Hdc_le : d * c <= 0) by (setoid_rewrite Hd0; lra). lra. }
    assert (Hc_pos : 0 < c).
    { destruct (Qlt_le_dec 0 c) as [Hp|Hn]; [exact Hp|].
      exfalso. assert (Hc00 : c == 0) by lra.
      assert (Hdc_le : d * c <= 0) by (setoid_rewrite Hc00; lra). lra. }
    assert (Htarget : 0 < eps * (1 - c) / d).
    { unfold Qdiv. apply Qmult_lt_0_compat;
        [apply Qmult_lt_0_compat; lra | apply Qinv_lt_0_compat; lra]. }
    destruct (Qpow_vanish c (eps * (1 - c) / d) Hc_pos Hc1 Htarget) as [N HN].
    assert (HdcN : d * Qpow c N < eps * (1 - c)).
    { assert (Hmul : Qpow c N * d < eps * (1 - c) / d * d).
      { apply Qmult_lt_compat_r; [exact Hd_pos | exact HN]. }
      assert (Hsimp : eps * (1 - c) / d * d == eps * (1 - c))
        by (field; lra).
      assert (Hcomm_dN : Qpow c N * d == d * Qpow c N) by ring.
      lra. }
    exists N. intros m n Hm Hn.
    destruct (Nat.le_ge_cases n m) as [Hnm | Hmn].
    + assert (Htel := iterate_diff_bound f a b c x Hc_copy Hxa Hxb n m Hnm).
      fold d in Htel.
      assert (Hcm_nn : 0 <= Qpow c m) by (apply Qpow_nonneg; exact Hc0).
      assert (Hcn_le : Qpow c n <= Qpow c N)
        by (apply qpow_le_mono; [exact Hc0 | lra | exact Hn]).
      assert (Hdiff_le : d * (Qpow c n - Qpow c m) <= d * Qpow c n).
      { apply Qmult_le_compat_l; [lra | lra]. }
      assert (Hdc_le : d * Qpow c n <= d * Qpow c N).
      { apply Qmult_le_compat_l; [exact Hcn_le | lra]. }
      apply (proj1 (Qmult_lt_r (Qabs (iterate f x m - iterate f x n)) eps
                     (1 - c) H1c)).
      assert (Hcomm : (1 - c) * Qabs (iterate f x m - iterate f x n) ==
                      Qabs (iterate f x m - iterate f x n) * (1 - c)) by ring.
      lra.
    + assert (Htel := iterate_diff_bound f a b c x Hc_copy Hxa Hxb m n Hmn).
      fold d in Htel.
      assert (Hcn_nn : 0 <= Qpow c n) by (apply Qpow_nonneg; exact Hc0).
      assert (Hcm_le : Qpow c m <= Qpow c N)
        by (apply qpow_le_mono; [exact Hc0 | lra | exact Hm]).
      assert (Hdiff_le : d * (Qpow c m - Qpow c n) <= d * Qpow c m).
      { apply Qmult_le_compat_l; [lra | lra]. }
      assert (Hdc_le : d * Qpow c m <= d * Qpow c N).
      { apply Qmult_le_compat_l; [exact Hcm_le | lra]. }
      assert (Hsym := Qabs_minus_sym (iterate f x m) (iterate f x n)).
      apply (proj1 (Qmult_lt_r (Qabs (iterate f x m - iterate f x n)) eps
                     (1 - c) H1c)).
      assert (Hlink : Qabs (iterate f x m - iterate f x n) * (1 - c) ==
                      (1 - c) * Qabs (iterate f x n - iterate f x m)).
      { setoid_rewrite Hsym. ring. }
      lra.
  - (* d*c <= 0: either d = 0 or c = 0 *)
    assert (Hdc_nn : 0 <= d * c).
    { apply Qmult_le_0_compat; [exact Hd_nn | exact Hc0]. }
    assert (Hdc0 : d * c == 0) by lra.
    exists 1%nat. intros m n Hm Hn.
    destruct (Nat.le_ge_cases n m) as [Hnm | Hmn].
    + assert (Htel := iterate_diff_bound f a b c x Hc_copy Hxa Hxb n m Hnm).
      fold d in Htel.
      assert (Hcm_nn : 0 <= Qpow c m) by (apply Qpow_nonneg; exact Hc0).
      assert (Hcn_bound : Qpow c n <= Qpow c 1)
        by (apply qpow_le_mono; [exact Hc0 | lra | exact Hn]).
      simpl in Hcn_bound.
      assert (Hdc_bound : d * Qpow c n <= d * (c * 1)).
      { apply Qmult_le_compat_l; [lra | exact Hd_nn]. }
      assert (Hdc_eq : d * (c * 1) == d * c) by ring.
      assert (Hdn_nn : 0 <= d * Qpow c n).
      { apply Qmult_le_0_compat; [exact Hd_nn | apply Qpow_nonneg; exact Hc0]. }
      assert (Hdn0 : d * Qpow c n == 0) by lra.
      assert (Hdiff_le : d * (Qpow c n - Qpow c m) <= d * Qpow c n).
      { apply Qmult_le_compat_l; [lra | lra]. }
      assert (Habs_nn := Qabs_nonneg (iterate f x m - iterate f x n)).
      assert (Htel_bound : (1 - c) * Qabs (iterate f x m - iterate f x n) <= 0) by lra.
      assert (Habs0 : Qabs (iterate f x m - iterate f x n) <= 0).
      { destruct (Qlt_le_dec 0 (Qabs (iterate f x m - iterate f x n))) as [Hp | Hn0].
        - assert (Hprod : 0 < (1 - c) * Qabs (iterate f x m - iterate f x n)).
          { apply Qmult_lt_0_compat; lra. }
          lra.
        - exact Hn0. }
      lra.
    + assert (Htel := iterate_diff_bound f a b c x Hc_copy Hxa Hxb m n Hmn).
      fold d in Htel.
      assert (Hcn_nn : 0 <= Qpow c n) by (apply Qpow_nonneg; exact Hc0).
      assert (Hcm_bound : Qpow c m <= Qpow c 1)
        by (apply qpow_le_mono; [exact Hc0 | lra | exact Hm]).
      simpl in Hcm_bound.
      assert (Hdc_bound : d * Qpow c m <= d * (c * 1)).
      { apply Qmult_le_compat_l; [lra | exact Hd_nn]. }
      assert (Hdc_eq : d * (c * 1) == d * c) by ring.
      assert (Hdm_nn : 0 <= d * Qpow c m).
      { apply Qmult_le_0_compat; [exact Hd_nn | apply Qpow_nonneg; exact Hc0]. }
      assert (Hdm0 : d * Qpow c m == 0) by lra.
      assert (Hdiff_le : d * (Qpow c m - Qpow c n) <= d * Qpow c m).
      { apply Qmult_le_compat_l; [lra | lra]. }
      assert (Habs_nn := Qabs_nonneg (iterate f x n - iterate f x m)).
      assert (Htel_bound : (1 - c) * Qabs (iterate f x n - iterate f x m) <= 0) by lra.
      assert (Habs0 : Qabs (iterate f x n - iterate f x m) <= 0).
      { destruct (Qlt_le_dec 0 (Qabs (iterate f x n - iterate f x m))) as [Hp | Hn0].
        - assert (Hprod : 0 < (1 - c) * Qabs (iterate f x n - iterate f x m)).
          { apply Qmult_lt_0_compat; lra. }
          lra.
        - exact Hn0. }
      assert (Hsym := Qabs_minus_sym (iterate f x m) (iterate f x n)).
      lra.
Qed.

(** 10. Banach fixed point: construct CauchySeq from contraction *)
Definition banach_fixed_point (f : Q -> Q) (a b c x : Q)
  (Hc : is_contraction f a b c) (Hxa : a <= x) (Hxb : x <= b)
  : CauchySeq :=
  mkCauchy (fun n => iterate f x n)
           (iterate_is_cauchy f a b c x Hc Hxa Hxb).

(** 11. Approximate fixed point: |f(x_n) - x_n| -> 0 *)
Lemma approximate_fixed_point : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (f (iterate f x n) - iterate f x n) < eps.
Proof.
  intros f a b c x Hc Hxa Hxb eps Heps.
  assert (Hc_copy := Hc).
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  set (d := Qabs (f x - x)).
  assert (Hd_nn : 0 <= d) by (unfold d; apply Qabs_nonneg).
  (* f(x_n) - x_n = x_{n+1} - x_n, and |x_{n+1} - x_n| <= c^n * d *)
  (* Need c^n * d < eps *)
  destruct (Qlt_le_dec 0 (d * c)) as [Hdc_pos | Hdc_zero].
  - assert (Hd_pos : 0 < d).
    { destruct (Qlt_le_dec 0 d) as [Hp|Hn]; [exact Hp|].
      exfalso. assert (Hd0 : d == 0) by lra.
      assert (Hdc_le : d * c <= 0) by (setoid_rewrite Hd0; lra). lra. }
    assert (Hc_pos : 0 < c).
    { destruct (Qlt_le_dec 0 c) as [Hp|Hn]; [exact Hp|].
      exfalso. assert (Hc00 : c == 0) by lra.
      assert (Hdc_le : d * c <= 0) by (setoid_rewrite Hc00; lra). lra. }
    destruct (Qpow_vanish c (eps / d) Hc_pos Hc1) as [N HN].
    { unfold Qdiv. apply Qmult_lt_0_compat;
        [lra | apply Qinv_lt_0_compat; lra]. }
    exists N. intros n Hn.
    assert (Hstep := iterate_step_shrink f a b c x Hc_copy Hxa Hxb n).
    fold d in Hstep.
    change (iterate f x (S n)) with (f (iterate f x n)) in Hstep.
    assert (Hcn_le : Qpow c n <= Qpow c N)
      by (apply qpow_le_mono; [exact Hc0 | lra | exact Hn]).
    assert (Hdc_le : Qpow c n * d <= Qpow c N * d).
    { apply Qmult_le_compat_r; [exact Hcn_le | exact Hd_nn]. }
    assert (HcN_bound : Qpow c N * d < eps).
    { assert (Hmul : Qpow c N * d < eps / d * d).
      { apply Qmult_lt_compat_r; [exact Hd_pos | exact HN]. }
      assert (Hsimp : eps / d * d == eps) by (field; lra).
      lra. }
    lra.
  - (* d*c <= 0 => d*c = 0 *)
    assert (Hdc_nn : 0 <= d * c).
    { apply Qmult_le_0_compat; [exact Hd_nn | exact Hc0]. }
    assert (Hdc0 : d * c == 0) by lra.
    exists 1%nat. intros n Hn.
    assert (Hstep := iterate_step_shrink f a b c x Hc_copy Hxa Hxb n).
    fold d in Hstep.
    change (iterate f x (S n)) with (f (iterate f x n)) in Hstep.
    assert (Hcn_le : Qpow c n <= Qpow c 1)
      by (apply qpow_le_mono; [exact Hc0 | lra | exact Hn]).
    simpl in Hcn_le.
    assert (Hcn_bound : Qpow c n * d <= (c * 1) * d).
    { apply Qmult_le_compat_r; [lra | exact Hd_nn]. }
    assert (Hsimp : (c * 1) * d == d * c) by ring.
    assert (Hcn0 : Qpow c n * d <= 0) by lra.
    assert (Hcn_nn : 0 <= Qpow c n * d).
    { apply Qmult_le_0_compat; [apply Qpow_nonneg; exact Hc0 | exact Hd_nn]. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: UNIQUENESS AND BOUNDS                                         *)
(* ========================================================================= *)

(** 12. Different starting points give close iterates *)
Lemma fixed_point_independent : forall f a b c x y,
  is_contraction f a b c ->
  a <= x -> x <= b -> a <= y -> y <= b ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (iterate f x n - iterate f y n) < eps.
Proof.
  intros f a b c x y Hc Hxa Hxb Hya Hyb eps Heps.
  assert (Hc_copy := Hc).
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  set (e := Qabs (x - y)).
  assert (He_nn : 0 <= e) by (unfold e; apply Qabs_nonneg).
  (* |f^n(x) - f^n(y)| <= c^n * |x - y| by iterate_contraction *)
  (* Need c^n * e < eps *)
  destruct (Qlt_le_dec 0 (e * c)) as [Hec_pos | Hec_zero].
  - assert (He_pos : 0 < e).
    { destruct (Qlt_le_dec 0 e) as [Hp|Hn]; [exact Hp|].
      exfalso. assert (He0 : e == 0) by lra.
      assert (Hec_le : e * c <= 0) by (setoid_rewrite He0; lra). lra. }
    assert (Hc_pos : 0 < c).
    { destruct (Qlt_le_dec 0 c) as [Hp|Hn]; [exact Hp|].
      exfalso. assert (Hc00 : c == 0) by lra.
      assert (Hec_le : e * c <= 0) by (setoid_rewrite Hc00; lra). lra. }
    destruct (Qpow_vanish c (eps / e) Hc_pos Hc1) as [N HN].
    { unfold Qdiv. apply Qmult_lt_0_compat;
        [lra | apply Qinv_lt_0_compat; lra]. }
    exists N. intros n Hn.
    assert (Hic := iterate_contraction f a b c Hc_copy x y Hxa Hxb Hya Hyb n).
    fold e in Hic.
    assert (Hcn_le : Qpow c n <= Qpow c N)
      by (apply qpow_le_mono; [exact Hc0 | lra | exact Hn]).
    assert (Hce_le : Qpow c n * e <= Qpow c N * e).
    { apply Qmult_le_compat_r; [exact Hcn_le | exact He_nn]. }
    assert (HcN_bound : Qpow c N * e < eps).
    { assert (Hmul : Qpow c N * e < eps / e * e).
      { apply Qmult_lt_compat_r; [exact He_pos | exact HN]. }
      assert (Hsimp : eps / e * e == eps) by (field; lra).
      lra. }
    lra.
  - (* e*c <= 0 => e*c = 0 *)
    assert (Hec_nn : 0 <= e * c).
    { apply Qmult_le_0_compat; [exact He_nn | exact Hc0]. }
    assert (Hec0 : e * c == 0) by lra.
    exists 1%nat. intros n Hn.
    assert (Hic := iterate_contraction f a b c Hc_copy x y Hxa Hxb Hya Hyb n).
    fold e in Hic.
    assert (Hcn_le : Qpow c n <= Qpow c 1)
      by (apply qpow_le_mono; [exact Hc0 | lra | exact Hn]).
    simpl in Hcn_le.
    assert (Hcn_bound : Qpow c n * e <= (c * 1) * e).
    { apply Qmult_le_compat_r; [lra | exact He_nn]. }
    assert (Hsimp : (c * 1) * e == e * c) by ring.
    assert (Hcn0 : Qpow c n * e <= 0) by lra.
    assert (Hcn_nn : 0 <= Qpow c n * e).
    { apply Qmult_le_0_compat; [apply Qpow_nonneg; exact Hc0 | exact He_nn]. }
    lra.
Qed.

(** 13. Limit stays in [a,b] *)
Lemma contraction_limit_in_interval : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    a < iterate f x n + eps) /\
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    iterate f x n < b + eps).
Proof.
  intros f a b c x Hc Hxa Hxb.
  split; intros eps Heps; exists 0%nat; intros n _.
  - assert (Hin := iterate_in_interval f a b c x Hc Hxa Hxb n). lra.
  - assert (Hin := iterate_in_interval f a b c x Hc Hxa Hxb n). lra.
Qed.

(** 14. iterate_add: f^(m+n)(x) = f^m(f^n(x)) *)
Lemma iterate_add : forall f x m n,
  iterate f x (m + n) = iterate f (iterate f x n) m.
Proof.
  intros f x m n. induction m as [|m IHm].
  - simpl. reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 5: COMPOSITION AND STRUCTURAL PROPERTIES                         *)
(* ========================================================================= *)

(** 15. Composition of contractions is a contraction *)
Lemma contraction_compose : forall f g a b c1 c2,
  is_contraction f a b c1 ->
  is_contraction g a b c2 ->
  (forall x, a <= x -> x <= b -> a <= g x /\ g x <= b) ->
  is_contraction (fun x => f (g x)) a b (c1 * c2).
Proof.
  intros f g a b c1 c2
    [Hc10 [Hc11 [Hf_self Hf_contr]]]
    [Hc20 [Hc21 [Hg_self Hg_contr]]]
    Hg_maps.
  unfold is_contraction.
  split; [apply Qmult_le_0_compat; assumption |].
  split.
  { (* c1 * c2 < 1 *)
    assert (Hc2_bound : c2 <= 1) by lra.
    assert (H : c1 * c2 <= c1 * 1).
    { apply Qmult_le_compat_l; [exact Hc2_bound | exact Hc10]. }
    lra. }
  split.
  { (* self-map *)
    intros x Hxa Hxb.
    assert (Hgx := Hg_self x Hxa Hxb).
    apply Hf_self; [apply Hgx | apply Hgx]. }
  { (* contraction *)
    intros x y Hxa Hxb Hya Hyb.
    assert (Hgx := Hg_self x Hxa Hxb).
    assert (Hgy := Hg_self y Hya Hyb).
    assert (Hf_bound : Qabs (f (g x) - f (g y)) <= c1 * Qabs (g x - g y)).
    { apply Hf_contr; [apply Hgx | apply Hgx | apply Hgy | apply Hgy]. }
    assert (Hg_bound : Qabs (g x - g y) <= c2 * Qabs (x - y))
      by (apply Hg_contr; assumption).
    apply Qle_trans with (c1 * Qabs (g x - g y)); [exact Hf_bound |].
    apply Qle_trans with (c1 * (c2 * Qabs (x - y))).
    { apply Qmult_le_compat_l; [exact Hg_bound | exact Hc10]. }
    assert (Heq : c1 * (c2 * Qabs (x - y)) == c1 * c2 * Qabs (x - y)) by ring.
    lra. }
Qed.

(** 16. f^k is a contraction with factor c^k (k >= 1) *)
Lemma iterate_is_contraction : forall f a b c,
  is_contraction f a b c ->
  forall k, (1 <= k)%nat -> is_contraction (fun x => iterate f x k) a b (Qpow c k).
Proof.
  intros f a b c Hc k Hk.
  destruct Hc as [Hc0 [Hc1 [Hself Hcontr]]].
  assert (Hc_full : is_contraction f a b c)
    by (unfold is_contraction; auto).
  unfold is_contraction.
  split; [apply Qpow_nonneg; exact Hc0 |].
  split.
  { (* c^k < 1 for k >= 1 *)
    apply Qle_lt_trans with (Qpow c 1).
    - apply qpow_le_mono; [exact Hc0 | lra | exact Hk].
    - simpl. lra. }
  split.
  { (* self-map *)
    intros x Hxa Hxb.
    apply (iterate_in_interval f a b c x Hc_full Hxa Hxb k). }
  { (* contraction *)
    intros x y Hxa Hxb Hya Hyb.
    apply (iterate_contraction f a b c Hc_full x y Hxa Hxb Hya Hyb k). }
Qed.

(** 17. Monotone iterates: increasing f with f(x) >= x gives non-decreasing iterates *)
Lemma contraction_monotone_iterate : forall f a b c x,
  is_contraction f a b c ->
  a <= x -> x <= b ->
  (forall u v, a <= u -> u <= b -> a <= v -> v <= b -> u <= v -> f u <= f v) ->
  x <= f x ->
  forall n, iterate f x n <= iterate f x (S n).
Proof.
  intros f a b c x Hc Hxa Hxb Hmono Hxfx n.
  induction n as [|n IHn].
  - simpl. exact Hxfx.
  - simpl.
    assert (Hin_n := iterate_in_interval f a b c x Hc Hxa Hxb n).
    assert (Hin_sn := iterate_in_interval f a b c x Hc Hxa Hxb (S n)).
    apply Hmono; [apply Hin_n | apply Hin_n | apply Hin_sn | apply Hin_sn | exact IHn].
Qed.

(** Helper: recurrence for geometric partial sums *)
Lemma geometric_ps_recurrence : forall c n,
  c * partial_sum (fun k => Qpow c k) n + 1 ==
  Qpow c (S n) + partial_sum (fun k => Qpow c k) n.
Proof.
  intros c n.
  assert (Hgeo := geometric_sum_identity c n).
  set (p := partial_sum (fun k => Qpow c k) n) in *.
  set (q := Qpow c (S n)) in *.
  assert (Hgeo' : p - c * p == 1 - q).
  { setoid_replace (p - c * p) with ((1 - c) * p) by ring. exact Hgeo. }
  lra.
Qed.

(** 18. Perturbation: nearby contractions have nearby iterates *)
Lemma perturbed_iterate_bound : forall f g a b c x delta,
  is_contraction f a b c ->
  is_contraction g a b c ->
  a <= x -> x <= b ->
  (forall u, a <= u -> u <= b -> Qabs (f u - g u) <= delta) ->
  0 <= delta ->
  forall n, Qabs (iterate f x n - iterate g x n) <=
            delta * partial_sum (fun k => Qpow c k) (Nat.pred n).
Proof.
  intros f g a b c x delta Hcf Hcg Hxa Hxb Hclose Hdelta_nn.
  destruct Hcf as [Hc0 [Hc1 [Hf_self Hf_contr]]].
  assert (Hcf_full : is_contraction f a b c)
    by (unfold is_contraction; auto).
  destruct Hcg as [Hc0' [Hc1' [Hg_self Hg_contr]]].
  assert (Hcg_full : is_contraction g a b c)
    by (unfold is_contraction; auto).
  induction n as [|n IHn].
  - simpl iterate. simpl Nat.pred. simpl partial_sum. simpl Qpow.
    assert (Habs0 : Qabs (x - x) == 0).
    { assert (Hx0 : x - x == 0) by lra. rewrite (Qabs_wd _ _ Hx0). apply Qabs_pos. lra. }
    assert (Hlhs : Qabs (x - x) <= 0) by (apply Qeq_Qle; exact Habs0).
    lra.
  - destruct n as [|n'].
    + (* n = 0: |f(x) - g(x)| <= delta * ps(0) = delta *)
      simpl iterate. simpl Nat.pred. simpl partial_sum. simpl Qpow.
      setoid_replace (delta * 1) with delta by ring.
      exact (Hclose x Hxa Hxb).
    + (* n = S n': full bound chain *)
      change (iterate f x (S (S n'))) with (f (iterate f x (S n'))).
      change (iterate g x (S (S n'))) with (g (iterate g x (S n'))).
      simpl Nat.pred.
      assert (Hin_f := iterate_in_interval f a b c x Hcf_full Hxa Hxb (S n')).
      assert (Hin_g := iterate_in_interval g a b c x Hcg_full Hxa Hxb (S n')).
      assert (Htri : Qabs (f (iterate f x (S n')) - g (iterate g x (S n'))) <=
                     Qabs (f (iterate f x (S n')) - f (iterate g x (S n'))) +
                     Qabs (f (iterate g x (S n')) - g (iterate g x (S n')))).
      { setoid_replace (f (iterate f x (S n')) - g (iterate g x (S n'))) with
          ((f (iterate f x (S n')) - f (iterate g x (S n'))) +
           (f (iterate g x (S n')) - g (iterate g x (S n')))) by ring.
        apply Qabs_triangle. }
      assert (Hf_bound : Qabs (f (iterate f x (S n')) - f (iterate g x (S n'))) <=
                         c * Qabs (iterate f x (S n') - iterate g x (S n'))).
      { apply Hf_contr; [apply Hin_f | apply Hin_f | apply Hin_g | apply Hin_g]. }
      assert (Hg_bound : Qabs (f (iterate g x (S n')) - g (iterate g x (S n'))) <= delta).
      { apply Hclose; [apply Hin_g | apply Hin_g]. }
      assert (Hih : c * Qabs (iterate f x (S n') - iterate g x (S n')) <=
                    c * (delta * partial_sum (fun k => Qpow c k) n')).
      { apply Qmult_le_compat_l.
        - simpl Nat.pred in IHn. exact IHn.
        - exact Hc0. }
      (* Use geometric recurrence: c * ps(n') + 1 == c^(S n') + ps(n') *)
      assert (Hrec := geometric_ps_recurrence c n').
      (* Unfold ps(S n') = Qpow c (S n') + ps(n') *)
      assert (Hps_def : partial_sum (fun k : nat => Qpow c k) (S n') ==
                        Qpow c (S n') + partial_sum (fun k : nat => Qpow c k) n').
      { change (partial_sum (fun k : nat => Qpow c k) (S n'))
          with (partial_sum (fun k : nat => Qpow c k) n' +
                (fun k : nat => Qpow c k) (S n')).
        cbv beta. ring. }
      assert (Halg : c * (delta * partial_sum (fun k => Qpow c k) n') + delta ==
                      delta * partial_sum (fun k => Qpow c k) (S n')).
      { setoid_rewrite Hps_def.
        setoid_replace (c * (delta * partial_sum (fun k => Qpow c k) n') + delta)
          with (delta * (c * partial_sum (fun k => Qpow c k) n' + 1)) by ring.
        apply Qmult_comp. reflexivity. exact Hrec. }
      assert (Halg_le := Qeq_Qle _ _ Halg).
      lra.
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                              *)
(* ========================================================================= *)

Check iterate_in_interval.
Check iterate_shift.
Check iterate_contraction.
Check iterate_step_shrink.
Check qpow_le_mono.
Check Qabs_0.
Check contraction_unique_fixed.
Check iterate_diff_bound.
Check iterate_is_cauchy.
Check approximate_fixed_point.
Check fixed_point_independent.
Check contraction_limit_in_interval.
Check iterate_add.
Check contraction_compose.
Check iterate_is_contraction.
Check contraction_monotone_iterate.
Check perturbed_iterate_bound.

Print Assumptions iterate_in_interval.
Print Assumptions iterate_is_cauchy.
Print Assumptions banach_fixed_point.
Print Assumptions contraction_unique_fixed.
Print Assumptions fixed_point_independent.
Print Assumptions contraction_compose.
Print Assumptions iterate_is_contraction.
Print Assumptions contraction_monotone_iterate.
Print Assumptions perturbed_iterate_bound.
