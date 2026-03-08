(** * ImplicitFunction.v -- Implicit Function via Newton-Contraction

    Theory of Systems -- Analysis Gap Closure (Phase 0)

    Newton iteration g(x) = x - lambda * f(x) as contraction mapping.
    Uses damping factor lambda to avoid division.
    Applies Banach fixed point from FixedPoint.v.

    Elements: function f, damping lambda, iterates
    Roles:    f -> Target, lambda -> Damping, iterate -> Approximation
    Rules:    contraction (constitution), convergence rate (constraint)

    SIXTH application of Banach contraction in the repo!
    Previous: pipeline, Bellman, Picard, Nash, consensus.

    STATUS: 18 Qed, 0 Admitted, 0 axioms (uses classic transitively via FixedPoint)
    Author: Horsocrates | Date: March 2026
*)

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
From ToS Require Import FixedPoint.

Open Scope Q_scope.

(* ========================================================================= *)
(* LOCAL Q-ARITHMETIC HELPER                                                  *)
(* ========================================================================= *)

(** Left multiplication preserves <= *)
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

(** Newton step: g(x) = x - lambda * f(x) *)
Definition newton_step (f : Q -> Q) (lambda : Q) (x : Q) : Q :=
  x - lambda * f x.

(** Newton iterate: g^n(x0) *)
Definition newton_iterate (f : Q -> Q) (lambda : Q) (x0 : Q) (n : nat) : Q :=
  iterate (newton_step f lambda) x0 n.

(** Strong monotonicity: m*(y-x) <= f(y)-f(x) <= M*(y-x) for x <= y in [a,b] *)
Definition strongly_monotone (f : Q -> Q) (a b m M : Q) : Prop :=
  0 < m /\ m <= M /\
  (forall x y, a <= x -> x <= b -> a <= y -> y <= b -> x <= y ->
    m * (y - x) <= f y - f x /\ f y - f x <= M * (y - x)).

(* ========================================================================= *)
(* SECTION 1: FIXED POINT = ZERO (3 lemmas)                                  *)
(* ========================================================================= *)

(** 1. g(x) = x implies f(x) = 0 *)
Lemma newton_step_fixed_is_zero : forall f lambda x,
  ~ lambda == 0 ->
  newton_step f lambda x == x -> f x == 0.
Proof.
  intros f lam x Hlam Hfix.
  unfold newton_step in Hfix.
  assert (Hlf : lam * f x == 0) by lra.
  destruct (Qeq_dec (f x) 0) as [Heq | Hneq].
  - exact Heq.
  - exfalso. apply Hlam.
    destruct (Qeq_dec lam 0) as [Hl0 | Hl0].
    + exact Hl0.
    + exfalso. apply Hneq.
      assert (Hinv : / lam * (lam * f x) == / lam * 0).
      { apply Qmult_comp; [reflexivity | exact Hlf]. }
      assert (Hsimp : / lam * (lam * f x) == f x) by (field; exact Hl0).
      assert (Hsimp2 : / lam * 0 == 0) by ring.
      lra.
Qed.

(** 2. f(x) = 0 implies g(x) = x *)
Lemma newton_step_zero_is_fixed : forall f lambda x,
  f x == 0 -> newton_step f lambda x == x.
Proof.
  intros f lam x Hfx.
  unfold newton_step.
  assert (Hprod : lam * f x == lam * 0).
  { apply Qmult_comp; [reflexivity | exact Hfx]. }
  lra.
Qed.

(** 3. g(x) - g(y) = (x - y) - lambda*(f(x) - f(y)) *)
Lemma newton_step_diff : forall f lambda x y,
  newton_step f lambda x - newton_step f lambda y ==
  (x - y) - lambda * (f x - f y).
Proof.
  intros f lam x y.
  unfold newton_step. ring.
Qed.

(* ========================================================================= *)
(* SECTION 2: CONTRACTION ANALYSIS (6 lemmas)                                *)
(* ========================================================================= *)

(** 4. For x <= y with strong monotonicity, bound |g(x)-g(y)| *)
Lemma newton_contraction_ordered : forall f lambda m M x y d,
  0 < lambda ->
  0 < m -> m <= M ->
  d == y - x -> 0 <= d ->
  m * d <= f y - f x ->
  f y - f x <= M * d ->
  lambda * m <= 1 ->
  lambda * M <= 1 ->
  Qabs (newton_step f lambda x - newton_step f lambda y) <=
  Qmax (1 - lambda * m) (lambda * M - 1) * d.
Proof.
  intros f lam m0 M0 x y d Hlam Hm HmM Hd Hd_nn Hlo Hhi HlamM HlamM2.
  assert (Hdiff : newton_step f lam x - newton_step f lam y ==
                  -(d) + lam * (f y - f x)).
  { unfold newton_step. lra. }
  set (df := f y - f x).
  assert (Hlo2 : -d + lam * (m0 * d) <= -d + lam * df).
  { assert (H : lam * (m0 * d) <= lam * df).
    { apply Qmult_le_compat_l; [unfold df; lra | lra]. }
    lra. }
  assert (Hhi2 : -d + lam * df <= -d + lam * (M0 * d)).
  { assert (H : lam * df <= lam * (M0 * d)).
    { apply Qmult_le_compat_l; [unfold df; lra | lra]. }
    lra. }
  assert (Hval : newton_step f lam x - newton_step f lam y == -d + lam * df) by exact Hdiff.
  assert (Hrange_lo : (lam * m0 - 1) * d <= newton_step f lam x - newton_step f lam y).
  { assert (Halg : -d + lam * (m0 * d) == (lam * m0 - 1) * d) by ring. lra. }
  assert (Hrange_hi : newton_step f lam x - newton_step f lam y <= (lam * M0 - 1) * d).
  { assert (Halg : -d + lam * (M0 * d) == (lam * M0 - 1) * d) by ring. lra. }
  destruct (Q.max_spec (1 - lam * m0) (lam * M0 - 1)) as [[Hlt Hmax] | [Hle Hmax]].
  - rewrite Hmax.
    destruct (Qlt_le_dec 0 (newton_step f lam x - newton_step f lam y)) as [Hpos | Hneg].
    + rewrite Qabs_pos by lra.
      assert (H0 : 0 <= lam * M0 - 1) by lra. lra.
    + rewrite Qabs_neg by lra. lra.
  - rewrite Hmax.
    destruct (Qlt_le_dec 0 (newton_step f lam x - newton_step f lam y)) as [Hpos | Hneg].
    + assert (Habs_eq : Qabs (newton_step f lam x - newton_step f lam y) ==
                         newton_step f lam x - newton_step f lam y)
        by (apply Qabs_pos; lra).
      setoid_rewrite Habs_eq.
      assert (Hbridge : (lam * M0 - 1) * d <= (1 - lam * m0) * d).
      { apply Qmult_le_compat_r; lra. }
      lra.
    + assert (Habs_eq : Qabs (newton_step f lam x - newton_step f lam y) ==
                         -(newton_step f lam x - newton_step f lam y))
        by (apply Qabs_neg; lra).
      assert (Hfrom_lo : -(newton_step f lam x - newton_step f lam y) <=
                          (1 - lam * m0) * d).
      { assert (Hexp : (1 - lam * m0) * d == -((lam * m0 - 1) * d)) by ring. lra. }
      setoid_rewrite Habs_eq. lra.
Qed.

(** 5. Extend contraction bound to general x, y (symmetry) *)
Lemma newton_contraction_bound : forall f lambda a b m M,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
  Qabs (newton_step f lambda x - newton_step f lambda y) <=
  Qmax (1 - lambda * m) (lambda * M - 1) * Qabs (x - y).
Proof.
  intros f lam a b m0 M0 Hmon Hlam HlamM HlamM2 x y Hxa Hxb Hya Hyb.
  destruct Hmon as [Hm [HmM Hbounds]].
  destruct (Qlt_le_dec y x) as [Hyx | Hxy].
  - assert (Hxy' : y <= x) by lra.
    destruct (Hbounds y x Hya Hyb Hxa Hxb Hxy') as [Hlo Hhi].
    assert (Hsym : newton_step f lam x - newton_step f lam y ==
                   -(newton_step f lam y - newton_step f lam x)) by ring.
    assert (Habs_sym : Qabs (newton_step f lam x - newton_step f lam y) ==
                       Qabs (newton_step f lam y - newton_step f lam x)).
    { setoid_rewrite Hsym. apply Qabs_opp. }
    assert (Habs_xy : Qabs (x - y) == Qabs (y - x)).
    { setoid_replace (x - y) with (-(y - x)) by ring. apply Qabs_opp. }
    setoid_rewrite Habs_sym. setoid_rewrite Habs_xy.
    set (d := x - y).
    assert (Hd_nn : 0 <= d) by (unfold d; lra).
    assert (Habs_d : Qabs (y - x) == d).
    { assert (Hyx2 : y - x == -d) by (unfold d; ring).
      setoid_rewrite Hyx2. rewrite Qabs_opp. apply Qabs_pos. lra. }
    setoid_rewrite Habs_d.
    apply newton_contraction_ordered with (m := m0) (M := M0); try lra; try assumption.
    unfold d. lra.
  - destruct (Hbounds x y Hxa Hxb Hya Hyb Hxy) as [Hlo Hhi].
    set (d := y - x).
    assert (Hd_nn : 0 <= d) by (unfold d; lra).
    assert (Habs_d : Qabs (x - y) == d).
    { assert (Hxy2 : x - y == -d) by (unfold d; ring).
      setoid_rewrite Hxy2. rewrite Qabs_opp. apply Qabs_pos. lra. }
    setoid_rewrite Habs_d.
    apply newton_contraction_ordered with (m := m0) (M := M0); try lra; try assumption.
    unfold d. lra.
Qed.

(** 6. Contraction factor < 1 when lambda * M < 2 *)
Lemma contraction_factor_lt_1 : forall m M lambda,
  0 < m -> m <= M ->
  0 < lambda -> lambda * M < 2 ->
  Qmax (1 - lambda * m) (lambda * M - 1) < 1.
Proof.
  intros m0 M0 lam Hm HmM Hlam HlamM.
  destruct (Q.max_spec (1 - lam * m0) (lam * M0 - 1)) as [[Hlt Hmax] | [Hle Hmax]].
  - rewrite Hmax. lra.
  - rewrite Hmax.
    assert (H : 0 < lam * m0) by (apply Qmult_lt_0_compat; lra).
    lra.
Qed.

(** 7. Contraction factor is nonneg *)
Lemma contraction_factor_nonneg : forall m M lambda,
  0 < m -> m <= M ->
  0 < lambda -> lambda * m <= 1 ->
  0 <= Qmax (1 - lambda * m) (lambda * M - 1).
Proof.
  intros m0 M0 lam Hm HmM Hlam HlamM.
  destruct (Q.max_spec (1 - lam * m0) (lam * M0 - 1)) as [[Hlt Hmax] | [Hle Hmax]].
  - rewrite Hmax. lra.
  - rewrite Hmax. lra.
Qed.

(** 8. Strongly monotone implies Lipschitz *)
Lemma strongly_monotone_lipschitz : forall f a b m M,
  strongly_monotone f a b m M ->
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
  Qabs (f x - f y) <= M * Qabs (x - y).
Proof.
  intros f a b m0 M0 [Hm [HmM Hbounds]] x y Hxa Hxb Hya Hyb.
  destruct (Qlt_le_dec y x) as [Hyx | Hxy].
  - assert (Hxy' : y <= x) by lra.
    destruct (Hbounds y x Hya Hyb Hxa Hxb Hxy') as [Hlo Hhi].
    assert (Habs_xy : Qabs (x - y) == x - y) by (apply Qabs_pos; lra).
    setoid_rewrite Habs_xy.
    destruct (Qlt_le_dec 0 (f x - f y)) as [Hp | Hn].
    + rewrite Qabs_pos by lra. lra.
    + rewrite Qabs_neg by exact Hn.
      assert (HM_nn : 0 <= M0) by lra.
      assert (Hd_nn : 0 <= x - y) by lra.
      assert (Hm_prod : 0 <= m0 * (x - y)) by (apply Qmult_le_0_compat; lra).
      assert (HM_prod : 0 <= M0 * (x - y)) by (apply Qmult_le_0_compat; lra).
      lra.
  - destruct (Hbounds x y Hxa Hxb Hya Hyb Hxy) as [Hlo Hhi].
    assert (Habs_xy : Qabs (x - y) == y - x).
    { setoid_replace (x - y) with (-(y - x)) by ring.
      rewrite Qabs_opp. apply Qabs_pos. lra. }
    setoid_rewrite Habs_xy.
    assert (Hfx_le : f x - f y <= 0).
    { assert (H0 : 0 <= m0 * (y - x)) by (apply Qmult_le_0_compat; lra). lra. }
    assert (Heq : f x - f y == -(f y - f x)) by ring.
    setoid_rewrite Heq. rewrite Qabs_opp.
    assert (Hfy_nn : 0 <= f y - f x).
    { assert (H0 : 0 <= m0 * (y - x)) by (apply Qmult_le_0_compat; lra). lra. }
    rewrite Qabs_pos by lra. lra.
Qed.

(** 9. Newton step maps [a,b] to [a,b] under conditions *)
Lemma newton_self_map : forall f lambda a b m M,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  f a <= 0 -> 0 <= f b ->
  forall x, a <= x -> x <= b ->
  a <= newton_step f lambda x /\ newton_step f lambda x <= b.
Proof.
  intros f lam a b m0 M0 Hmon Hlam HlamM HlamM2 Hfa Hfb x Hxa Hxb.
  destruct Hmon as [Hm [HmM Hbounds]].
  unfold newton_step.
  split.
  - (* a <= x - lam * f(x) *)
    assert (Hab : a <= b) by lra.
    destruct (Hbounds a x (Qle_refl a) Hab Hxa Hxb Hxa) as [Hlo_a Hhi_a].
    (* f(x) - f(a) <= M0*(x-a), f(a) <= 0, so f(x) <= M0*(x-a) *)
    assert (Hfx_bound : f x <= M0 * (x - a)) by lra.
    assert (Hlam_bound : lam * f x <= lam * (M0 * (x - a))).
    { destruct (Qlt_le_dec 0 (f x)) as [Hfpos | Hfneg].
      - apply Qmult_le_compat_l; lra.
      - assert (Hneg : lam * f x <= 0).
        { assert (H : lam * f x <= lam * 0) by (apply Qmult_le_compat_l; lra). lra. }
        assert (Hpos : 0 <= lam * (M0 * (x - a))).
        { apply Qmult_le_0_compat; [lra|]. apply Qmult_le_0_compat; lra. }
        lra. }
    assert (Halg : x - lam * (M0 * (x - a)) == a + (x - a) * (1 - lam * M0)) by ring.
    assert (Hge : 0 <= (x - a) * (1 - lam * M0)).
    { apply Qmult_le_0_compat; lra. }
    lra.
  - (* x - lam * f(x) <= b *)
    assert (Hab : a <= b) by lra.
    destruct (Hbounds x b Hxa Hxb Hab (Qle_refl b) Hxb) as [Hlo_b Hhi_b].
    (* f(b) - f(x) <= M0*(b-x), f(b) >= 0, so -f(x) <= M0*(b-x) - f(b) <= M0*(b-x) *)
    assert (Hfx_lo : f x >= - M0 * (b - x)).
    { assert (H : f x >= f b - M0 * (b - x)) by lra. lra. }
    assert (Hlam_lo : lam * f x >= lam * (- M0 * (b - x))).
    { destruct (Qlt_le_dec (f x) 0) as [Hfneg | Hfpos].
      - assert (Hfx_neg : - M0 * (b - x) <= f x) by lra.
        assert (H : lam * (- M0 * (b - x)) <= lam * f x).
        { apply Qmult_le_compat_l; lra. }
        lra.
      - assert (H0 : 0 <= lam * f x) by (apply Qmult_le_0_compat; lra).
        assert (Hneg : lam * (- M0 * (b - x)) <= 0).
        { assert (Hval : - M0 * (b - x) <= 0).
          { assert (HM_nn : 0 <= M0) by lra.
            assert (Hbx : 0 <= b - x) by lra.
            assert (H : 0 <= M0 * (b - x)) by (apply Qmult_le_0_compat; assumption).
            lra. }
          assert (H : lam * (- M0 * (b - x)) <= lam * 0) by (apply Qmult_le_compat_l; lra).
          lra. }
        lra. }
    assert (Halg : x - lam * (- M0 * (b - x)) == b - (b - x) * (1 - lam * M0)) by ring.
    assert (Hge : 0 <= (b - x) * (1 - lam * M0)).
    { apply Qmult_le_0_compat; lra. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: CONTRACTION + CONVERGENCE (5 lemmas)                           *)
(* ========================================================================= *)

(** 10. Newton is a contraction on [a,b] *)
Lemma newton_is_contraction : forall f lambda a b m M,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  f a <= 0 -> 0 <= f b ->
  is_contraction (newton_step f lambda) a b (Qmax (1 - lambda * m) (lambda * M - 1)).
Proof.
  intros f lam a b m0 M0 Hmon Hlam HlamM HlamM2 Hfa Hfb.
  assert (Hm := proj1 Hmon).
  assert (HmM := proj1 (proj2 Hmon)).
  unfold is_contraction.
  split.
  - apply contraction_factor_nonneg; try lra.
  - split.
    + apply contraction_factor_lt_1; lra.
    + split.
      * intros x Hxa Hxb.
        apply newton_self_map with (m := m0) (M := M0);
          [exact Hmon | exact Hlam | exact HlamM | exact HlamM2 | exact Hfa | exact Hfb | exact Hxa | exact Hxb].
      * intros x y Hxa Hxb Hya Hyb.
        apply newton_contraction_bound with (a := a) (b := b) (m := m0) (M := M0);
          [exact Hmon | exact Hlam | exact HlamM | exact HlamM2 | exact Hxa | exact Hxb | exact Hya | exact Hyb].
Qed.

(** 11. Newton iterates form a Cauchy sequence *)
Lemma newton_converges : forall f lambda a b m M x0,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  f a <= 0 -> 0 <= f b ->
  a <= x0 -> x0 <= b ->
  is_cauchy (fun n => newton_iterate f lambda x0 n).
Proof.
  intros f lam a b m0 M0 x0 Hmon Hlam HlamM HlamM2 Hfa Hfb Hx0a Hx0b.
  unfold newton_iterate.
  apply iterate_is_cauchy with a b (Qmax (1 - lam * m0) (lam * M0 - 1)).
  - apply (newton_is_contraction f lam a b m0 M0); assumption.
  - exact Hx0a.
  - exact Hx0b.
Qed.

(** 12. Newton iterates converge to approximate zero *)
Lemma newton_limit_is_zero : forall f lambda a b m M x0,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  f a <= 0 -> 0 <= f b ->
  a <= x0 -> x0 <= b ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (f (newton_iterate f lambda x0 n)) < eps.
Proof.
  intros f lam a b m0 M0 x0 Hmon Hlam HlamM HlamM2 Hfa Hfb Hx0a Hx0b eps Heps.
  assert (Hc : is_contraction (newton_step f lam) a b
    (Qmax (1 - lam * m0) (lam * M0 - 1))).
  { apply (newton_is_contraction f lam a b m0 M0); assumption. }
  assert (Heps' : 0 < eps * lam).
  { apply Qmult_lt_0_compat; assumption. }
  destruct (approximate_fixed_point (newton_step f lam) a b
    (Qmax (1 - lam * m0) (lam * M0 - 1)) x0 Hc Hx0a Hx0b (eps * lam) Heps') as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* HN : |g(x_n) - x_n| < eps * lam, where g = newton_step f lam *)
  unfold newton_iterate.
  set (xn := iterate (newton_step f lam) x0 n) in *.
  (* g(xn) - xn = -lam * f(xn) *)
  assert (Hrel : newton_step f lam xn - xn == - lam * f xn).
  { unfold newton_step. ring. }
  (* |g(xn) - xn| == lam * |f(xn)| *)
  assert (Habs_rel : Qabs (newton_step f lam xn - xn) == lam * Qabs (f xn)).
  { setoid_rewrite Hrel.
    setoid_replace (- lam * f xn) with (-(lam * f xn)) by ring.
    rewrite Qabs_opp.
    destruct (Qlt_le_dec 0 (f xn)) as [Hfp | Hfn].
    - assert (Habs_fxn : Qabs (f xn) == f xn) by (apply Qabs_pos; lra).
      assert (Hprod_nn : 0 <= lam * f xn) by (apply Qmult_le_0_compat; lra).
      assert (Habs_prod : Qabs (lam * f xn) == lam * f xn) by (apply Qabs_pos; lra).
      setoid_rewrite Habs_fxn. setoid_rewrite Habs_prod. ring.
    - assert (Habs_fxn : Qabs (f xn) == -(f xn)) by (apply Qabs_neg; lra).
      assert (Hn0 : lam * f xn <= 0).
      { assert (H : lam * f xn <= lam * 0) by (apply Qmult_le_compat_l; lra). lra. }
      assert (Habs_prod : Qabs (lam * f xn) == -(lam * f xn)) by (apply Qabs_neg; lra).
      setoid_rewrite Habs_fxn. setoid_rewrite Habs_prod. ring. }
  (* lam * |f(xn)| < eps * lam *)
  assert (Hlam_abs : lam * Qabs (f xn) < eps * lam) by lra.
  (* Divide both sides by lam *)
  assert (Hgt : lam * Qabs (f xn) * / lam < eps * lam * / lam).
  { apply Qmult_lt_compat_r; [apply Qinv_lt_0_compat; assumption | exact Hlam_abs]. }
  assert (Hsimp1 : lam * Qabs (f xn) * / lam == Qabs (f xn)) by (field; lra).
  assert (Hsimp2 : eps * lam * / lam == eps) by (field; lra).
  lra.
Qed.

(** 13. Strongly monotone implies injective *)
Lemma strongly_monotone_injective : forall f a b m M,
  strongly_monotone f a b m M ->
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
  f x == f y -> x == y.
Proof.
  intros f a b m0 M0 [Hm [HmM Hbounds]] x y Hxa Hxb Hya Hyb Hfxy.
  destruct (Qlt_le_dec x y) as [Hlt | Hge].
  - assert (Hxy : x <= y) by lra.
    destruct (Hbounds x y Hxa Hxb Hya Hyb Hxy) as [Hlo _].
    assert (Hpos : 0 < m0 * (y - x)) by (apply Qmult_lt_0_compat; lra).
    lra.
  - destruct (Qlt_le_dec y x) as [Hlt2 | Hge2].
    + assert (Hyx : y <= x) by lra.
      destruct (Hbounds y x Hya Hyb Hxa Hxb Hyx) as [Hlo _].
      assert (Hpos : 0 < m0 * (x - y)) by (apply Qmult_lt_0_compat; lra).
      lra.
    + lra.
Qed.

(** 14. Unique zero: strongly monotone f has at most one zero in [a,b] *)
Lemma newton_unique_zero : forall f a b m M,
  strongly_monotone f a b m M ->
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
  f x == 0 -> f y == 0 -> x == y.
Proof.
  intros f a b m0 M0 Hmon x y Hxa Hxb Hya Hyb Hfx Hfy.
  apply (strongly_monotone_injective f a b m0 M0 Hmon); try assumption.
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: CONVERGENCE RATE + INTERVAL (2 lemmas)                         *)
(* ========================================================================= *)

(** 15. Convergence rate: |x_{n+1} - x_n| <= c^n * |x_1 - x_0| *)
Lemma newton_convergence_rate : forall f lambda a b m M x0,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  f a <= 0 -> 0 <= f b ->
  a <= x0 -> x0 <= b ->
  forall n,
  Qabs (newton_iterate f lambda x0 (S n) - newton_iterate f lambda x0 n) <=
  Qpow (Qmax (1 - lambda * m) (lambda * M - 1)) n *
  Qabs (newton_step f lambda x0 - x0).
Proof.
  intros f lam a b m0 M0 x0 Hmon Hlam HlamM HlamM2 Hfa Hfb Hx0a Hx0b n.
  unfold newton_iterate.
  apply (iterate_step_shrink _ a b).
  - apply (newton_is_contraction f lam a b m0 M0); assumption.
  - exact Hx0a.
  - exact Hx0b.
Qed.

(** 16. Newton iterates stay in [a,b] *)
Lemma newton_iterate_in_interval : forall f lambda a b m M x0,
  strongly_monotone f a b m M ->
  0 < lambda -> lambda * m <= 1 -> lambda * M <= 1 ->
  f a <= 0 -> 0 <= f b ->
  a <= x0 -> x0 <= b ->
  forall n, a <= newton_iterate f lambda x0 n /\ newton_iterate f lambda x0 n <= b.
Proof.
  intros f lam a b m0 M0 x0 Hmon Hlam HlamM HlamM2 Hfa Hfb Hx0a Hx0b n.
  unfold newton_iterate.
  apply iterate_in_interval with (Qmax (1 - lam * m0) (lam * M0 - 1)).
  - apply (newton_is_contraction f lam a b m0 M0); assumption.
  - exact Hx0a.
  - exact Hx0b.
Qed.

(* ========================================================================= *)
(* SECTION 5: OPTIMAL PARAMETERS (3 lemmas)                                  *)
(* ========================================================================= *)

(** 17. Optimal lambda: 1 - (2/(m+M))*m = (M-m)/(m+M) *)
Lemma optimal_lambda_factor : forall m M,
  0 < m -> m <= M ->
  1 - (2 / (m + M)) * m == (M - m) / (m + M).
Proof.
  intros m0 M0 Hm HmM.
  field. lra.
Qed.

(** 18. Optimal factor < 1 *)
Lemma optimal_factor_lt_1 : forall m M,
  0 < m -> m <= M ->
  (M - m) / (m + M) < 1.
Proof.
  intros m0 M0 Hm HmM.
  assert (HmM_pos : 0 < m0 + M0) by lra.
  unfold Qdiv.
  assert (Hinv_pos : 0 < / (m0 + M0)) by (apply Qinv_lt_0_compat; lra).
  assert (Hlt : M0 - m0 < m0 + M0) by lra.
  assert (H1 : 1 == (m0 + M0) * / (m0 + M0)) by (field; lra).
  setoid_rewrite H1.
  apply Qmult_lt_compat_r; [exact Hinv_pos | exact Hlt].
Qed.

(** 19. Optimal factor is nonneg *)
Lemma optimal_factor_nonneg : forall m M,
  0 < m -> m <= M ->
  0 <= (M - m) / (m + M).
Proof.
  intros m0 M0 Hm HmM.
  assert (HmM_pos : 0 < m0 + M0) by lra.
  unfold Qdiv.
  apply Qmult_le_0_compat.
  - lra.
  - assert (H : 0 < / (m0 + M0)) by (apply Qinv_lt_0_compat; exact HmM_pos). lra.
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                              *)
(* ========================================================================= *)

Check newton_step_fixed_is_zero.   (* 1 *)
Check newton_step_zero_is_fixed.   (* 2 *)
Check newton_step_diff.            (* 3 *)
Check newton_contraction_ordered.  (* 4 *)
Check newton_contraction_bound.    (* 5 *)
Check contraction_factor_lt_1.     (* 6 *)
Check contraction_factor_nonneg.   (* 7 *)
Check strongly_monotone_lipschitz. (* 8 *)
Check newton_self_map.             (* 9 *)
Check newton_is_contraction.       (* 10 *)
Check newton_converges.            (* 11 *)
Check newton_limit_is_zero.        (* 12 *)
Check strongly_monotone_injective. (* 13 *)
Check newton_unique_zero.          (* 14 *)
Check newton_convergence_rate.     (* 15 *)
Check newton_iterate_in_interval.  (* 16 *)
Check optimal_lambda_factor.       (* 17 *)
Check optimal_factor_lt_1.         (* 18 *)
Check optimal_factor_nonneg.       (* 19 *)

Print Assumptions newton_is_contraction.
Print Assumptions newton_converges.
Print Assumptions newton_limit_is_zero.
Print Assumptions newton_convergence_rate.
