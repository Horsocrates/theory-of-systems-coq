(* ========================================================================= *)
(*         DIFFERENTIATION — DIVISION-FREE DERIVATIVES & POWER RULE         *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Formalize derivatives for Q-valued functions using the         *)
(*    division-free o(h) definition:                                        *)
(*      |f(x+h) - f(x) - L*h| < eps * |h|                                 *)
(*    Prove derivative rules, product rule, power rule by induction,        *)
(*    and connect to gradient descent on quadratic loss.                    *)
(*                                                                          *)
(*  AXIOMS: none (fully constructive)                                       *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import GradientDescent.

Open Scope Q_scope.

(* ========================================================================= *)
(* DEFINITIONS                                                                *)
(* ========================================================================= *)

(** Division-free derivative: |f(x+h) - f(x) - L*h| < eps * |h| *)
Definition has_derivative (f : Q -> Q) (x L : Q) : Prop :=
  forall eps : Q, 0 < eps ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x - L * h) < eps * Qabs h.

(** Continuity at a point (requires h nonzero -- Q functions don't respect Qeq) *)
Definition continuous_at (f : Q -> Q) (x : Q) : Prop :=
  forall eps : Q, 0 < eps ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x) < eps.

(** Local minimum *)
Definition local_min (f : Q -> Q) (x : Q) : Prop :=
  exists delta : Q, 0 < delta /\
  forall h : Q, Qabs h < delta -> f x <= f (x + h).

(* ========================================================================= *)
(* SECTION 1: EXTENSIONALITY AND BASICS                                       *)
(* ========================================================================= *)

(** Extensional equality of functions preserves derivative *)
Lemma has_derivative_ext : forall (f g : Q -> Q) (x L : Q),
  (forall w, f w == g w) -> has_derivative f x L -> has_derivative g x L.
Proof.
  intros f g x L Hext Hf eps Heps.
  destruct (Hf eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  assert (Heq : g (x + h) - g x - L * h == f (x + h) - f x - L * h).
  { assert (Hg1 := Hext (x + h)). assert (Hg2 := Hext x). lra. }
  qabs_rw Heq. exact (Hbound h Hh_pos Hh_lt).
Qed.

(** Qeq on derivative value *)
Lemma has_derivative_eq : forall (f : Q -> Q) (x L L' : Q),
  L == L' -> has_derivative f x L -> has_derivative f x L'.
Proof.
  intros f x L L' HLL' Hf eps Heps.
  destruct (Hf eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  assert (Heq : f (x + h) - f x - L' * h == f (x + h) - f x - L * h).
  { assert (HLh : L' * h == L * h).
    { apply Qmult_comp; [symmetry; exact HLL' | reflexivity]. }
    lra. }
  qabs_rw Heq. exact (Hbound h Hh_pos Hh_lt).
Qed.

(** Derivative of constant function *)
Lemma deriv_const : forall (c x : Q), has_derivative (fun _ => c) x 0.
Proof.
  intros c x eps Heps.
  exists 1. split; [lra |].
  intros h Hh_pos Hh_lt.
  assert (Heq : c - c - 0 * h == 0) by ring.
  qabs_rw Heq. rewrite Qabs_pos; [| lra].
  apply Qmult_lt_0_compat; lra.
Qed.

(** Derivative of identity function *)
Lemma deriv_id : forall (x : Q), has_derivative (fun w => w) x 1.
Proof.
  intros x eps Heps.
  exists 1. split; [lra |].
  intros h Hh_pos Hh_lt.
  assert (Heq : (x + h) - x - 1 * h == 0) by ring.
  qabs_rw Heq. rewrite Qabs_pos; [| lra].
  apply Qmult_lt_0_compat; lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: LINEARITY                                                       *)
(* ========================================================================= *)

(** Derivative of scalar multiple *)
Lemma deriv_scale : forall (f : Q -> Q) (x L c : Q),
  has_derivative f x L -> has_derivative (fun w => c * f w) x (c * L).
Proof.
  intros f x L c Hf eps Heps.
  destruct (Qeq_dec c 0) as [Hc0 | Hcnz].
  - (* c == 0: error is 0 *)
    exists 1. split; [lra |].
    intros h Hh_pos Hh_lt.
    assert (Heq : c * f (x + h) - c * f x - c * L * h == 0).
    { transitivity (0 * f (x + h) - 0 * f x - 0 * L * h).
      - apply Qplus_comp; [apply Qplus_comp; [| ]|]; try (apply Qopp_comp);
        repeat (apply Qmult_comp; try exact Hc0; try reflexivity).
      - ring. }
    qabs_rw Heq. rewrite Qabs_pos; [| lra].
    apply Qmult_lt_0_compat; lra.
  - (* c /= 0 *)
    assert (Hc_pos : 0 < Qabs c).
    { destruct (Qlt_le_dec c 0).
      - rewrite Qabs_neg; lra.
      - rewrite Qabs_pos; [|lra].
        destruct (Qlt_le_dec 0 c); [lra | exfalso; apply Hcnz; lra]. }
    assert (Heps' : 0 < eps * / Qabs c).
    { apply Qmult_lt_0_compat; [exact Heps | apply Qinv_lt_0_compat; exact Hc_pos]. }
    destruct (Hf (eps * / Qabs c) Heps') as [delta [Hdelta Hbound]].
    exists delta. split; [exact Hdelta |].
    intros h Hh_pos Hh_lt.
    assert (Heq : c * f (x + h) - c * f x - c * L * h ==
                   c * (f (x + h) - f x - L * h)) by ring.
    qabs_rw Heq. rewrite Qabs_Qmult.
    specialize (Hbound h Hh_pos Hh_lt).
    assert (H1 : Qabs (f (x + h) - f x - L * h) * Qabs c <
                  eps * / Qabs c * Qabs h * Qabs c).
    { apply Qmult_lt_compat_r; [exact Hc_pos | exact Hbound]. }
    assert (H2 : eps * / Qabs c * Qabs h * Qabs c == eps * Qabs h).
    { field. lra. }
    lra.
Qed.

(** Derivative of negation *)
Lemma deriv_neg : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L -> has_derivative (fun w => - f w) x (- L).
Proof.
  intros f x L Hf eps Heps.
  destruct (Hf eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  assert (Heq : - f (x + h) - - f x - - L * h ==
                 - (f (x + h) - f x - L * h)) by ring.
  qabs_rw Heq. rewrite Qabs_opp. exact (Hbound h Hh_pos Hh_lt).
Qed.

(** Derivative of sum *)
Lemma deriv_sum : forall (f g : Q -> Q) (x Lf Lg : Q),
  has_derivative f x Lf -> has_derivative g x Lg ->
  has_derivative (fun w => f w + g w) x (Lf + Lg).
Proof.
  intros f g x Lf Lg Hf Hg eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hf (eps * (1#2)) Heps2) as [df [Hdf Hbf]].
  destruct (Hg (eps * (1#2)) Heps2) as [dg [Hdg Hbg]].
  exists (Qmin df dg). split.
  - destruct (Q.min_spec df dg) as [[_ ->] | [_ ->]]; lra.
  - intros h Hh_pos Hh_lt.
    assert (Hh_df : Qabs h < df).
    { assert (Hmin := Q.le_min_l df dg). lra. }
    assert (Hh_dg : Qabs h < dg).
    { assert (Hmin := Q.le_min_r df dg). lra. }
    assert (Heq : (f (x + h) + g (x + h)) - (f x + g x) - (Lf + Lg) * h ==
                   (f (x + h) - f x - Lf * h) + (g (x + h) - g x - Lg * h)) by ring.
    qabs_rw Heq.
    assert (Htri := Qabs_triangle (f (x + h) - f x - Lf * h)
                                   (g (x + h) - g x - Lg * h)).
    specialize (Hbf h Hh_pos Hh_df).
    specialize (Hbg h Hh_pos Hh_dg).
    lra.
Qed.

(** Derivative of subtraction *)
Lemma deriv_sub : forall (f g : Q -> Q) (x Lf Lg : Q),
  has_derivative f x Lf -> has_derivative g x Lg ->
  has_derivative (fun w => f w - g w) x (Lf - Lg).
Proof.
  intros f g x Lf Lg Hf Hg.
  assert (Hng := deriv_neg g x Lg Hg).
  assert (Hsum := deriv_sum f (fun w => - g w) x Lf (-Lg) Hf Hng).
  apply (has_derivative_ext (fun w => f w + - g w)).
  - intros w. ring.
  - apply (has_derivative_eq (fun w => f w + - g w) x (Lf + - Lg)).
    + ring.
    + exact Hsum.
Qed.

(* ========================================================================= *)
(* SECTION 3: CONTINUITY                                                      *)
(* ========================================================================= *)

(** Differentiable implies continuous *)
Lemma deriv_implies_continuous : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L -> continuous_at f x.
Proof.
  intros f x L Hf eps Heps.
  (* Get delta from derivative with eps_d = 1 *)
  destruct (Hf 1 ltac:(lra)) as [delta_d [Hdd Hbd]].
  (* Take delta = min(delta_d, eps / (|L| + 1)) *)
  assert (HLp : 0 < Qabs L + 1).
  { assert (H := Qabs_nonneg L). lra. }
  set (delta2 := eps * / (Qabs L + 1)).
  assert (Hd2 : 0 < delta2).
  { unfold delta2. apply Qmult_lt_0_compat; [exact Heps | apply Qinv_lt_0_compat; exact HLp]. }
  exists (Qmin delta_d delta2). split.
  - destruct (Q.min_spec delta_d delta2) as [[_ ->] | [_ ->]]; lra.
  - intros h Hh_pos Hh_lt.
    assert (Hh_dd : Qabs h < delta_d).
    { assert (Hmin := Q.le_min_l delta_d delta2). lra. }
    assert (Hh_d2 : Qabs h < delta2).
    { assert (Hmin := Q.le_min_r delta_d delta2). lra. }
    (* |f(x+h) - f(x)| = |f(x+h) - f(x) - L*h + L*h| *)
    assert (Heq : f (x + h) - f x == (f (x + h) - f x - L * h) + L * h) by ring.
    qabs_rw Heq.
    assert (Htri := Qabs_triangle (f (x + h) - f x - L * h) (L * h)).
    specialize (Hbd h Hh_pos Hh_dd).
    rewrite Qabs_Qmult in Htri.
    (* |err| < 1 * |h| = |h|, |L*h| = |L|*|h| *)
    (* Total <= |err| + |L|*|h| < |h| + |L|*|h| = (1 + |L|) * |h| *)
    (* And (1 + |L|) * |h| < (|L| + 1) * delta2 = eps *)
    assert (Hmul : 0 < (Qabs L + 1) * (delta2 - Qabs h)).
    { apply Qmult_lt_0_compat; [exact HLp | lra]. }
    assert (Hcancel : (Qabs L + 1) * delta2 == eps).
    { unfold delta2. field. lra. }
    lra.
Qed.

(** Continuous function is bounded near x *)
Lemma continuous_bounded_near : forall (f : Q -> Q) (x : Q),
  continuous_at f x ->
  exists M delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h)) <= M.
Proof.
  intros f x Hcont.
  destruct (Hcont 1 ltac:(lra)) as [delta [Hdelta Hbound]].
  exists (Qabs (f x) + 1), delta.
  split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  specialize (Hbound h Hh_pos Hh_lt).
  (* |f(x+h)| = |(f(x+h) - f(x)) + f(x)| <= |f(x+h) - f(x)| + |f(x)| *)
  assert (Heq : f (x + h) == (f (x + h) - f x) + f x) by ring.
  assert (Habs_eq := Qabs_wd _ _ Heq).
  assert (Htri := Qabs_triangle (f (x + h) - f x) (f x)).
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: PRODUCT AND POWER RULE                                          *)
(* ========================================================================= *)

(** Derivative of x^2 -- direct proof *)
Lemma deriv_square : forall (x : Q),
  has_derivative (fun w => w * w) x (2 * x).
Proof.
  intros x eps Heps.
  exists eps. split; [exact Heps |].
  intros h Hh_pos Hh_lt.
  assert (Heq : (x + h) * (x + h) - x * x - 2 * x * h == h * h) by ring.
  qabs_rw Heq.
  rewrite Qabs_Qmult.
  (* |h| * |h| < eps * |h| since |h| < eps *)
  apply Qmult_lt_compat_r; [exact Hh_pos | exact Hh_lt].
Qed.

(** Product rule: (fg)' = f'g + fg' *)
Lemma deriv_product : forall (f g : Q -> Q) (x Lf Lg : Q),
  has_derivative f x Lf -> has_derivative g x Lg ->
  has_derivative (fun w => f w * g w) x (Lf * g x + f x * Lg).
Proof.
  intros f g x Lf Lg Hf Hg eps Heps.
  (* Step 1: Get Mg bounding |g(x+h)| near x *)
  assert (Hcg := deriv_implies_continuous g x Lg Hg).
  destruct (continuous_bounded_near g x Hcg) as [Mg [dg_bound [Hdgb Hbg]]].
  (* Step 2: Get continuity of g for T2 bound *)
  assert (Heps_T2 : 0 < eps * (1#3) * / (Qabs Lf + 1)).
  { apply Qmult_lt_0_compat; [lra |].
    apply Qinv_lt_0_compat. assert (H := Qabs_nonneg Lf). lra. }
  destruct (Hcg (eps * (1#3) * / (Qabs Lf + 1)) Heps_T2) as [dg_cont [Hdgc Hbgc]].
  (* Step 3: Get derivative of f for T1 bound *)
  assert (Heps_T1 : 0 < eps * (1#3) * / (Mg + 1)).
  { apply Qmult_lt_0_compat; [lra |].
    apply Qinv_lt_0_compat.
    assert (HMg_nn : 0 <= Mg).
    { (* Mg = |f(x)| + 1 from continuous_bounded_near; actually Mg is just some bound *)
      (* We know |g(x+h)| <= Mg. We need 0 <= Mg. If Mg < 0, then |g(x+h)| <= Mg < 0,
         but |g(x+h)| >= 0, so this can't hold. We need at least one h to test.
         Actually, continuous_bounded_near gives Mg such that |g(x+h)| <= Mg for
         0 < |h| < delta. We can deduce Mg >= 0 from Qabs_nonneg. But we actually
         just need Mg + 1 > 0, which holds if Mg >= -1. Since Mg >= |f(x)| >= 0...
         wait, Mg comes from the proof of continuous_bounded_near which sets
         Mg = Qabs(f x) + 1 -- but here it's for g, so Mg = Qabs(g x) + 1.
         Actually the existential doesn't guarantee Mg >= 0 directly.
         But Mg + 1 > 0 regardless: any h with 0 < |h| < dg_bound gives
         0 <= |g(x+h)| <= Mg, hence Mg >= 0. But if no such h exists...
         well 0 < dg_bound, so h = dg_bound/2 works. *)
      destruct (Qlt_le_dec Mg 0); [| lra].
      exfalso.
      (* There exists h with 0 < |h| < dg_bound *)
      assert (Hh : 0 < Qabs (dg_bound * (1#2))).
      { rewrite Qabs_pos; lra. }
      assert (Hh2 : Qabs (dg_bound * (1#2)) < dg_bound).
      { rewrite Qabs_pos; lra. }
      specialize (Hbg (dg_bound * (1#2)) Hh Hh2).
      assert (H0 := Qabs_nonneg (g (x + dg_bound * (1#2)))). lra. }
    lra. }
  destruct (Hf (eps * (1#3) * / (Mg + 1)) Heps_T1) as [df_T1 [Hdf1 Hbf1]].
  (* Step 4: Get derivative of g for T3 bound *)
  assert (Heps_T3 : 0 < eps * (1#3) * / (Qabs (f x) + 1)).
  { apply Qmult_lt_0_compat; [lra |].
    apply Qinv_lt_0_compat. assert (H := Qabs_nonneg (f x)). lra. }
  destruct (Hg (eps * (1#3) * / (Qabs (f x) + 1)) Heps_T3) as [dg_T3 [Hdg3 Hbg3]].
  (* Step 5: Find delta <= all four deltas *)
  assert (Hexd : exists delta, 0 < delta /\
    delta <= dg_bound /\ delta <= df_T1 /\ delta <= dg_cont /\ delta <= dg_T3).
  { destruct (Qlt_le_dec dg_bound df_T1);
    destruct (Qlt_le_dec dg_cont dg_T3).
    - destruct (Qlt_le_dec dg_bound dg_cont).
      + exists dg_bound; repeat split; lra.
      + exists dg_cont; repeat split; lra.
    - destruct (Qlt_le_dec dg_bound dg_T3).
      + exists dg_bound; repeat split; lra.
      + exists dg_T3; repeat split; lra.
    - destruct (Qlt_le_dec df_T1 dg_cont).
      + exists df_T1; repeat split; lra.
      + exists dg_cont; repeat split; lra.
    - destruct (Qlt_le_dec df_T1 dg_T3).
      + exists df_T1; repeat split; lra.
      + exists dg_T3; repeat split; lra. }
  destruct Hexd as [delta [Hdelta_pos [Hdle1 [Hdle2 [Hdle3 Hdle4]]]]].
  exists delta. split; [exact Hdelta_pos |].
  intros h Hh_pos Hh_lt.
  assert (Hh_dgb : Qabs h < dg_bound) by lra.
  assert (Hh_df1 : Qabs h < df_T1) by lra.
  assert (Hh_dgc : Qabs h < dg_cont) by lra.
  assert (Hh_dg3 : Qabs h < dg_T3) by lra.
  (* Algebraic decomposition *)
  assert (Hdecomp :
    f (x + h) * g (x + h) - f x * g x - (Lf * g x + f x * Lg) * h ==
    (f (x + h) - f x - Lf * h) * g (x + h) +
    Lf * h * (g (x + h) - g x) +
    f x * (g (x + h) - g x - Lg * h)) by ring.
  qabs_rw Hdecomp.
  (* Triangle inequality on three terms *)
  assert (Htri1 := Qabs_triangle
    ((f (x + h) - f x - Lf * h) * g (x + h))
    (Lf * h * (g (x + h) - g x) + f x * (g (x + h) - g x - Lg * h))).
  assert (Htri2 := Qabs_triangle
    (Lf * h * (g (x + h) - g x))
    (f x * (g (x + h) - g x - Lg * h))).
  (* Bound T1: |err_f * g(x+h)| < eps/3 * |h| *)
  assert (HT1 : Qabs ((f (x + h) - f x - Lf * h) * g (x + h)) <
                  eps * (1#3) * Qabs h).
  { rewrite Qabs_Qmult.
    specialize (Hbf1 h Hh_pos Hh_df1).
    specialize (Hbg (h) Hh_pos Hh_dgb).
    assert (HMg_nn : 0 <= Mg).
    { assert (H0 := Qabs_nonneg (g (x + h))). lra. }
    assert (Herr_nn := Qabs_nonneg (f (x + h) - f x - Lf * h)).
    destruct (Qlt_le_dec 0 Mg) as [HMg_pos | HMg_le].
    - (* Mg > 0: chain |err_f|*|g(x+h)| <= |err_f|*Mg < eps/3/(Mg+1)*|h|*Mg <= eps/3*|h| *)
      assert (H1 : Qabs (f (x + h) - f x - Lf * h) * Qabs (g (x + h)) <=
                    Qabs (f (x + h) - f x - Lf * h) * Mg).
      { assert (Hd : 0 <= Qabs (f (x + h) - f x - Lf * h) *
                            (Mg - Qabs (g (x + h)))).
        { apply Qmult_le_0_compat; [exact Herr_nn | lra]. }
        lra. }
      assert (H2 : Qabs (f (x + h) - f x - Lf * h) * Mg <
                    eps * (1#3) * / (Mg + 1) * Qabs h * Mg).
      { apply Qmult_lt_compat_r; [exact HMg_pos | exact Hbf1]. }
      assert (H3 : eps * (1#3) * / (Mg + 1) * Qabs h * Mg <=
                    eps * (1#3) * Qabs h).
      { assert (Hinv : 0 < / (Mg + 1)).
        { apply Qinv_lt_0_compat. lra. }
        assert (Hcanc : eps * (1#3) * / (Mg + 1) * Qabs h * Mg ==
                         eps * (1#3) * Qabs h * (Mg * / (Mg + 1))) by ring.
        assert (Hfrac : Mg * / (Mg + 1) <= 1).
        { assert (H4 : Mg * / (Mg + 1) <= (Mg + 1) * / (Mg + 1)).
          { apply Qmult_le_compat_r; [lra | lra]. }
          assert (H5 : (Mg + 1) * / (Mg + 1) == 1).
          { field. lra. }
          lra. }
        assert (Hcoeff : 0 <= eps * (1#3) * Qabs h).
        { apply Qmult_le_0_compat; [lra | apply Qabs_nonneg]. }
        assert (Hdiff2 : 0 <= eps * (1#3) * Qabs h * (1 - Mg * / (Mg + 1))).
        { apply Qmult_le_0_compat; [exact Hcoeff | lra]. }
        lra. }
      lra.
    - (* Mg <= 0 (hence Mg = 0): |g(x+h)| <= Mg <= 0, so |g(x+h)| = 0 *)
      assert (Hgxh : Qabs (g (x + h)) <= 0) by lra.
      assert (Hgxh0 : Qabs (g (x + h)) == 0).
      { assert (H0 := Qabs_nonneg (g (x + h))). lra. }
      assert (Hprod_le : Qabs (f (x + h) - f x - Lf * h) * Qabs (g (x + h)) <= 0).
      { assert (Hd : 0 <= Qabs (f (x + h) - f x - Lf * h) *
                            (0 - Qabs (g (x + h)))).
        { apply Qmult_le_0_compat; [exact Herr_nn | lra]. }
        lra. }
      assert (Hpos : 0 < eps * (1#3) * Qabs h).
      { apply Qmult_lt_0_compat; lra. }
      lra. }
  (* Bound T2: |Lf * h * (g(x+h) - g(x))| < eps/3 * |h| *)
  assert (HT2 : Qabs (Lf * h * (g (x + h) - g x)) < eps * (1#3) * Qabs h).
  { rewrite Qabs_Qmult. rewrite Qabs_Qmult.
    specialize (Hbgc h Hh_pos Hh_dgc).
    assert (HLf_nn := Qabs_nonneg Lf).
    (* Step 1: |Lf|*|h|*|g(x+h)-g(x)| <= |Lf|*|h|*eps/3/(|Lf|+1) via nonneg diff *)
    assert (H1 : Qabs Lf * Qabs h * Qabs (g (x + h) - g x) <=
                  Qabs Lf * Qabs h * (eps * (1#3) * / (Qabs Lf + 1))).
    { assert (Hd : 0 <= Qabs Lf * Qabs h *
                          ((eps * (1#3) * / (Qabs Lf + 1)) - Qabs (g (x + h) - g x))).
      { apply Qmult_le_0_compat.
        - apply Qmult_le_0_compat; [exact HLf_nn | apply Qabs_nonneg].
        - lra. }
      assert (Hr : Qabs Lf * Qabs h *
                      ((eps * (1#3) * / (Qabs Lf + 1)) - Qabs (g (x + h) - g x)) ==
                    Qabs Lf * Qabs h * (eps * (1#3) * / (Qabs Lf + 1)) -
                    Qabs Lf * Qabs h * Qabs (g (x + h) - g x)) by ring.
      lra. }
    (* Step 2: |Lf|*(|h|*eps/3/(|Lf|+1)) < (|Lf|+1)*(|h|*eps/3/(|Lf|+1)) = eps/3*|h| *)
    assert (Hz_pos : 0 < Qabs h * (eps * (1#3) * / (Qabs Lf + 1))).
    { apply Qmult_lt_0_compat; [exact Hh_pos | exact Heps_T2]. }
    assert (H2 : Qabs Lf * (Qabs h * (eps * (1#3) * / (Qabs Lf + 1))) <
                  (Qabs Lf + 1) * (Qabs h * (eps * (1#3) * / (Qabs Lf + 1)))).
    { apply Qmult_lt_compat_r; [exact Hz_pos | lra]. }
    assert (Hassoc : Qabs Lf * Qabs h * (eps * (1#3) * / (Qabs Lf + 1)) ==
                      Qabs Lf * (Qabs h * (eps * (1#3) * / (Qabs Lf + 1)))) by ring.
    assert (Hcancel : (Qabs Lf + 1) * (Qabs h * (eps * (1#3) * / (Qabs Lf + 1))) ==
                       eps * (1#3) * Qabs h).
    { field. lra. }
    lra. }
  (* Bound T3: |f(x) * err_g| < eps/3 * |h| *)
  assert (HT3 : Qabs (f x * (g (x + h) - g x - Lg * h)) < eps * (1#3) * Qabs h).
  { rewrite Qabs_Qmult.
    specialize (Hbg3 h Hh_pos Hh_dg3).
    assert (HFx_nn := Qabs_nonneg (f x)).
    (* Step 1: |f(x)|*|err_g| <= |f(x)|*eps/3/(|f(x)|+1)*|h| via nonneg diff *)
    assert (H1 : Qabs (f x) * Qabs (g (x + h) - g x - Lg * h) <=
                  Qabs (f x) * (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h)).
    { assert (Hd : 0 <= Qabs (f x) *
                          (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h -
                           Qabs (g (x + h) - g x - Lg * h))).
      { apply Qmult_le_0_compat; [lra | lra]. }
      assert (Hr : Qabs (f x) *
                      (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h -
                       Qabs (g (x + h) - g x - Lg * h)) ==
                    Qabs (f x) * (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h) -
                    Qabs (f x) * Qabs (g (x + h) - g x - Lg * h)) by ring.
      lra. }
    (* Step 2: |f(x)|*(eps/3/(|f(x)|+1)*|h|) < (|f(x)|+1)*(eps/3/(|f(x)|+1)*|h|) = eps/3*|h| *)
    assert (Hz_pos : 0 < eps * (1#3) * / (Qabs (f x) + 1) * Qabs h).
    { apply Qmult_lt_0_compat; [exact Heps_T3 | exact Hh_pos]. }
    assert (H2 : Qabs (f x) * (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h) <
                  (Qabs (f x) + 1) * (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h)).
    { apply Qmult_lt_compat_r; [exact Hz_pos | lra]. }
    assert (Hcancel : (Qabs (f x) + 1) * (eps * (1#3) * / (Qabs (f x) + 1) * Qabs h) ==
                       eps * (1#3) * Qabs h).
    { field. lra. }
    lra. }
  (* Combine: |T1+T2+T3| <= |T1| + |T2| + |T3| < eps * |h| *)
  (* Reassociate (T1+T2)+T3 to T1+(T2+T3) to match Htri1 *)
  assert (Hassoc_sum :
    (f (x + h) - f x - Lf * h) * g (x + h) +
    Lf * h * (g (x + h) - g x) +
    f x * (g (x + h) - g x - Lg * h) ==
    (f (x + h) - f x - Lf * h) * g (x + h) +
    (Lf * h * (g (x + h) - g x) +
     f x * (g (x + h) - g x - Lg * h))) by ring.
  qabs_rw Hassoc_sum.
  lra.
Qed.

(** Power rule: d/dx(x^{n+1}) = (n+1) * x^n *)
Lemma deriv_power_succ : forall (n : nat) (x : Q),
  has_derivative (fun w => Qpow w (S n)) x
                 (inject_Z (Z.of_nat (S n)) * Qpow x n).
Proof.
  induction n; intros x.
  - (* Base: d/dx(x^1) = 1 * x^0 = 1 *)
    apply (has_derivative_ext (fun w => w)).
    + intros w. cbn [Qpow]. ring.
    + apply (has_derivative_eq _ _ 1).
      * cbn [Qpow]. ring.
      * exact (deriv_id x).
  - (* Step: d/dx(x^{S(S n)}) using product rule *)
    (* x^{S(S n)} = x * x^{S n} *)
    apply (has_derivative_ext (fun w => w * Qpow w (S n))).
    + intros w. cbn [Qpow]. ring.
    + (* Product rule: f=id (L=1), g=x^{S n} (L=IH) *)
      assert (Hprod := deriv_product (fun w => w) (fun w => Qpow w (S n)) x
                1 (inject_Z (Z.of_nat (S n)) * Qpow x n)
                (deriv_id x) (IHn x)).
      apply (has_derivative_eq _ _ (1 * Qpow x (S n) +
                                     x * (inject_Z (Z.of_nat (S n)) * Qpow x n))).
      * (* Need: 1*x^{Sn} + x*(inject_Z(Sn)*x^n) == inject_Z(S(Sn))*x^{Sn} *)
        assert (Hinj : inject_Z (Z.of_nat (S (S n))) ==
                         inject_Z (Z.of_nat (S n)) + 1).
        { replace (Z.of_nat (S (S n))) with (Z.of_nat (S n) + 1)%Z by lia.
          rewrite inject_Z_plus. reflexivity. }
        setoid_rewrite Hinj. cbn [Qpow]. ring.
      * exact Hprod.
Qed.

(** Derivative is unique *)
Lemma deriv_unique : forall (f : Q -> Q) (x L L' : Q),
  has_derivative f x L -> has_derivative f x L' -> L == L'.
Proof.
  intros f x L L' Hf Hg.
  destruct (Qeq_dec L L') as [Heq | Hneq]; [exact Heq |].
  (* L /= L' leads to contradiction *)
  exfalso.
  assert (Hdiff_pos : 0 < Qabs (L - L')).
  { destruct (Qlt_le_dec (L - L') 0).
    - rewrite Qabs_neg; lra.
    - rewrite Qabs_pos; [|lra].
      destruct (Qlt_le_dec 0 (L - L')); [lra | exfalso; apply Hneq; lra]. }
  set (eps := Qabs (L - L') * (1#4)).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hf eps Heps) as [d1 [Hd1 Hb1]].
  destruct (Hg eps Heps) as [d2 [Hd2 Hb2]].
  (* Pick h = min(d1, d2) / 2 *)
  set (h := Qmin d1 d2 * (1#2)).
  assert (Hh_pos : 0 < h).
  { unfold h. destruct (Q.min_spec d1 d2) as [[_ ->] | [_ ->]]; lra. }
  assert (Hh_abs : Qabs h == h).
  { rewrite Qabs_pos; lra. }
  assert (Hh_pos2 : 0 < Qabs h) by lra.
  assert (Hh_d1 : Qabs h < d1).
  { assert (Hmin := Q.le_min_l d1 d2). unfold h in Hh_abs |- *. lra. }
  assert (Hh_d2 : Qabs h < d2).
  { assert (Hmin := Q.le_min_r d1 d2). unfold h in Hh_abs |- *. lra. }
  specialize (Hb1 h Hh_pos2 Hh_d1).
  specialize (Hb2 h Hh_pos2 Hh_d2).
  (* |(L - L') * h| <= |err1| + |err2| *)
  assert (Hdecomp : (L - L') * h == (f (x + h) - f x - L' * h) -
                                      (f (x + h) - f x - L * h)) by ring.
  assert (Habs_diff := Qabs_wd _ _ Hdecomp).
  assert (Htri := Qabs_triangle (f (x + h) - f x - L' * h)
                                 (-(f (x + h) - f x - L * h))).
  rewrite Qabs_opp in Htri.
  rewrite Qabs_Qmult in Habs_diff.
  (* |L-L'| * |h| < 2 * eps * |h| = |L-L'|/2 * |h| *)
  assert (Hcontra : Qabs (L - L') * Qabs h < 2 * eps * Qabs h).
  { (* Chain: |L-L'|*|h| == |decomp| <= |A|+|B| < 2*eps*|h| *)
    assert (Hle : Qabs (L - L') * Qabs h <=
                   Qabs (f (x + h) - f x - L' * h) +
                   Qabs (f (x + h) - f x - L * h)).
    { apply Qle_trans with
        (y := Qabs ((f (x + h) - f x - L' * h) - (f (x + h) - f x - L * h))).
      - rewrite Habs_diff. apply Qle_refl.
      - exact Htri. }
    lra. }
  (* 2*eps*|h| == |L-L'|*|h| * (1/2), so |L-L'|*|h| < |L-L'|*|h|*(1/2) — contradiction *)
  assert (Hdp : 0 < Qabs (L - L') * Qabs h).
  { apply Qmult_lt_0_compat; [exact Hdiff_pos | exact Hh_pos2]. }
  assert (H2epsH : 2 * eps * Qabs h == Qabs (L - L') * Qabs h * (1#2)).
  { unfold eps. ring. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: APPLICATIONS TO OPTIMIZATION                                    *)
(* ========================================================================= *)

(** Derivative of affine function *)
Lemma deriv_affine : forall (a b x : Q),
  has_derivative (fun w => a * w + b) x a.
Proof.
  intros a b x eps Heps.
  exists 1. split; [lra |].
  intros h Hh_pos Hh_lt.
  assert (Heq : a * (x + h) + b - (a * x + b) - a * h == 0) by ring.
  qabs_rw Heq. rewrite Qabs_pos; [| lra].
  apply Qmult_lt_0_compat; lra.
Qed.

(** Derivative of quadratic loss: d/dw (w - wstar)^2 = 2(w - wstar) *)
Lemma quadratic_loss_derivative : forall (wstar x : Q),
  has_derivative (fun w => (w - wstar) * (w - wstar)) x (2 * (x - wstar)).
Proof.
  intros wstar x eps Heps.
  exists eps. split; [exact Heps |].
  intros h Hh_pos Hh_lt.
  assert (Heq : (x + h - wstar) * (x + h - wstar) -
                 (x - wstar) * (x - wstar) -
                 2 * (x - wstar) * h == h * h) by ring.
  qabs_rw Heq.
  rewrite Qabs_Qmult.
  apply Qmult_lt_compat_r; [exact Hh_pos | exact Hh_lt].
Qed.

(** GD step = w - eta * L'(w) for quadratic loss *)
Lemma gradient_step_uses_derivative : forall (w0 wstar eta : Q),
  gd_weight w0 wstar eta 1 == w0 - eta * (2 * (w0 - wstar)).
Proof.
  intros. unfold gd_weight, gd_error, contraction. ring.
Qed.

(** Fermat's theorem: local minimum implies zero derivative *)
Lemma local_min_zero_deriv : forall (f : Q -> Q) (x L : Q),
  local_min f x -> has_derivative f x L -> L == 0.
Proof.
  intros f x L [dm [Hdm Hmin]] Hderiv.
  destruct (Qeq_dec L 0) as [HL0 | HLnz]; [exact HL0 |].
  exfalso.
  assert (HLabs_pos : 0 < Qabs L).
  { destruct (Qlt_le_dec L 0).
    - rewrite Qabs_neg; lra.
    - rewrite Qabs_pos; [|lra].
      destruct (Qlt_le_dec 0 L); [lra | exfalso; apply HLnz; lra]. }
  (* Use eps = |L|/2 *)
  assert (Heps : 0 < Qabs L * (1#2)) by lra.
  destruct (Hderiv (Qabs L * (1#2)) Heps) as [dd [Hdd Hbd]].
  destruct (Qlt_le_dec L 0) as [HLneg | HLpos].
  - (* L < 0: take h > 0 *)
    set (h := Qmin dm dd * (1#2)).
    assert (Hh_pos : 0 < h).
    { unfold h. destruct (Q.min_spec dm dd) as [[_ ->] | [_ ->]]; lra. }
    assert (Hh_abs : Qabs h == h) by (rewrite Qabs_pos; lra).
    assert (Hh_pos2 : 0 < Qabs h) by lra.
    assert (Hh_dm : Qabs h < dm).
    { assert (Hmin_l := Q.le_min_l dm dd). unfold h in Hh_abs |- *. lra. }
    assert (Hh_dd : Qabs h < dd).
    { assert (Hmin_r := Q.le_min_r dm dd). unfold h in Hh_abs |- *. lra. }
    (* From local min: f(x) <= f(x+h), so f(x+h) - f(x) >= 0 *)
    assert (Hmin_h := Hmin h Hh_dm).
    assert (Hge : 0 <= f (x + h) - f x) by lra.
    (* From derivative: |f(x+h)-f(x)-L*h| < |L|/2 * |h| *)
    specialize (Hbd h Hh_pos2 Hh_dd).
    (* This means: f(x+h)-f(x)-L*h > -(|L|/2)*|h| and < (|L|/2)*|h| *)
    (* So f(x+h)-f(x) < L*h + |L|/2 * |h| *)
    (* Since L < 0 and h > 0: L*h < 0 and |L| = -L, |h| = h *)
    (* f(x+h)-f(x) < L*h + (-L)/2 * h = L*h/2 + L*h/2 + (-L)/2*h = L*h + (-L*h)/2 *)
    (* Actually: L*h + |L|/2 * |h| = L*h + (-L)/2 * h = L*h - L*h/2 = L*h/2 *)
    (* Since L < 0 and h > 0: L*h/2 < 0 *)
    assert (HLabs : Qabs L == -L) by (rewrite Qabs_neg; lra).
    (* |err| < |L|/2 * |h|  →  err < |L|/2 * |h|  (since err <= |err|) *)
    assert (Hle_err : f (x + h) - f x - L * h <=
                       Qabs (f (x + h) - f x - L * h)).
    { destruct (Qlt_le_dec (f (x + h) - f x - L * h) 0).
      - rewrite Qabs_neg; [|lra]. lra.
      - rewrite Qabs_pos; lra. }
    assert (Hupper : f (x + h) - f x - L * h < Qabs L * (1#2) * Qabs h) by lra.
    (* |L|/2 * |h| = (-L)/2 * h since L < 0 and h > 0 *)
    assert (Hrewrite : Qabs L * (1#2) * Qabs h == (- L) * (1#2) * h).
    { setoid_rewrite HLabs. setoid_rewrite Hh_abs. ring. }
    (* f(x+h)-f(x) < L*h + (-L)/2*h = L/2*h < 0 contradicts f(x) <= f(x+h) *)
    assert (Hsimp : L * h + (-L) * (1#2) * h == L * (1#2) * h) by ring.
    assert (Hneg : L * (1#2) * h < 0).
    { assert (H1 : 0 < (-L) * (1#2) * h).
      { apply Qmult_lt_0_compat; [| exact Hh_pos]. lra. }
      lra. }
    lra.
  - (* L > 0: take h < 0 *)
    assert (HLpos2 : 0 < L).
    { destruct (Qlt_le_dec 0 L); [lra | exfalso; apply HLnz; lra]. }
    set (h := -(Qmin dm dd * (1#2))).
    assert (Hh_neg : h < 0).
    { unfold h. destruct (Q.min_spec dm dd) as [[_ ->] | [_ ->]]; lra. }
    assert (Hh_abs : Qabs h == -h) by (rewrite Qabs_neg; lra).
    assert (Hh_pos2 : 0 < Qabs h) by lra.
    assert (Hh_dm : Qabs h < dm).
    { assert (Hmin_l := Q.le_min_l dm dd). unfold h in Hh_abs |- *. lra. }
    assert (Hh_dd : Qabs h < dd).
    { assert (Hmin_r := Q.le_min_r dm dd). unfold h in Hh_abs |- *. lra. }
    assert (Hmin_h := Hmin h Hh_dm).
    assert (Hge : 0 <= f (x + h) - f x) by lra.
    specialize (Hbd h Hh_pos2 Hh_dd).
    assert (HLabs : Qabs L == L) by (rewrite Qabs_pos; lra).
    setoid_rewrite HLabs in Hbd.
    assert (Hle_err : f (x + h) - f x - L * h <=
                       Qabs (f (x + h) - f x - L * h)).
    { destruct (Qlt_le_dec (f (x + h) - f x - L * h) 0).
      - rewrite Qabs_neg; [|lra]. lra.
      - rewrite Qabs_pos; lra. }
    assert (Hupper : f (x + h) - f x - L * h < L * (1#2) * Qabs h) by lra.
    (* L * h = L * (-(min*1/2)) = -L * min/2 < 0 since L > 0 *)
    (* |h| = -h, so L*(1/2)*|h| = L*(1/2)*(-h) = -L*h/2 *)
    (* f(x+h)-f(x) < L*h + L/2*(-h) = L*h - L*h/2 = L*h/2 *)
    assert (Hrewrite : L * (1#2) * Qabs h == -(L * (1#2) * h)).
    { setoid_rewrite Hh_abs. ring. }
    assert (Hfinal : f (x + h) - f x < L * h + -(L * (1#2) * h)).
    { lra. }
    assert (Hsimp : L * h + -(L * (1#2) * h) == L * (1#2) * h) by ring.
    assert (Hneg : L * (1#2) * h < 0).
    { assert (H1 : 0 < L * (1#2) * (-h)).
      { apply Qmult_lt_0_compat; [lra | lra]. }
      lra. }
    lra.
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                               *)
(* ========================================================================= *)

Check has_derivative_ext.
Check has_derivative_eq.
Check deriv_const.
Check deriv_id.
Check deriv_scale.
Check deriv_neg.
Check deriv_sum.
Check deriv_sub.
Check deriv_implies_continuous.
Check continuous_bounded_near.
Check deriv_square.
Check deriv_product.
Check deriv_power_succ.
Check deriv_unique.
Check deriv_affine.
Check quadratic_loss_derivative.
Check gradient_step_uses_derivative.
Check local_min_zero_deriv.

Print Assumptions deriv_product.
Print Assumptions deriv_power_succ.
Print Assumptions local_min_zero_deriv.
Print Assumptions gradient_step_uses_derivative.
