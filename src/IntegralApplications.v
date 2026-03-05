(* ========================================================================= *)
(*        INTEGRAL APPLICATIONS — PRODUCT RULE, IBP, UDIFF EXTENSIONS       *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Extend the integration framework with:                         *)
(*    - Product rule for uniform differentiability (udiff_product)           *)
(*    - Integration by parts (IBP) via FTC + product rule                   *)
(*    - IBP applications and corollaries                                    *)
(*    - Additional udiff closure properties (negate, subtract, square)      *)
(*    - Antiderivative uniqueness                                           *)
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
From ToS Require Import EVT_idx.
From ToS Require Import Differentiation.
From ToS Require Import MeanValueTheorem.
From ToS Require Import RiemannIntegration.

Open Scope Q_scope.

(** Helper: Qeq implies Qle *)
Lemma Qeq_Qle : forall x y : Q, x == y -> x <= y.
Proof. intros. lra. Qed.

(* ========================================================================= *)
(* DEFINITIONS                                                                *)
(* ========================================================================= *)

(** Product telescoping sum: Σ_{k=0}^{n-1} [f(y_{k+1})*g(y_{k+1}) - f(y_k)*g(y_k)] *)
Fixpoint product_tele (f g : Q -> Q) (a step : Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => (f (walk_point a step n) * g (walk_point a step n)
            - f (walk_point a step n') * g (walk_point a step n'))
            + product_tele f g a step n'
  end.

(* ========================================================================= *)
(* SECTION 1: ALGEBRAIC IDENTITIES                                           *)
(* ========================================================================= *)

(** L1: Product increment decomposition — the algebraic heart of the product rule.
    f(x+h)*g(x+h) - f(x)*g(x) - (f'(x)*g(x) + f(x)*g'(x))*h
    = error_f * g(x) + f(x) * error_g + Δf * Δg
    where error_f = f(x+h)-f(x)-f'(x)*h, error_g = g(x+h)-g(x)-g'(x)*h,
    Δf = f(x+h)-f(x), Δg = g(x+h)-g(x) *)
Lemma product_decomp : forall a1 a2 b1 b2 c1 c2 h : Q,
  a1 * b1 - a2 * b2 - (c1 * b2 + a2 * c2) * h ==
  (a1 - a2 - c1 * h) * b2 + a2 * (b1 - b2 - c2 * h) + (a1 - a2) * (b1 - b2).
Proof.
  intros. ring.
Qed.

(** L2: Product telescoping sum collapses to endpoint difference *)
Lemma product_tele_collapse : forall (f g : Q -> Q) (a step : Q) (n : nat),
  product_tele f g a step n ==
  f (walk_point a step n) * g (walk_point a step n) - f a * g a.
Proof.
  intros f g a step n. induction n as [| n' IH].
  - simpl. ring.
  - assert (Hunfold : product_tele f g a step (S n') ==
      (f (walk_point a step (S n')) * g (walk_point a step (S n'))
       - f (walk_point a step n') * g (walk_point a step n'))
       + product_tele f g a step n') by reflexivity.
    set (PTsn := product_tele f g a step (S n')) in *.
    set (PT := product_tele f g a step n') in *.
    set (PGsn := f (walk_point a step (S n')) * g (walk_point a step (S n'))) in *.
    set (PGn := f (walk_point a step n') * g (walk_point a step n')) in *.
    set (PGa := f a * g a) in *.
    lra.
Qed.

(** L3: Triple triangle inequality: |a + b + c| ≤ |a| + |b| + |c| *)
Lemma triple_abs_bound : forall a b c : Q,
  Qabs (a + b + c) <= Qabs a + Qabs b + Qabs c.
Proof.
  intros a b c.
  apply Qle_trans with (Qabs (a + b) + Qabs c).
  - apply Qabs_triangle.
  - assert (H : Qabs (a + b) <= Qabs a + Qabs b) by apply Qabs_triangle.
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: INCREMENT & ERROR BOUNDS                                        *)
(* ========================================================================= *)

(** L4: Extensionality for Riemann sums — if f and g agree at grid points,
    their Riemann sums are equal *)
Lemma riemann_sum_ext : forall (f g : Q -> Q) (a step : Q) (n : nat),
  (forall k : nat, (k < n)%nat -> f (walk_point a step k) == g (walk_point a step k)) ->
  riemann_sum f a step n == riemann_sum g a step n.
Proof.
  intros f g a step n Hext. induction n as [| n' IH].
  - simpl. ring.
  - assert (Hunf : riemann_sum f a step (S n') =
      f (walk_point a step n') * step + riemann_sum f a step n') by reflexivity.
    assert (Hung : riemann_sum g a step (S n') =
      g (walk_point a step n') * step + riemann_sum g a step n') by reflexivity.
    assert (Hterm : f (walk_point a step n') == g (walk_point a step n')).
    { apply Hext. lia. }
    assert (IH' : riemann_sum f a step n' == riemann_sum g a step n').
    { apply IH. intros k Hk. apply Hext. lia. }
    rewrite Hunf, Hung.
    setoid_rewrite Hterm. lra.
Qed.

(** L5: Increment bound from uniform differentiability.
    If f is udiff with bounded derivative, the increment is controlled. *)
Lemma increment_from_udiff : forall (f f' : Q -> Q) (a b M eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 < eps ->
  exists delta : Q, 0 < delta /\
    forall x h : Q, a <= x -> x <= b ->
      0 < Qabs h -> Qabs h < delta ->
      Qabs (f (x + h) - f x) <= (M + eps) * Qabs h.
Proof.
  intros f f' a b M eps [Hab Huf] HM Heps.
  destruct (Huf eps Heps) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta |].
  intros x h Hax Hxb Hh_pos Hh.
  (* f(x+h) - f(x) = f'(x)*h + error *)
  assert (Herr : Qabs (f (x + h) - f x - f' x * h) < eps * Qabs h).
  { exact (Hbd x h Hax Hxb Hh_pos Hh). }
  (* |f(x+h) - f(x)| = |(f'(x)*h + error)| ≤ |f'(x)*h| + |error| *)
  assert (Hdecomp : f (x + h) - f x == (f' x * h) + (f (x + h) - f x - f' x * h)) by ring.
  assert (Htri : Qabs (f (x + h) - f x) <= Qabs (f' x * h) + Qabs (f (x + h) - f x - f' x * h)).
  { qabs_rw Hdecomp. apply Qabs_triangle. }
  assert (Hfh : Qabs (f' x * h) <= M * Qabs h).
  { rewrite Qabs_Qmult. apply Qmult_le_compat_r; [apply HM; assumption | apply Qabs_nonneg]. }
  apply Qle_trans with (Qabs (f' x * h) + Qabs (f (x + h) - f x - f' x * h)).
  { exact Htri. }
  apply Qle_trans with (M * Qabs h + eps * Qabs h).
  { lra. }
  lra.
Qed.

(** L6: Product of increment bounds *)
Lemma increment_product_bound : forall (A B h1 h2 : Q),
  0 <= A -> 0 <= B ->
  Qabs h1 <= A -> Qabs h2 <= B ->
  Qabs (h1 * h2) <= A * B.
Proof.
  intros A B h1 h2 HA HB Hh1 Hh2.
  rewrite Qabs_Qmult.
  apply Qmult_le_compat_nonneg.
  - split; [apply Qabs_nonneg | exact Hh1].
  - split; [apply Qabs_nonneg | exact Hh2].
Qed.

(** L7: Per-step product error bound.
    |ef*g(x) + f(x)*eg + Δf*Δg| ≤ (e1*Mg + Mf*e2 + A*B*|h|) * |h| *)
Lemma product_error_bound : forall (ef eg df_dg : Q)
  (Mg Mf A_B_h : Q),
  0 <= Mg -> 0 <= Mf -> 0 <= A_B_h ->
  Qabs ef <= Mg ->
  Qabs eg <= Mf ->
  Qabs df_dg <= A_B_h ->
  Qabs (ef + eg + df_dg) <= Mg + Mf + A_B_h.
Proof.
  intros ef eg df_dg Mg Mf A_B_h HMg HMf HABh Hef Heg Hdf.
  apply Qle_trans with (Qabs ef + Qabs eg + Qabs df_dg).
  - apply triple_abs_bound.
  - lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: PRODUCT RULE & EXTENSIONS                                       *)
(* ========================================================================= *)

(** L8: Extensionality for udiff_on — if f==g and f'==g' pointwise on [a,b],
    then udiff transfers *)
Lemma udiff_ext : forall (f g f' g' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  (forall x : Q, f x == g x) ->
  (forall x : Q, f' x == g' x) ->
  udiff_on g g' a b.
Proof.
  intros f g f' g' a b [Hab Huf] Hfg Hfg'.
  split; [exact Hab |].
  intros eps Heps.
  destruct (Huf eps Heps) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta |].
  intros x h Hax Hxb Hh_pos Hh.
  specialize (Hbd x h Hax Hxb Hh_pos Hh).
  (* Need: |g(x+h) - g(x) - g'(x)*h| < eps * |h| *)
  (* Have: |f(x+h) - f(x) - f'(x)*h| < eps * |h| *)
  assert (Heq : g (x + h) - g x - g' x * h == f (x + h) - f x - f' x * h).
  { rewrite (Hfg (x + h)). rewrite (Hfg x). rewrite (Hfg' x). ring. }
  qabs_rw Heq. exact Hbd.
Qed.

(** L9: Product rule for uniform differentiability.
    If f and g are uniformly differentiable with bounded values and derivatives,
    then f*g is uniformly differentiable with derivative f'*g + f*g'. *)
Lemma udiff_product : forall (f f' g g' : Q -> Q) (a b Mf Mg Mf' Mg' : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x) <= Mf) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g x) <= Mg) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g' x) <= Mg') ->
  0 <= Mf -> 0 <= Mg -> 0 <= Mf' -> 0 <= Mg' ->
  udiff_on (fun x => f x * g x) (fun x => f' x * g x + f x * g' x) a b.
Proof.
  intros f f' g g' a b Mf Mg Mf' Mg' Huf Hug HMf HMg HMf' HMg' HMf_nn HMg_nn HMf'_nn HMg'_nn.
  destruct Huf as [Hab Huf_body].
  destruct Hug as [_ Hug_body].
  split; [exact Hab |].
  intros eps Heps.
  (* Split eps into 3 parts *)
  assert (HMg1 : 0 < Mg + 1) by lra.
  assert (HMf1 : 0 < Mf + 1) by lra.
  set (eps1 := eps / (3 * (Mg + 1))).
  set (eps2 := eps / (3 * (Mf + 1))).
  assert (Heps1 : 0 < eps1).
  { unfold eps1. apply Qlt_shift_div_l; lra. }
  assert (Heps2 : 0 < eps2).
  { unfold eps2. apply Qlt_shift_div_l; lra. }
  (* Get deltas from udiff *)
  destruct (Huf_body eps1 Heps1) as [df [Hdf Hbdf]].
  destruct (Hug_body eps2 Heps2) as [dg [Hdg Hbdg]].
  (* Delta for the product term Δf*Δg *)
  set (A := Mf' + eps1 + 1).
  set (B := Mg' + eps2 + 1).
  assert (HA : 0 < A) by (unfold A; lra).
  assert (HB : 0 < B) by (unfold B; lra).
  assert (HAB : 0 < A * B) by (apply Qmult_lt_0_compat; assumption).
  set (d3 := eps / (3 * (A * B))).
  assert (Hd3 : 0 < d3).
  { unfold d3. apply Qlt_shift_div_l; lra. }
  (* Take minimum of three deltas *)
  exists (Qmin (Qmin df dg) d3).
  split.
  { apply Q.min_glb_lt; [apply Q.min_glb_lt |]; assumption. }
  intros x h Hax Hxb Hh_pos Hh.
  (* Extract individual delta bounds *)
  assert (Hh_df : Qabs h < df).
  { apply Qlt_le_trans with (Qmin (Qmin df dg) d3); [exact Hh |].
    apply Qle_trans with (Qmin df dg); [apply Q.le_min_l | apply Q.le_min_l]. }
  assert (Hh_dg : Qabs h < dg).
  { apply Qlt_le_trans with (Qmin (Qmin df dg) d3); [exact Hh |].
    apply Qle_trans with (Qmin df dg); [apply Q.le_min_l | apply Q.le_min_r]. }
  assert (Hh_d3 : Qabs h < d3).
  { apply Qlt_le_trans with (Qmin (Qmin df dg) d3); [exact Hh |].
    apply Q.le_min_r. }
  (* Get udiff error bounds *)
  assert (Hef : Qabs (f (x + h) - f x - f' x * h) < eps1 * Qabs h).
  { exact (Hbdf x h Hax Hxb Hh_pos Hh_df). }
  assert (Heg : Qabs (g (x + h) - g x - g' x * h) < eps2 * Qabs h).
  { exact (Hbdg x h Hax Hxb Hh_pos Hh_dg). }
  (* Bound values *)
  assert (HMgx : Qabs (g x) <= Mg) by (apply HMg; assumption).
  assert (HMfx : Qabs (f x) <= Mf) by (apply HMf; assumption).
  (* Apply product_decomp:
     f(x+h)*g(x+h) - f(x)*g(x) - (f'(x)*g(x)+f(x)*g'(x))*h
     = ef*g(x) + f(x)*eg + Δf*Δg *)
  set (ef := f (x + h) - f x - f' x * h).
  set (eg := g (x + h) - g x - g' x * h).
  set (Df := f (x + h) - f x).
  set (Dg := g (x + h) - g x).
  fold ef in Hef. fold eg in Heg.
  assert (Hdecomp :
    f (x + h) * g (x + h) - f x * g x - (f' x * g x + f x * g' x) * h ==
    ef * g x + f x * eg + Df * Dg).
  { unfold ef, eg, Df, Dg. ring. }
  qabs_rw Hdecomp.
  (* Bound each of the three terms *)
  (* Term 1: |ef * g(x)| ≤ eps1*|h|*Mg *)
  assert (HT1 : Qabs (ef * g x) <= eps1 * Qabs h * Mg).
  { rewrite Qabs_Qmult.
    apply Qle_trans with (eps1 * Qabs h * Mg).
    - apply Qmult_le_compat_nonneg.
      + split; [apply Qabs_nonneg | lra].
      + split; [apply Qabs_nonneg | exact HMgx].
    - lra. }
  (* Term 2: |f(x) * eg| ≤ Mf*eps2*|h| *)
  assert (HT2 : Qabs (f x * eg) <= Mf * (eps2 * Qabs h)).
  { rewrite Qabs_Qmult.
    apply Qmult_le_compat_nonneg.
    - split; [apply Qabs_nonneg | exact HMfx].
    - split; [apply Qabs_nonneg | lra]. }
  (* Term 3: |Δf * Δg| — need increment bounds *)
  (* |Δf| ≤ |f'(x)*h| + |ef| ≤ (Mf'+eps1)*|h| *)
  assert (HDf_decomp : Df == f' x * h + ef) by (unfold Df, ef; ring).
  assert (HDf_bound : Qabs Df <= (Mf' + eps1) * Qabs h).
  { qabs_rw HDf_decomp.
    apply Qle_trans with (Qabs (f' x * h) + Qabs ef).
    - apply Qabs_triangle.
    - assert (H1 : Qabs (f' x * h) <= Mf' * Qabs h).
      { rewrite Qabs_Qmult. apply Qmult_le_compat_r; [apply HMf'; assumption | apply Qabs_nonneg]. }
      lra. }
  (* |Δg| ≤ (Mg'+eps2)*|h| *)
  assert (HDg_decomp : Dg == g' x * h + eg) by (unfold Dg, eg; ring).
  assert (HDg_bound : Qabs Dg <= (Mg' + eps2) * Qabs h).
  { qabs_rw HDg_decomp.
    apply Qle_trans with (Qabs (g' x * h) + Qabs eg).
    - apply Qabs_triangle.
    - assert (H1 : Qabs (g' x * h) <= Mg' * Qabs h).
      { rewrite Qabs_Qmult. apply Qmult_le_compat_r; [apply HMg'; assumption | apply Qabs_nonneg]. }
      lra. }
  (* |Δf*Δg| ≤ (Mf'+eps1)*(Mg'+eps2)*|h|² *)
  assert (HT3 : Qabs (Df * Dg) <= (Mf' + eps1) * (Mg' + eps2) * (Qabs h * Qabs h)).
  { rewrite Qabs_Qmult.
    apply Qle_trans with ((Mf' + eps1) * Qabs h * ((Mg' + eps2) * Qabs h)).
    - apply Qmult_le_compat_nonneg.
      + split; [apply Qabs_nonneg | exact HDf_bound].
      + split; [apply Qabs_nonneg | exact HDg_bound].
    - assert (Hring : (Mf' + eps1) * Qabs h * ((Mg' + eps2) * Qabs h) ==
                       (Mf' + eps1) * (Mg' + eps2) * (Qabs h * Qabs h)) by ring.
      lra. }
  (* Now combine: |ef*g(x) + f(x)*eg + Df*Dg| ≤ sum of three bounds *)
  apply Qle_lt_trans with (Qabs (ef * g x) + Qabs (f x * eg) + Qabs (Df * Dg)).
  { apply triple_abs_bound. }
  (* Each term bound:
     eps1*|h|*Mg ≤ eps/3*|h| since eps1*Mg = eps*Mg/(3*(Mg+1)) ≤ eps/3
     Mf*eps2*|h| ≤ eps/3*|h| since Mf*eps2 = eps*Mf/(3*(Mf+1)) ≤ eps/3
     (Mf'+eps1)*(Mg'+eps2)*|h|² ≤ A*B*d3*|h| ≤ eps/3*|h| *)
  assert (Hterm1 : eps1 * Qabs h * Mg <= eps / 3 * Qabs h).
  { assert (Hsub : eps1 * Mg <= eps / 3).
    { unfold eps1.
      assert (Hznn : 0 <= eps / (3 * (Mg + 1))).
      { apply Qle_shift_div_l; [lra |]. rewrite Qmult_0_l. lra. }
      setoid_replace (eps / (3 * (Mg + 1)) * Mg)
        with (Mg * (eps / (3 * (Mg + 1)))) by ring.
      setoid_replace (eps / 3)
        with ((Mg + 1) * (eps / (3 * (Mg + 1)))) by (field; lra).
      apply Qmult_le_compat_r; [lra | exact Hznn]. }
    assert (Hnn : 0 <= Qabs h) by apply Qabs_nonneg.
    assert (Hcomm : eps1 * Qabs h * Mg == eps1 * Mg * Qabs h) by ring.
    setoid_rewrite Hcomm.
    apply Qmult_le_compat_r; [exact Hsub | exact Hnn]. }
  assert (Hterm2 : Mf * (eps2 * Qabs h) <= eps / 3 * Qabs h).
  { assert (Hsub : Mf * eps2 <= eps / 3).
    { unfold eps2.
      assert (Hznn : 0 <= eps / (3 * (Mf + 1))).
      { apply Qle_shift_div_l; [lra |]. rewrite Qmult_0_l. lra. }
      setoid_replace (eps / 3)
        with ((Mf + 1) * (eps / (3 * (Mf + 1)))) by (field; lra).
      apply Qmult_le_compat_r; [lra | exact Hznn]. }
    assert (Hnn : 0 <= Qabs h) by apply Qabs_nonneg.
    assert (Hcomm : Mf * (eps2 * Qabs h) == Mf * eps2 * Qabs h) by ring.
    setoid_rewrite Hcomm.
    apply Qmult_le_compat_r; [exact Hsub | exact Hnn]. }
  assert (Hterm3 : (Mf' + eps1) * (Mg' + eps2) * (Qabs h * Qabs h) < eps / 3 * Qabs h).
  { (* (Mf'+eps1)*(Mg'+eps2)*|h|² < (Mf'+eps1)*(Mg'+eps2)*d3*|h| ≤ eps/3*|h| *)
    set (X := (Mf' + eps1) * (Mg' + eps2)).
    assert (HX_pos : 0 < X) by (unfold X; apply Qmult_lt_0_compat; lra).
    (* Step 1: |h|*|h| < d3*|h| since |h| < d3 and |h| > 0 *)
    assert (Hh_sq : Qabs h * Qabs h < d3 * Qabs h).
    { apply Qmult_lt_r; [exact Hh_pos | exact Hh_d3]. }
    (* Step 2: X * (|h|*|h|) < X * (d3*|h|) since X > 0 *)
    assert (Hfactor : X * (Qabs h * Qabs h) < X * (d3 * Qabs h)).
    { apply Qmult_lt_l; [exact HX_pos | exact Hh_sq]. }
    (* Step 3: X * d3 <= eps/3 *)
    assert (Hsub : X * d3 <= eps / 3).
    { unfold X, d3.
      assert (HAB_bound : (Mf' + eps1) * (Mg' + eps2) < A * B).
      { unfold A, B.
        assert (Hexpand : (Mf' + eps1 + 1) * (Mg' + eps2 + 1) ==
                           (Mf' + eps1) * (Mg' + eps2) + (Mf' + eps1) + (Mg' + eps2) + 1) by ring.
        lra. }
      assert (Hznn : 0 <= eps / (3 * (A * B))).
      { apply Qle_shift_div_l; [lra |]. rewrite Qmult_0_l. lra. }
      setoid_replace (eps / 3)
        with (A * B * (eps / (3 * (A * B)))) by (field; lra).
      apply Qmult_le_compat_r; [lra | exact Hznn]. }
    (* Step 4: chain X*(d3*|h|) = (X*d3)*|h| <= (eps/3)*|h| *)
    apply Qlt_le_trans with (X * (d3 * Qabs h)).
    { exact Hfactor. }
    assert (Hassoc : X * (d3 * Qabs h) == (X * d3) * Qabs h) by ring.
    setoid_rewrite Hassoc.
    apply Qmult_le_compat_r; [exact Hsub | apply Qabs_nonneg]. }
  (* Total: <= + <= + < gives < *)
  apply Qle_lt_trans with (Qabs (ef * g x) + Qabs (f x * eg) + (Mf' + eps1) * (Mg' + eps2) * (Qabs h * Qabs h)).
  { assert (H : Qabs (Df * Dg) <= (Mf' + eps1) * (Mg' + eps2) * (Qabs h * Qabs h)) by exact HT3.
    lra. }
  assert (Hsum : eps / 3 * Qabs h + eps / 3 * Qabs h + eps / 3 * Qabs h == eps * Qabs h) by (field; lra).
  setoid_rewrite <- Hsum.
  lra.
Qed.

(** L10: Square rule — special case of product rule with g = f *)
Lemma udiff_square : forall (f f' : Q -> Q) (a b Mf Mf' : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x) <= Mf) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  0 <= Mf -> 0 <= Mf' ->
  udiff_on (fun x => f x * f x) (fun x => 2 * f x * f' x) a b.
Proof.
  intros f f' a b Mf Mf' Huf HMf HMf' HMf_nn HMf'_nn.
  assert (Hprod : udiff_on (fun x => f x * f x)
                            (fun x => f' x * f x + f x * f' x) a b).
  { apply (udiff_product f f' f f' a b Mf Mf Mf' Mf'); assumption. }
  apply (udiff_ext (fun x => f x * f x) (fun x => f x * f x)
                   (fun x => f' x * f x + f x * f' x) (fun x => 2 * f x * f' x)
                   a b).
  - exact Hprod.
  - intros x. ring.
  - intros x. ring.
Qed.

(* ========================================================================= *)
(* SECTION 4: INTEGRATION BY PARTS                                            *)
(* ========================================================================= *)

(** L11: FTC for product function *)
Lemma ftc_product : forall (f f' g g' : Q -> Q) (a b Mf Mg Mf' Mg' eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x) <= Mf) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g x) <= Mg) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g' x) <= Mg') ->
  0 <= Mf -> 0 <= Mg -> 0 <= Mf' -> 0 <= Mg' ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' x * g x + f x * g' x) a step (S N) -
          (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a)) <=
    eps * (b - a).
Proof.
  intros f f' g g' a b Mf Mg Mf' Mg' eps Huf Hug HMf HMg HMf' HMg'
         HMf_nn HMg_nn HMf'_nn HMg'_nn Heps.
  assert (Hprod : udiff_on (fun x => f x * g x) (fun x => f' x * g x + f x * g' x) a b).
  { apply (udiff_product f f' g g' a b Mf Mg Mf' Mg'); assumption. }
  exact (ftc_grid _ _ a b eps Hprod Heps).
Qed.

(** L12: Integration by parts.
    ∫f'g ≈ f*g|_a^b - ∫f*g'
    Stated as: |RS(f'g) - (fg(end) - fg(a)) + RS(fg')| ≤ eps*(b-a) *)
Lemma integration_by_parts :
  forall (f f' g g' : Q -> Q) (a b Mf Mg Mf' Mg' eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x) <= Mf) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g x) <= Mg) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g' x) <= Mg') ->
  0 <= Mf -> 0 <= Mg -> 0 <= Mf' -> 0 <= Mg' ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' x * g x) a step (S N) -
          (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a) +
          riemann_sum (fun x => f x * g' x) a step (S N)) <=
    eps * (b - a).
Proof.
  intros f f' g g' a b Mf Mg Mf' Mg' eps Huf Hug HMf HMg HMf' HMg'
         HMf_nn HMg_nn HMf'_nn HMg'_nn Heps.
  destruct (ftc_product f f' g g' a b Mf Mg Mf' Mg' eps
              Huf Hug HMf HMg HMf' HMg' HMf_nn HMg_nn HMf'_nn HMg'_nn Heps)
    as [N HN].
  exists N.
  simpl in HN |- *.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* Use set to abstract terms for qabs_rw *)
  set (RS_sum := riemann_sum (fun x => f' x * g x + f x * g' x) a step (S N)) in *.
  set (RS_fg := riemann_sum (fun x => f' x * g x) a step (S N)) in *.
  set (RS_fgp := riemann_sum (fun x => f x * g' x) a step (S N)) in *.
  set (fg_end := f (walk_point a step (S N)) * g (walk_point a step (S N))) in *.
  set (fg_a := f a * g a) in *.
  (* RS(f'g + fg') == RS(f'g) + RS(fg') *)
  assert (Hadd : RS_sum == RS_fg + RS_fgp).
  { apply riemann_sum_add. }
  (* Goal: |RS_fg - (fg_end - fg_a) + RS_fgp| ≤ eps*(b-a) *)
  (* HN:  |RS_sum - (fg_end - fg_a)| ≤ eps*(b-a) *)
  assert (Habs_eq : Qabs (RS_fg - (fg_end - fg_a) + RS_fgp) ==
                     Qabs (RS_sum - (fg_end - fg_a))).
  { apply Qabs_wd. lra. }
  apply Qle_trans with (Qabs (RS_sum - (fg_end - fg_a))).
  - exact (Qeq_Qle _ _ Habs_eq).
  - exact HN.
Qed.

(** L13: IBP bound — upper bound on |∫f'g|.
    Uses the decomposition RS(f'g) = IBP_remainder + (fg_boundary - RS(fg')),
    giving |RS(f'g)| ≤ |fg_boundary - RS(fg')| + eps*(b-a) *)
Lemma ibp_bound :
  forall (f f' g g' : Q -> Q) (a b Mf Mg Mf' Mg' eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x) <= Mf) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g x) <= Mg) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g' x) <= Mg') ->
  0 <= Mf -> 0 <= Mg -> 0 <= Mf' -> 0 <= Mg' ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' x * g x) a step (S N)) <=
    Qabs (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a -
          riemann_sum (fun x => f x * g' x) a step (S N)) +
    eps * (b - a).
Proof.
  intros f f' g g' a b Mf Mg Mf' Mg' eps Huf Hug HMf HMg HMf' HMg'
         HMf_nn HMg_nn HMf'_nn HMg'_nn Heps.
  destruct (integration_by_parts f f' g g' a b Mf Mg Mf' Mg' eps
              Huf Hug HMf HMg HMf' HMg' HMf_nn HMg_nn HMf'_nn HMg'_nn Heps)
    as [N HN].
  exists N.
  simpl in HN |- *.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* Set the Qabs atom from the goal to ensure consistent atoms *)
  set (QY := Qabs (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a -
                    riemann_sum (fun x => f x * g' x) a step (S N))) in *.
  (* Goal: |RS(f'g)| <= QY + eps*(b-a) *)
  (* HN: |RS(f'g) - bd + RS(fg')| <= eps*(b-a) *)
  (* Key: RS(f'g) = (RS(f'g) - bd + RS(fg')) + (bd - RS(fg')), then triangle *)
  assert (Hdecomp :
    riemann_sum (fun x => f' x * g x) a step (S N) ==
    (riemann_sum (fun x => f' x * g x) a step (S N) -
     (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a) +
     riemann_sum (fun x => f x * g' x) a step (S N)) +
    (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a -
     riemann_sum (fun x => f x * g' x) a step (S N))) by ring.
  apply Qle_trans with
    (Qabs (riemann_sum (fun x => f' x * g x) a step (S N) -
           (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a) +
           riemann_sum (fun x => f x * g' x) a step (S N)) + QY).
  { apply Qle_trans with (Qabs (
      (riemann_sum (fun x => f' x * g x) a step (S N) -
       (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a) +
       riemann_sum (fun x => f x * g' x) a step (S N)) +
      (f (walk_point a step (S N)) * g (walk_point a step (S N)) - f a * g a -
       riemann_sum (fun x => f x * g' x) a step (S N)))).
    - exact (Qeq_Qle _ _ (Qabs_wd _ _ Hdecomp)).
    - unfold QY. apply Qabs_triangle. }
  (* Goal: |X| + QY <= QY + eps*(b-a) with HN: |X| <= eps*(b-a) *)
  assert (Hplus : forall x y z : Q, x <= z -> x + y <= y + z).
  { intros. lra. }
  apply Hplus. exact HN.
Qed.

(** L14: IBP self-application: 2∫f'f ≈ f(end)² - f(a)² *)
Lemma ibp_self :
  forall (f f' : Q -> Q) (a b Mf Mf' eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x) <= Mf) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  0 <= Mf -> 0 <= Mf' ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (2 * riemann_sum (fun x => f' x * f x) a step (S N) -
          (f (walk_point a step (S N)) * f (walk_point a step (S N)) - f a * f a)) <=
    eps * (b - a).
Proof.
  intros f f' a b Mf Mf' eps Huf HMf HMf' HMf_nn HMf'_nn Heps.
  destruct (ftc_product f f' f f' a b Mf Mf Mf' Mf' eps
              Huf Huf HMf HMf HMf' HMf' HMf_nn HMf_nn HMf'_nn HMf'_nn Heps)
    as [N HN].
  exists N.
  simpl in HN |- *.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* RS(f'f + ff') ≈ ff(end) - ff(a) *)
  (* RS(f'f + ff') == RS(f'f) + RS(ff') == 2*RS(f'f) since f'f == ff' pointwise *)
  assert (Hext : riemann_sum (fun x => f x * f' x) a step (S N) ==
                  riemann_sum (fun x => f' x * f x) a step (S N)).
  { apply riemann_sum_ext. intros k Hk. ring. }
  assert (Hadd : riemann_sum (fun x => f' x * f x + f x * f' x) a step (S N) ==
                  riemann_sum (fun x => f' x * f x) a step (S N) +
                  riemann_sum (fun x => f x * f' x) a step (S N)).
  { apply riemann_sum_add. }
  assert (Hdouble : riemann_sum (fun x => f' x * f x + f x * f' x) a step (S N) ==
                     2 * riemann_sum (fun x => f' x * f x) a step (S N)).
  { lra. }
  (* Transfer the bound *)
  assert (Heq :
    riemann_sum (fun x => f' x * f x + f x * f' x) a step (S N) -
    (f (walk_point a step (S N)) * f (walk_point a step (S N)) - f a * f a) ==
    2 * riemann_sum (fun x => f' x * f x) a step (S N) -
    (f (walk_point a step (S N)) * f (walk_point a step (S N)) - f a * f a)).
  { lra. }
  assert (Habs_eq : Qabs (2 * riemann_sum (fun x => f' x * f x) a step (S N) -
                          (f (walk_point a step (S N)) * f (walk_point a step (S N)) - f a * f a)) ==
                     Qabs (riemann_sum (fun x => f' x * f x + f x * f' x) a step (S N) -
                          (f (walk_point a step (S N)) * f (walk_point a step (S N)) - f a * f a))).
  { apply Qabs_wd. lra. }
  apply Qle_trans with
    (Qabs (riemann_sum (fun x => f' x * f x + f x * f' x) a step (S N) -
          (f (walk_point a step (S N)) * f (walk_point a step (S N)) - f a * f a))).
  - exact (Qeq_Qle _ _ Habs_eq).
  - exact HN.
Qed.

(* ========================================================================= *)
(* SECTION 5: DERIVED RULES & APPLICATIONS                                    *)
(* ========================================================================= *)

(** L15: udiff is closed under negation *)
Lemma udiff_negate : forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  udiff_on (fun x => - f x) (fun x => - f' x) a b.
Proof.
  intros f f' a b Huf.
  assert (Hscale : udiff_on (fun x => -(1) * f x) (fun x => -(1) * f' x) a b).
  { apply udiff_scale. exact Huf. }
  apply (udiff_ext (fun x => -(1) * f x) (fun x => - f x)
                   (fun x => -(1) * f' x) (fun x => - f' x) a b).
  - exact Hscale.
  - intros x. ring.
  - intros x. ring.
Qed.

(** L16: udiff is closed under subtraction *)
Lemma udiff_sub : forall (f f' g g' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  udiff_on (fun x => f x - g x) (fun x => f' x - g' x) a b.
Proof.
  intros f f' g g' a b Huf Hug.
  assert (Hneg : udiff_on (fun x => - g x) (fun x => - g' x) a b).
  { apply udiff_negate. exact Hug. }
  assert (Hsum : udiff_on (fun x => f x + (- g x)) (fun x => f' x + (- g' x)) a b).
  { apply udiff_add; assumption. }
  apply (udiff_ext (fun x => f x + - g x) (fun x => f x - g x)
                   (fun x => f' x + - g' x) (fun x => f' x - g' x) a b).
  - exact Hsum.
  - intros x. ring.
  - intros x. ring.
Qed.

(** L17: Antiderivative uniqueness — two functions with the same derivative
    have the same increment (up to approximation). *)
Lemma antiderivative_unique :
  forall (f g h : Q -> Q) (a b eps : Q),
  udiff_on f h a b ->
  udiff_on g h a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs ((f (walk_point a step (S N)) - f a) -
          (g (walk_point a step (S N)) - g a)) <=
    eps * (b - a).
Proof.
  intros f g h a b eps Huf Hug Heps.
  (* Use ftc_grid for (f-g) with derivative (h-h)=0 *)
  assert (Hfg : udiff_on (fun x => f x - g x) (fun x => h x - h x) a b).
  { apply udiff_sub; assumption. }
  assert (Hfg0 : udiff_on (fun x => f x - g x) (fun x => 0) a b).
  { apply (udiff_ext (fun x => f x - g x) (fun x => f x - g x)
                     (fun x => h x - h x) (fun x => 0) a b).
    - exact Hfg.
    - intros x. ring.
    - intros x. ring. }
  destruct (ftc_grid (fun x => f x - g x) (fun _ => 0) a b eps Hfg0 Heps) as [N HN].
  exists N. cbv beta in HN |- *.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* HN: Qabs(RS(0) - (f(end)-g(end) - (f(a)-g(a)))) <= eps*(b-a) *)
  (* Goal: Qabs((f(end)-f(a)) - (g(end)-g(a))) <= eps*(b-a) *)
  assert (Hzero : riemann_sum (fun _ : Q => 0) a step (S N) == 0).
  { assert (Hconst : riemann_sum (fun _ : Q => 0) a step (S N) ==
                      0 * inject_Z (Z.of_nat (S N)) * step) by apply riemann_sum_const.
    lra. }
  assert (Habs_neg : forall q : Q, Qabs (- q) == Qabs q).
  { intros q. destruct (Qlt_le_dec q 0).
    - rewrite (Qabs_neg q) by lra. rewrite (Qabs_pos (-q)) by lra. ring.
    - rewrite (Qabs_pos q) by lra. rewrite (Qabs_neg (-q)) by lra. ring. }
  (* Chain: Qabs(goal) == Qabs(-goal) == Qabs(HN_expr) <= eps*(b-a) *)
  set (ge := (f (walk_point a step (S N)) - f a) -
             (g (walk_point a step (S N)) - g a)).
  assert (Hchain : Qabs ge ==
                    Qabs (riemann_sum (fun _ : Q => 0) a step (S N) -
                          (f (walk_point a step (S N)) - g (walk_point a step (S N)) -
                           (f a - g a)))).
  { transitivity (Qabs (- ge)).
    - symmetry. apply Habs_neg.
    - apply Qabs_wd. unfold ge. lra. }
  apply Qle_trans with (Qabs (riemann_sum (fun _ : Q => 0) a step (S N) -
                               (f (walk_point a step (S N)) - g (walk_point a step (S N)) -
                                (f a - g a)))).
  - exact (Qeq_Qle _ _ Hchain).
  - exact HN.
Qed.

(** L18: IBP with identity function: ∫g ≈ x*g|_a^b - ∫x*g' *)
Lemma ibp_identity :
  forall (g g' : Q -> Q) (a b Mg Mg' Mab eps : Q),
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g x) <= Mg) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (g' x) <= Mg') ->
  (forall x : Q, a <= x -> x <= b -> Qabs x <= Mab) ->
  0 <= Mg -> 0 <= Mg' -> 0 <= Mab ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => 1 * g x) a step (S N) -
          (walk_point a step (S N) * g (walk_point a step (S N)) - a * g a) +
          riemann_sum (fun x => x * g' x) a step (S N)) <=
    eps * (b - a).
Proof.
  intros g g' a b Mg Mg' Mab eps Hug HMg HMg' HMab HMg_nn HMg'_nn HMab_nn Heps.
  (* udiff_on for identity: from affine_udiff with c=1, d=0 *)
  assert (Hab : a < b).
  { destruct Hug as [Hab _]. exact Hab. }
  assert (Hid : udiff_on (fun x => 1 * x + 0) (fun _ => 1) a b).
  { apply affine_udiff. exact Hab. }
  assert (Hid' : udiff_on (fun x => x) (fun _ => 1) a b).
  { apply (udiff_ext (fun x => 1 * x + 0) (fun x => x)
                     (fun _ : Q => 1) (fun _ : Q => 1) a b).
    - exact Hid.
    - intros x. ring.
    - intros x. ring. }
  (* Bounds for identity: |x| ≤ Mab, |1| ≤ 1 *)
  assert (HM1 : forall x : Q, a <= x -> x <= b -> Qabs (1 : Q) <= 1).
  { intros x _ _. rewrite Qabs_pos; lra. }
  (* Apply integration_by_parts *)
  assert (Hibp := integration_by_parts
    (fun x => x) (fun _ => 1) g g' a b Mab Mg 1 Mg' eps
    Hid' Hug HMab HMg HM1 HMg' HMab_nn HMg_nn).
  assert (H1nn : (0 : Q) <= 1) by lra.
  specialize (Hibp H1nn HMg'_nn Heps).
  destruct Hibp as [N HN].
  exists N.
  simpl in HN |- *.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* RS(1*g) and RS(x*g') — need to match *)
  exact HN.
Qed.
