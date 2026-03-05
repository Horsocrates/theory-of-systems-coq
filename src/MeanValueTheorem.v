(* ========================================================================= *)
(*      MEAN VALUE THEOREM — GRID MVT, MONOTONICITY, LIPSCHITZ             *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove MVT consequences via walk-point telescoping:             *)
(*    - Bounded derivative ⟹ bounded increment                             *)
(*    - Zero derivative ⟹ near-constant                                    *)
(*    - Positive/negative derivative ⟹ increasing/decreasing               *)
(*    - Lipschitz condition from bounded derivative                        *)
(*    Walk-point Fixpoint ensures Leibniz-exact chaining, avoiding         *)
(*    the Q Qeq-vs-Leibniz issue for intermediate f-values.               *)
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

Open Scope Q_scope.

(* ========================================================================= *)
(* DEFINITIONS                                                                *)
(* ========================================================================= *)

(** Walk points: x, x+s, (x+s)+s, ... — Leibniz-exact chaining *)
Fixpoint walk_point (x step : Q) (n : nat) : Q :=
  match n with
  | O => x
  | S n' => walk_point x step n' + step
  end.

(** Uniform differentiability on interval [a,b]:
    single delta works for ALL points in the interval *)
Definition udiff_on (f f' : Q -> Q) (a b : Q) : Prop :=
  a < b /\
  forall eps : Q, 0 < eps ->
  exists delta : Q, 0 < delta /\
  forall x h : Q, a <= x -> x <= b ->
    0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x - f' x * h) < eps * Qabs h.

(* ========================================================================= *)
(* SECTION 1: WALK INFRASTRUCTURE                                            *)
(* ========================================================================= *)

(** L1: Walk point equals base + n * step (as Qeq) *)
Lemma walk_point_qeq : forall (x s : Q) (n : nat),
  walk_point x s n == x + inject_Z (Z.of_nat n) * s.
Proof.
  intros x s n. induction n as [| n' IH].
  - simpl. ring.
  - simpl walk_point. rewrite IH.
    assert (Hinj : inject_Z (Z.of_nat (S n')) == inject_Z (Z.of_nat n') + 1).
    { replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z by lia.
      rewrite inject_Z_plus. reflexivity. }
    rewrite Hinj. ring.
Qed.

(** L2: Walk points stay in [a,b] when step = (b-a)/(S N) *)
Lemma walk_point_in_interval : forall (a b : Q) (N : nat) (k : nat),
  a < b ->
  let step := (b - a) / inject_Z (Z.of_nat (S N)) in
  (k <= S N)%nat ->
  a <= walk_point a step k /\ walk_point a step k <= b.
Proof.
  intros a b N k Hab step Hk.
  assert (Hwalk : walk_point a step k == a + inject_Z (Z.of_nat k) * step).
  { apply walk_point_qeq. }
  assert (HSN_pos : (0 < Z.of_nat (S N))%Z) by lia.
  assert (HSN_Qpos : 0 < inject_Z (Z.of_nat (S N))).
  { unfold Qlt. simpl. lia. }
  assert (Hba : 0 < b - a) by lra.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l; [exact HSN_Qpos | lra]. }
  assert (Hk_le : inject_Z (Z.of_nat k) <= inject_Z (Z.of_nat (S N))).
  { unfold Qle. simpl. lia. }
  assert (Hk_nn : 0 <= inject_Z (Z.of_nat k)).
  { unfold Qle. simpl. lia. }
  split.
  - (* a <= walk_point a step k *)
    rewrite Hwalk.
    assert (H : 0 <= inject_Z (Z.of_nat k) * step).
    { apply Qmult_le_0_compat; [exact Hk_nn | apply Qlt_le_weak; exact Hstep_pos]. }
    lra.
  - (* walk_point a step k <= b *)
    rewrite Hwalk.
    assert (Hcancel : inject_Z (Z.of_nat (S N)) * step == b - a).
    { unfold step. field.
      intros Hcontra. rewrite Hcontra in HSN_Qpos. lra. }
    assert (H1 : inject_Z (Z.of_nat k) * step <= inject_Z (Z.of_nat (S N)) * step).
    { assert (Hdiff : 0 <= (inject_Z (Z.of_nat (S N)) - inject_Z (Z.of_nat k)) * step).
      { apply Qmult_le_0_compat; [lra | apply Qlt_le_weak; exact Hstep_pos]. }
      assert (Hring : (inject_Z (Z.of_nat (S N)) - inject_Z (Z.of_nat k)) * step ==
                        inject_Z (Z.of_nat (S N)) * step - inject_Z (Z.of_nat k) * step) by ring.
      lra. }
    assert (H2 : inject_Z (Z.of_nat k) * step <= b - a).
    { apply Qle_trans with (y := inject_Z (Z.of_nat (S N)) * step); [exact H1 |].
      rewrite Hcancel. apply Qle_refl. }
    lra.
Qed.

(** L3: Grid step is positive *)
Lemma walk_step_pos : forall (a b : Q) (N : nat),
  a < b -> 0 < (b - a) / inject_Z (Z.of_nat (S N)).
Proof.
  intros a b N Hab.
  assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
  { unfold Qlt. simpl. lia. }
  apply Qlt_shift_div_l; [exact HSN_pos | lra].
Qed.

(** L4: Grid step can be made arbitrarily small *)
Lemma walk_step_small : forall (a b : Q) (delta : Q),
  a < b -> 0 < delta ->
  exists N : nat, (b - a) / inject_Z (Z.of_nat (S N)) < delta.
Proof.
  intros a b delta Hab Hdelta.
  assert (Hba : b - a > 0) by lra.
  destruct (Archimedean_nat (b - a) delta Hba Hdelta) as [M [HM_pos HM]].
  destruct M as [| M'].
  - lia.
  - exists M'.
    assert (HSM : inject_Z (Z.of_nat (S M')) > 0).
    { unfold Qlt. simpl. lia. }
    exact HM.
Qed.

(* ========================================================================= *)
(* SECTION 2: SINGLE-STEP BOUNDS                                             *)
(* ========================================================================= *)

(** L5: Uniform differentiability implies pointwise differentiability *)
Lemma udiff_pointwise : forall (f f' : Q -> Q) (a b x : Q),
  udiff_on f f' a b -> a <= x -> x <= b ->
  has_derivative f x (f' x).
Proof.
  intros f f' a b x [Hab Hudiff] Hax Hxb eps Heps.
  destruct (Hudiff eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  exact (Hbound x h Hax Hxb Hh_pos Hh_lt).
Qed.

(** L6: Upper bound on single step from derivative *)
Lemma step_upper_bound : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L ->
  forall eps : Q, 0 < eps ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x) <= (Qabs L + eps) * Qabs h.
Proof.
  intros f x L Hderiv eps Heps.
  destruct (Hderiv eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  specialize (Hbound h Hh_pos Hh_lt).
  (* |f(x+h) - f(x)| = |(f(x+h) - f(x) - L*h) + L*h| ≤ |err| + |L*h| *)
  assert (Hdecomp : f (x + h) - f x == (f (x + h) - f x - L * h) + L * h) by ring.
  assert (Htri : Qabs (f (x + h) - f x) <=
                  Qabs (f (x + h) - f x - L * h) + Qabs (L * h)).
  { qabs_rw Hdecomp. apply Qabs_triangle. }
  rewrite Qabs_Qmult in Htri.
  assert (Herr_le : Qabs (f (x + h) - f x - L * h) <= eps * Qabs h).
  { apply Qlt_le_weak. exact Hbound. }
  assert (Hring : eps * Qabs h + Qabs L * Qabs h == (Qabs L + eps) * Qabs h) by ring.
  lra.
Qed.

(** L7: Lower bound on single step when derivative is positive *)
Lemma step_lower_bound : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L -> 0 < L ->
  forall eps : Q, 0 < eps -> eps < L ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < h -> h < delta ->
    f (x + h) - f x > (L - eps) * h.
Proof.
  intros f x L Hderiv HL eps Heps HepsL.
  destruct (Hderiv eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  assert (Hh_abs : Qabs h == h).
  { rewrite Qabs_pos; lra. }
  assert (Hh_abs_pos : 0 < Qabs h).
  { rewrite Hh_abs. exact Hh_pos. }
  assert (Hh_abs_lt : Qabs h < delta).
  { rewrite Hh_abs. exact Hh_lt. }
  specialize (Hbound h Hh_abs_pos Hh_abs_lt).
  (* -|err| ≤ err, so err > -eps*h *)
  assert (Hge_err : -(Qabs (f (x + h) - f x - L * h)) <=
                     f (x + h) - f x - L * h).
  { destruct (Qlt_le_dec (f (x + h) - f x - L * h) 0).
    - rewrite Qabs_neg; [| lra]. lra.
    - rewrite Qabs_pos; lra. }
  assert (Heps_h : eps * Qabs h == eps * h).
  { rewrite Hh_abs. reflexivity. }
  (* err > -eps*h, so f(x+h)-f(x) > L*h - eps*h *)
  assert (Hring : (L - eps) * h == L * h - eps * h) by ring.
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: THE GRID MVT CONSEQUENCES                                      *)
(* ========================================================================= *)

(** L8: Bounded derivative implies bounded increment — THE MAIN THEOREM *)
Lemma bounded_deriv_bounded_increment :
  forall (f f' : Q -> Q) (a b M eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a) <= (M + eps) * (b - a).
Proof.
  intros f f' a b M eps [Hab Hudiff] Hbound Heps.
  assert (Hba : 0 < b - a) by lra.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hudiff (eps * (1#2)) Heps2) as [delta [Hdelta Hbd]].
  destruct (walk_step_small a b delta Hab Hdelta) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hstep_abs : Qabs step == step).
  { rewrite Qabs_pos; lra. }
  assert (Hstep_abs_pos : 0 < Qabs step).
  { rewrite Hstep_abs. exact Hstep_pos. }
  assert (Hstep_lt : Qabs step < delta).
  { rewrite Hstep_abs. exact HN. }
  (* Induction: |f(y_k) - f(a)| ≤ k * (M + eps/2) * step for k ≤ S N *)
  assert (Hmain : forall k : nat, (k <= S N)%nat ->
    Qabs (f (walk_point a step k) - f a) <=
    inject_Z (Z.of_nat k) * (M + eps * (1#2)) * step).
  { induction k as [| k' IHk].
    - intros _. simpl.
      assert (Hzero : f a - f a == 0) by ring.
      qabs_rw Hzero. rewrite Qabs_pos; [| lra].
      assert (H0 : inject_Z (Z.of_nat 0) * (M + eps * (1#2)) * step == 0).
      { simpl. ring. }
      setoid_rewrite H0. lra.
    - intros Hk. assert (Hk' : (k' <= S N)%nat) by lia.
      specialize (IHk Hk').
      (* y_{k'+1} = y_{k'} + step, by Leibniz *)
      assert (Hdecomp : f (walk_point a step (S k')) - f a ==
                          (f (walk_point a step k' + step) - f (walk_point a step k')) +
                          (f (walk_point a step k') - f a)).
      { simpl. ring. }
      assert (Htri : Qabs (f (walk_point a step (S k')) - f a) <=
                       Qabs (f (walk_point a step k' + step) - f (walk_point a step k')) +
                       Qabs (f (walk_point a step k') - f a)).
      { qabs_rw Hdecomp. apply Qabs_triangle. }
      (* Bound the new step *)
      assert (Hin : a <= walk_point a step k' /\ walk_point a step k' <= b).
      { apply walk_point_in_interval; [exact Hab | exact Hk']. }
      destruct Hin as [Hlo Hhi].
      specialize (Hbd (walk_point a step k') step Hlo Hhi Hstep_abs_pos Hstep_lt).
      (* |f(y+step) - f(y) - f'(y)*step| < eps/2 * |step| *)
      (* |f(y+step) - f(y)| ≤ |f'(y)|*|step| + eps/2*|step| *)
      assert (Hstep_decomp : f (walk_point a step k' + step) - f (walk_point a step k') ==
                               (f (walk_point a step k' + step) - f (walk_point a step k') -
                                f' (walk_point a step k') * step) +
                               f' (walk_point a step k') * step) by ring.
      assert (Htri2 : Qabs (f (walk_point a step k' + step) - f (walk_point a step k')) <=
                        Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                              f' (walk_point a step k') * step) +
                        Qabs (f' (walk_point a step k') * step)).
      { qabs_rw Hstep_decomp. apply Qabs_triangle. }
      rewrite Qabs_Qmult in Htri2.
      assert (Herr_le : Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step) <=
                          eps * (1#2) * Qabs step).
      { apply Qlt_le_weak. exact Hbd. }
      assert (Hfp_le : Qabs (f' (walk_point a step k')) <= M).
      { apply Hbound; [exact Hlo | exact Hhi]. }
      (* |f'(y)| * |step| ≤ M * step *)
      assert (HfpM : Qabs (f' (walk_point a step k')) * Qabs step <= M * Qabs step).
      { assert (Hdiff : 0 <= (M - Qabs (f' (walk_point a step k'))) * Qabs step).
        { apply Qmult_le_0_compat; [lra | apply Qabs_nonneg]. }
        assert (Hring : (M - Qabs (f' (walk_point a step k'))) * Qabs step ==
                          M * Qabs step - Qabs (f' (walk_point a step k')) * Qabs step) by ring.
        lra. }
      (* Combine: new step ≤ (M + eps/2) * |step| = (M + eps/2) * step *)
      assert (Hnew : Qabs (f (walk_point a step k' + step) - f (walk_point a step k')) <=
                       (M + eps * (1#2)) * step).
      { assert (H1 : eps * (1#2) * Qabs step + Qabs (f' (walk_point a step k')) * Qabs step <=
                       eps * (1#2) * Qabs step + M * Qabs step) by lra.
        assert (H2 : eps * (1#2) * Qabs step + M * Qabs step == (M + eps * (1#2)) * Qabs step) by ring.
        assert (H3 : (M + eps * (1#2)) * Qabs step == (M + eps * (1#2)) * step).
        { setoid_rewrite Hstep_abs. reflexivity. }
        lra. }
      (* Total *)
      assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      assert (Hring : (inject_Z (Z.of_nat k') + 1) * (M + eps * (1#2)) * step ==
                        inject_Z (Z.of_nat k') * (M + eps * (1#2)) * step +
                        (M + eps * (1#2)) * step) by ring.
      setoid_rewrite Hinj. lra. }
  (* Apply at k = S N *)
  specialize (Hmain (S N) (Nat.le_refl _)).
  (* inject_Z(S N) * (M + eps/2) * step == (M + eps/2) * (b-a) *)
  assert (Hcancel : inject_Z (Z.of_nat (S N)) * (M + eps * (1#2)) * step ==
                     (M + eps * (1#2)) * (b - a)).
  { unfold step. field.
    intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  assert (Hfinal : (M + eps * (1#2)) * (b - a) <= (M + eps) * (b - a)).
  { assert (Hdiff : 0 <= (eps - eps * (1#2)) * (b - a)).
    { apply Qmult_le_0_compat; lra. }
    assert (Hring2 : (eps - eps * (1#2)) * (b - a) == (M + eps) * (b - a) - (M + eps * (1#2)) * (b - a)) by ring.
    lra. }
  setoid_rewrite Hcancel in Hmain.
  apply Qle_trans with (y := (M + eps * (1#2)) * (b - a));
    [exact Hmain | exact Hfinal].
Qed.

(** L9: Zero derivative means near-constant *)
Lemma zero_deriv_near_constant :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' x == 0) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a) <= eps * (b - a).
Proof.
  intros f f' a b eps Hudiff Hzero Heps.
  assert (HM : forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= 0).
  { intros x Hax Hxb.
    specialize (Hzero x Hax Hxb).
    assert (H : Qabs (f' x) == Qabs 0).
    { apply Qabs_wd. exact Hzero. }
    rewrite H. rewrite Qabs_pos; lra. }
  destruct (bounded_deriv_bounded_increment f f' a b 0 eps Hudiff HM Heps) as [N HN].
  exists N. simpl in HN |- *. lra.
Qed.

(** L10: Positive derivative implies function increases *)
Lemma pos_deriv_increases :
  forall (f f' : Q -> Q) (a b c : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> c <= f' x) ->
  0 < c ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    0 < f (walk_point a step (S N)) - f a.
Proof.
  intros f f' a b c [Hab Hudiff] Hlo Hc.
  assert (Hba : 0 < b - a) by lra.
  assert (Hc2 : 0 < c * (1#2)) by lra.
  destruct (Hudiff (c * (1#2)) Hc2) as [delta [Hdelta Hbd]].
  destruct (walk_step_small a b delta Hab Hdelta) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hstep_abs : Qabs step == step).
  { rewrite Qabs_pos; lra. }
  assert (Hstep_abs_pos : 0 < Qabs step).
  { rewrite Hstep_abs. exact Hstep_pos. }
  assert (Hstep_lt : Qabs step < delta).
  { rewrite Hstep_abs. exact HN. }
  (* Induction: f(y_k) - f(a) ≥ k * (c/2) * step *)
  assert (Hmain : forall k : nat, (k <= S N)%nat ->
    inject_Z (Z.of_nat k) * (c * (1#2)) * step <= f (walk_point a step k) - f a).
  { induction k as [| k' IHk].
    - intros _. simpl. ring_simplify. lra.
    - intros Hk. assert (Hk' : (k' <= S N)%nat) by lia.
      specialize (IHk Hk').
      (* f(y_{k'+1}) - f(a) = [f(y_{k'}+step) - f(y_{k'})] + [f(y_{k'}) - f(a)] *)
      assert (Hsum : f (walk_point a step (S k')) - f a ==
                       (f (walk_point a step k' + step) - f (walk_point a step k')) +
                       (f (walk_point a step k') - f a)).
      { simpl. ring. }
      (* Bound the new step from below *)
      assert (Hin : a <= walk_point a step k' /\ walk_point a step k' <= b).
      { apply walk_point_in_interval; [exact Hab | exact Hk']. }
      destruct Hin as [Hlo_k Hhi_k].
      specialize (Hbd (walk_point a step k') step Hlo_k Hhi_k Hstep_abs_pos Hstep_lt).
      (* |f(y+step) - f(y) - f'(y)*step| < (c/2)*|step| *)
      (* f(y+step) - f(y) - f'(y)*step > -(c/2)*step *)
      assert (Hle_err : f (walk_point a step k' + step) - f (walk_point a step k') -
                          f' (walk_point a step k') * step <=
                         Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step)).
      { destruct (Qlt_le_dec (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step) 0).
        - rewrite Qabs_neg; [| lra]. lra.
        - rewrite Qabs_pos; lra. }
      (* err > -(c/2)*step *)
      assert (Hbd2 : Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                            f' (walk_point a step k') * step) < c * (1#2) * step).
      { assert (Heq : c * (1#2) * Qabs step == c * (1#2) * step).
        { rewrite Hstep_abs. reflexivity. }
        lra. }
      assert (Hge_err : -(Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step)) <=
                         f (walk_point a step k' + step) - f (walk_point a step k') -
                          f' (walk_point a step k') * step).
      { destruct (Qlt_le_dec (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step) 0).
        - rewrite Qabs_neg; [| lra]. lra.
        - rewrite Qabs_pos; lra. }
      assert (Herr_lo : f (walk_point a step k' + step) - f (walk_point a step k') -
                          f' (walk_point a step k') * step > -(c * (1#2)) * step).
      { lra. }
      (* f'(y)*step ≥ c*step *)
      assert (Hfp : c <= f' (walk_point a step k')).
      { apply Hlo; [exact Hlo_k | exact Hhi_k]. }
      assert (Hfp_step : c * step <= f' (walk_point a step k') * step).
      { assert (Hdiff : 0 <= (f' (walk_point a step k') - c) * step).
        { apply Qmult_le_0_compat; [lra | apply Qlt_le_weak; exact Hstep_pos]. }
        assert (Hring : (f' (walk_point a step k') - c) * step ==
                          f' (walk_point a step k') * step - c * step) by ring.
        lra. }
      (* f(y+step) - f(y) > f'(y)*step - (c/2)*step ≥ c*step - (c/2)*step = (c/2)*step *)
      assert (Hnew : f (walk_point a step k' + step) - f (walk_point a step k') >=
                       c * (1#2) * step).
      { lra. }
      (* Total *)
      assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      assert (Hring : (inject_Z (Z.of_nat k') + 1) * (c * (1#2)) * step ==
                        inject_Z (Z.of_nat k') * (c * (1#2)) * step +
                        c * (1#2) * step) by ring.
      rewrite Hsum. setoid_rewrite Hinj. lra. }
  (* Apply at k = S N *)
  specialize (Hmain (S N) (Nat.le_refl _)).
  assert (Hcancel : inject_Z (Z.of_nat (S N)) * (c * (1#2)) * step ==
                     c * (1#2) * (b - a)).
  { unfold step. field.
    intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  setoid_rewrite Hcancel in Hmain.
  assert (Hpos : 0 < c * (1#2) * (b - a)).
  { apply Qmult_lt_0_compat; [lra | exact Hba]. }
  apply Qlt_le_trans with (c * (1#2) * (b - a)); assumption.
Qed.

(** L11: Negative derivative implies function decreases *)
Lemma neg_deriv_decreases :
  forall (f f' : Q -> Q) (a b c : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' x <= - c) ->
  0 < c ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    f (walk_point a step (S N)) - f a < 0.
Proof.
  intros f f' a b c [Hab Hudiff] Hhi Hc.
  assert (Hba : 0 < b - a) by lra.
  assert (Hc2 : 0 < c * (1#2)) by lra.
  destruct (Hudiff (c * (1#2)) Hc2) as [delta [Hdelta Hbd]].
  destruct (walk_step_small a b delta Hab Hdelta) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hstep_abs : Qabs step == step).
  { rewrite Qabs_pos; lra. }
  assert (Hstep_abs_pos : 0 < Qabs step).
  { rewrite Hstep_abs. exact Hstep_pos. }
  assert (Hstep_lt : Qabs step < delta).
  { rewrite Hstep_abs. exact HN. }
  (* Induction: f(y_k) - f(a) ≤ -k * (c/2) * step *)
  assert (Hmain : forall k : nat, (k <= S N)%nat ->
    f (walk_point a step k) - f a <= -(inject_Z (Z.of_nat k) * (c * (1#2)) * step)).
  { induction k as [| k' IHk].
    - intros _. simpl. ring_simplify. lra.
    - intros Hk. assert (Hk' : (k' <= S N)%nat) by lia.
      specialize (IHk Hk').
      assert (Hsum : f (walk_point a step (S k')) - f a ==
                       (f (walk_point a step k' + step) - f (walk_point a step k')) +
                       (f (walk_point a step k') - f a)).
      { simpl. ring. }
      assert (Hin : a <= walk_point a step k' /\ walk_point a step k' <= b).
      { apply walk_point_in_interval; [exact Hab | exact Hk']. }
      destruct Hin as [Hlo_k Hhi_k].
      specialize (Hbd (walk_point a step k') step Hlo_k Hhi_k Hstep_abs_pos Hstep_lt).
      (* Upper bound on err: err ≤ |err| *)
      assert (Hle_err : f (walk_point a step k' + step) - f (walk_point a step k') -
                          f' (walk_point a step k') * step <=
                         Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step)).
      { destruct (Qlt_le_dec (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step) 0).
        - rewrite Qabs_neg; [| lra]. lra.
        - rewrite Qabs_pos; lra. }
      assert (Hbd2 : Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                            f' (walk_point a step k') * step) < c * (1#2) * step).
      { assert (Heq : c * (1#2) * Qabs step == c * (1#2) * step).
        { rewrite Hstep_abs. reflexivity. }
        lra. }
      (* f(y+step) - f(y) < f'(y)*step + (c/2)*step ≤ -c*step + (c/2)*step = -(c/2)*step *)
      assert (Hfp : f' (walk_point a step k') <= -c).
      { apply Hhi; [exact Hlo_k | exact Hhi_k]. }
      assert (Hfp_step : f' (walk_point a step k') * step <= -(c * step)).
      { assert (Hdiff : 0 <= (-(f' (walk_point a step k')) - c) * step).
        { apply Qmult_le_0_compat; [lra | apply Qlt_le_weak; exact Hstep_pos]. }
        assert (Hring : (-(f' (walk_point a step k')) - c) * step ==
                          -(f' (walk_point a step k') * step) - c * step) by ring.
        lra. }
      assert (Hnew : f (walk_point a step k' + step) - f (walk_point a step k') <=
                       -(c * (1#2)) * step).
      { lra. }
      assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      assert (Hring : -((inject_Z (Z.of_nat k') + 1) * (c * (1#2)) * step) ==
                        -(inject_Z (Z.of_nat k') * (c * (1#2)) * step) +
                        -(c * (1#2) * step)) by ring.
      rewrite Hsum. setoid_rewrite Hinj. lra. }
  specialize (Hmain (S N) (Nat.le_refl _)).
  assert (Hcancel : inject_Z (Z.of_nat (S N)) * (c * (1#2)) * step ==
                     c * (1#2) * (b - a)).
  { unfold step. field.
    intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  setoid_rewrite Hcancel in Hmain.
  assert (Hneg : -(c * (1#2) * (b - a)) < 0).
  { assert (Hpos : 0 < c * (1#2) * (b - a)).
    { apply Qmult_lt_0_compat; [lra | exact Hba]. }
    lra. }
  apply Qle_lt_trans with (-(c * (1#2) * (b - a))); assumption.
Qed.

(* ========================================================================= *)
(* SECTION 4: LIPSCHITZ AND CONTINUITY                                        *)
(* ========================================================================= *)

(** L12: Uniform differentiability implies continuity at each point *)
Lemma udiff_continuous_at : forall (f f' : Q -> Q) (a b x : Q),
  udiff_on f f' a b -> a <= x -> x <= b ->
  continuous_at f x.
Proof.
  intros f f' a b x Hudiff Hax Hxb.
  apply deriv_implies_continuous with (L := f' x).
  exact (udiff_pointwise f f' a b x Hudiff Hax Hxb).
Qed.

(** L13: Nonnegative derivative implies approximately nondecreasing *)
Lemma nonneg_deriv_approx_nondec :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> 0 <= f' x) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    -(eps * (b - a)) <= f (walk_point a step (S N)) - f a.
Proof.
  intros f f' a b eps [Hab Hudiff] Hnn Heps.
  assert (Hba : 0 < b - a) by lra.
  destruct (Hudiff eps Heps) as [delta [Hdelta Hbd]].
  destruct (walk_step_small a b delta Hab Hdelta) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hstep_abs : Qabs step == step).
  { rewrite Qabs_pos; lra. }
  assert (Hstep_abs_pos : 0 < Qabs step).
  { rewrite Hstep_abs. exact Hstep_pos. }
  assert (Hstep_lt : Qabs step < delta).
  { rewrite Hstep_abs. exact HN. }
  (* Induction: f(y_k) - f(a) ≥ -k * eps * step *)
  assert (Hmain : forall k : nat, (k <= S N)%nat ->
    -(inject_Z (Z.of_nat k) * eps * step) <= f (walk_point a step k) - f a).
  { induction k as [| k' IHk].
    - intros _. simpl. ring_simplify. lra.
    - intros Hk. assert (Hk' : (k' <= S N)%nat) by lia.
      specialize (IHk Hk').
      assert (Hsum : f (walk_point a step (S k')) - f a ==
                       (f (walk_point a step k' + step) - f (walk_point a step k')) +
                       (f (walk_point a step k') - f a)).
      { simpl. ring. }
      assert (Hin : a <= walk_point a step k' /\ walk_point a step k' <= b).
      { apply walk_point_in_interval; [exact Hab | exact Hk']. }
      destruct Hin as [Hlo_k Hhi_k].
      specialize (Hbd (walk_point a step k') step Hlo_k Hhi_k Hstep_abs_pos Hstep_lt).
      (* f(y+step) - f(y) > f'(y)*step - eps*step ≥ 0 - eps*step = -eps*step *)
      assert (Hge_err : -(Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step)) <=
                         f (walk_point a step k' + step) - f (walk_point a step k') -
                          f' (walk_point a step k') * step).
      { destruct (Qlt_le_dec (f (walk_point a step k' + step) - f (walk_point a step k') -
                               f' (walk_point a step k') * step) 0).
        - rewrite Qabs_neg; [| lra]. lra.
        - rewrite Qabs_pos; lra. }
      assert (Hbd2 : Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                            f' (walk_point a step k') * step) < eps * step).
      { assert (Heq : eps * Qabs step == eps * step).
        { rewrite Hstep_abs. reflexivity. }
        lra. }
      assert (Hfp_nn : 0 <= f' (walk_point a step k')).
      { apply Hnn; [exact Hlo_k | exact Hhi_k]. }
      assert (Hfp_step : 0 <= f' (walk_point a step k') * step).
      { apply Qmult_le_0_compat; [exact Hfp_nn | apply Qlt_le_weak; exact Hstep_pos]. }
      assert (Hnew : f (walk_point a step k' + step) - f (walk_point a step k') >=
                       -(eps * step)).
      { lra. }
      assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      assert (Hring : -((inject_Z (Z.of_nat k') + 1) * eps * step) ==
                        -(inject_Z (Z.of_nat k') * eps * step) + -(eps * step)) by ring.
      rewrite Hsum. setoid_rewrite Hinj. lra. }
  specialize (Hmain (S N) (Nat.le_refl _)).
  assert (Hcancel : inject_Z (Z.of_nat (S N)) * eps * step == eps * (b - a)).
  { unfold step. field.
    intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  setoid_rewrite Hcancel in Hmain. exact Hmain.
Qed.

(** L14: Local Lipschitz from derivative — single step *)
Lemma bounded_deriv_lipschitz_local : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x) <= (Qabs L + 1) * Qabs h.
Proof.
  intros f x L Hderiv.
  destruct (step_upper_bound f x L Hderiv 1 (eq_refl : 0 < 1)) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta |].
  exact Hbd.
Qed.

(** L15: Walk endpoint equals b (as Qeq) *)
Lemma walk_endpoint_qeq : forall (a b : Q) (N : nat),
  a < b ->
  walk_point a ((b - a) / inject_Z (Z.of_nat (S N))) (S N) == b.
Proof.
  intros a b N Hab.
  rewrite walk_point_qeq.
  assert (HSN_nz : ~ inject_Z (Z.of_nat (S N)) == 0).
  { intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  field. exact HSN_nz.
Qed.

(* ========================================================================= *)
(* SECTION 5: EXACT CASES AND APPLICATIONS                                    *)
(* ========================================================================= *)

(** L16: Affine functions are uniformly differentiable *)
Lemma affine_udiff : forall (c d a b : Q),
  a < b ->
  udiff_on (fun w => c * w + d) (fun _ => c) a b.
Proof.
  intros c d a b Hab.
  split; [exact Hab |].
  intros eps Heps.
  exists 1. split; [lra |].
  intros x h Hax Hxb Hh_pos Hh_lt.
  assert (Herr : c * (x + h) + d - (c * x + d) - c * h == 0) by ring.
  qabs_rw Herr. rewrite Qabs_pos; [| lra].
  apply Qmult_lt_0_compat; [exact Heps | exact Hh_pos].
Qed.

(** L17: Quadratic function is uniformly differentiable *)
Lemma quadratic_udiff : forall (a b : Q),
  a < b ->
  udiff_on (fun w => w * w) (fun w => 2 * w) a b.
Proof.
  intros a b Hab.
  split; [exact Hab |].
  intros eps Heps.
  exists eps. split; [exact Heps |].
  intros x h Hax Hxb Hh_pos Hh_lt.
  (* error = |(x+h)*(x+h) - x*x - 2*x*h| = |h*h| = |h|^2 *)
  assert (Herr : (x + h) * (x + h) - x * x - 2 * x * h == h * h) by ring.
  qabs_rw Herr. rewrite Qabs_Qmult.
  (* |h|*|h| < eps*|h| since |h| < eps *)
  apply Qmult_lt_compat_r; [exact Hh_pos | exact Hh_lt].
Qed.

(** L18: Exact MVT for quadratic — midpoint satisfies f'(c)*(b-a) = f(b)-f(a) *)
Lemma mvt_quadratic_midpoint : forall (a b : Q),
  2 * ((a + b) * (1#2)) * (b - a) == b * b - a * a.
Proof.
  intros a b. ring.
Qed.
