(* ========================================================================= *)
(*     FTC.v -- Fundamental Theorem of Calculus Extensions                  *)
(*                                                                          *)
(*  Theory of Systems -- Analysis Gap Closure (Phase 0)                     *)
(*                                                                          *)
(*  Extends existing ftc_grid with Lipschitz theory, u-substitution,        *)
(*  and monotonicity consequences. Stays in walk_point framework.           *)
(*                                                                          *)
(*  Elements: functions, derivatives, integrals, Lipschitz constants        *)
(*  Roles:    f -> Integrand, f' -> Derivative, K -> LipschitzBound         *)
(*  Rules:    FTC equation (constitution), Lipschitz bound (constraint)     *)
(*                                                                          *)
(*  P4 connection: integral = process of accumulation indexed by grid       *)
(*  refinement                                                              *)
(*                                                                          *)
(*  STATUS: 28 Qed, 0 Admitted, 0 axioms                                   *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.

From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import EVT_idx.
From ToS Require Import Differentiation.
From ToS Require Import MeanValueTheorem.
From ToS Require Import RiemannIntegration.
From ToS Require Import IntegralApplications.

Open Scope Q_scope.

(* ========================================================================= *)
(* DEFINITIONS                                                                *)
(* ========================================================================= *)

(** Lipschitz condition on [a,b] with constant K *)
Definition Lipschitz_on (f : Q -> Q) (a b K : Q) : Prop :=
  0 <= K /\
  forall x y : Q, a <= x -> x <= b -> a <= y -> y <= b ->
    Qabs (f x - f y) <= K * Qabs (x - y).

(** Uniform continuity on [a,b] *)
Definition uniformly_continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists delta : Q, 0 < delta /\
      forall x y : Q, a <= x -> x <= b -> a <= y -> y <= b ->
        Qabs (x - y) < delta ->
        Qabs (f x - f y) < eps.

(* ========================================================================= *)
(* SECTION 1: LIPSCHITZ THEORY (8 lemmas)                                    *)
(* ========================================================================= *)

(** L1: Constant function is 0-Lipschitz *)
Lemma lipschitz_const : forall (c a b : Q),
  a <= b -> Lipschitz_on (fun _ => c) a b 0.
Proof.
  intros c a b Hab.
  split; [lra |].
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : c - c == 0) by ring.
  qabs_rw Herr. rewrite Qabs_pos; [| lra].
  assert (Hnn := Qabs_nonneg (x - y)). lra.
Qed.

(** L2: Identity function is 1-Lipschitz *)
Lemma lipschitz_identity : forall (a b : Q),
  a <= b -> Lipschitz_on (fun x => x) a b 1.
Proof.
  intros a b Hab.
  split; [lra |].
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : x - y == 1 * (x - y)) by ring.
  qabs_rw Herr. rewrite Qabs_Qmult.
  rewrite Qabs_pos; [lra | lra].
Qed.

(** L3: c*f is |c|*K-Lipschitz *)
Lemma lipschitz_scale : forall (f : Q -> Q) (a b K c : Q),
  Lipschitz_on f a b K ->
  Lipschitz_on (fun x => c * f x) a b (Qabs c * K).
Proof.
  intros f a b K c [HK Hlip].
  split.
  { apply Qmult_le_0_compat; [apply Qabs_nonneg | exact HK]. }
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : c * f x - c * f y == c * (f x - f y)) by ring.
  qabs_rw Herr. rewrite Qabs_Qmult.
  specialize (Hlip x y Hax Hxb Hay Hyb).
  assert (Hnn := Qabs_nonneg c).
  assert (Hdiff : 0 <= Qabs c * (K * Qabs (x - y) - Qabs (f x - f y))).
  { apply Qmult_le_0_compat; [exact Hnn | lra]. }
  assert (Hring : Qabs c * (K * Qabs (x - y) - Qabs (f x - f y)) ==
                   Qabs c * K * Qabs (x - y) - Qabs c * Qabs (f x - f y)) by ring.
  lra.
Qed.

(** L4: f+g is (Kf+Kg)-Lipschitz *)
Lemma lipschitz_add : forall (f g : Q -> Q) (a b Kf Kg : Q),
  Lipschitz_on f a b Kf ->
  Lipschitz_on g a b Kg ->
  Lipschitz_on (fun x => f x + g x) a b (Kf + Kg).
Proof.
  intros f g a b Kf Kg [HKf Hlipf] [HKg Hlipg].
  split; [lra |].
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : (f x + g x) - (f y + g y) == (f x - f y) + (g x - g y)) by ring.
  qabs_rw Herr.
  specialize (Hlipf x y Hax Hxb Hay Hyb).
  specialize (Hlipg x y Hax Hxb Hay Hyb).
  assert (Htri := Qabs_triangle (f x - f y) (g x - g y)).
  assert (Hring : (Kf + Kg) * Qabs (x - y) == Kf * Qabs (x - y) + Kg * Qabs (x - y)) by ring.
  lra.
Qed.

(** L5: f-g is (Kf+Kg)-Lipschitz *)
Lemma lipschitz_sub : forall (f g : Q -> Q) (a b Kf Kg : Q),
  Lipschitz_on f a b Kf ->
  Lipschitz_on g a b Kg ->
  Lipschitz_on (fun x => f x - g x) a b (Kf + Kg).
Proof.
  intros f g a b Kf Kg [HKf Hlipf] [HKg Hlipg].
  split; [lra |].
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : (f x - g x) - (f y - g y) == (f x - f y) + (-(g x - g y))) by ring.
  qabs_rw Herr.
  specialize (Hlipf x y Hax Hxb Hay Hyb).
  specialize (Hlipg x y Hax Hxb Hay Hyb).
  assert (Htri := Qabs_triangle (f x - f y) (-(g x - g y))).
  rewrite Qabs_opp in Htri.
  assert (Hring : (Kf + Kg) * Qabs (x - y) == Kf * Qabs (x - y) + Kg * Qabs (x - y)) by ring.
  lra.
Qed.

(** L6: -f is K-Lipschitz *)
Lemma lipschitz_negate : forall (f : Q -> Q) (a b K : Q),
  Lipschitz_on f a b K ->
  Lipschitz_on (fun x => - f x) a b K.
Proof.
  intros f a b K [HK Hlip].
  split; [exact HK |].
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : - f x - - f y == -(f x - f y)) by ring.
  qabs_rw Herr. rewrite Qabs_opp.
  exact (Hlip x y Hax Hxb Hay Hyb).
Qed.

(** L7: Composition g o f is Kg*Kf-Lipschitz (assuming ranges match) *)
Lemma lipschitz_compose : forall (f g : Q -> Q) (a b c d Kf Kg : Q),
  Lipschitz_on f a b Kf ->
  Lipschitz_on g c d Kg ->
  (forall x : Q, a <= x -> x <= b -> c <= f x /\ f x <= d) ->
  Lipschitz_on (fun x => g (f x)) a b (Kg * Kf).
Proof.
  intros f g a b c d Kf Kg [HKf Hlipf] [HKg Hlipg] Hrange.
  split.
  { apply Qmult_le_0_compat; assumption. }
  intros x y Hax Hxb Hay Hyb.
  specialize (Hlipf x y Hax Hxb Hay Hyb).
  assert (Hfx_in := Hrange x Hax Hxb). destruct Hfx_in as [Hfxc Hfxd].
  assert (Hfy_in := Hrange y Hay Hyb). destruct Hfy_in as [Hfyc Hfyd].
  specialize (Hlipg (f x) (f y) Hfxc Hfxd Hfyc Hfyd).
  apply Qle_trans with (Kg * Qabs (f x - f y)); [exact Hlipg |].
  assert (Hnn_fg := Qabs_nonneg (f x - f y)).
  assert (Hdiff : 0 <= Kg * (Kf * Qabs (x - y) - Qabs (f x - f y))).
  { apply Qmult_le_0_compat; [exact HKg | lra]. }
  assert (Hring : Kg * (Kf * Qabs (x - y) - Qabs (f x - f y)) ==
                   Kg * Kf * Qabs (x - y) - Kg * Qabs (f x - f y)) by ring.
  lra.
Qed.

(** L8: Lipschitz implies uniformly continuous *)
Lemma lipschitz_uniform_cont : forall (f : Q -> Q) (a b K : Q),
  Lipschitz_on f a b K ->
  uniformly_continuous_on f a b.
Proof.
  intros f a b K [HK Hlip] eps Heps.
  exists (eps / (K + 1)).
  assert (HK1 : 0 < K + 1) by lra.
  split.
  { apply Qlt_shift_div_l; [exact HK1 | lra]. }
  intros x y Hax Hxb Hay Hyb Hxy.
  specialize (Hlip x y Hax Hxb Hay Hyb).
  apply Qle_lt_trans with (K * Qabs (x - y)); [exact Hlip |].
  apply Qle_lt_trans with (K * (eps / (K + 1))).
  { assert (Hdiff : 0 <= K * (eps / (K + 1) - Qabs (x - y))).
    { apply Qmult_le_0_compat; [exact HK | lra]. }
    assert (Hring2 : K * (eps / (K + 1) - Qabs (x - y)) ==
                       K * (eps / (K + 1)) - K * Qabs (x - y)) by ring.
    lra. }
  assert (Hfrac : K / (K + 1) < 1).
  { apply Qlt_shift_div_r; [exact HK1 |]. lra. }
  assert (Hassoc : K * (eps / (K + 1)) == eps * (K / (K + 1))).
  { field. lra. }
  assert (Hbd : eps * (K / (K + 1)) < eps * 1).
  { apply Qmult_lt_l; [exact Heps | exact Hfrac]. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: FTC CONSEQUENCES (8 lemmas)                                    *)
(* ========================================================================= *)

(** L9: Increment bound from FTC: |f(wp(SN)) - f(a)| <= (M+eps)(b-a) *)
Lemma ftc_increment_bound : forall (f f' : Q -> Q) (a b M eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 <= M ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a) <= (M + eps) * (b - a).
Proof.
  intros f f' a b M eps Hudiff HM HMnn Heps.
  exact (bounded_deriv_bounded_increment f f' a b M eps Hudiff HM Heps).
Qed.

(** L10: f' >= 0 implies f increasing (grid version) *)
Lemma ftc_monotone : forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> 0 <= f' x) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    -(eps * (b - a)) <= f (walk_point a step (S N)) - f a.
Proof.
  intros f f' a b eps Hudiff Hnn Heps.
  assert (Hab : a < b) by (destruct Hudiff; exact H).
  assert (Hba : 0 < b - a) by lra.
  destruct (ftc_grid f f' a b eps Hudiff Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hrs_nn : 0 <= riemann_sum f' a step (S N)).
  { apply riemann_sum_nonneg; [| lra].
    intros k Hk.
    assert (Hin := walk_point_in_interval a b N k Hab).
    assert (Hk_le : (k <= S N)%nat) by lia.
    specialize (Hin Hk_le). destruct Hin as [Hlo Hhi].
    apply Hnn; assumption. }
  assert (Hle_abs : riemann_sum f' a step (S N) -
                      (f (walk_point a step (S N)) - f a) <=
                      Qabs (riemann_sum f' a step (S N) -
                            (f (walk_point a step (S N)) - f a))).
  { destruct (Qlt_le_dec (riemann_sum f' a step (S N) -
                            (f (walk_point a step (S N)) - f a)) 0).
    - assert (Hnn2 := Qabs_nonneg (riemann_sum f' a step (S N) -
                                    (f (walk_point a step (S N)) - f a))). lra.
    - rewrite Qabs_pos; lra. }
  assert (HN_noabs : riemann_sum f' a step (S N) -
    (f (walk_point a step (S N)) - f a) <= eps * (b - a)).
  { eapply Qle_trans. exact Hle_abs. exact HN. }
  (* lra can't handle the nonlinear product eps*(b-a), so we prove manually *)
  assert (Hgoal : -(eps * (b - a)) <= f (walk_point a step (S N)) - f a).
  { assert (H1 : riemann_sum f' a step (S N) - eps * (b - a) <=
                  f (walk_point a step (S N)) - f a).
    { set (E := eps * (b - a)) in *. lra. }
    set (E := eps * (b - a)) in *. lra. }
  exact Hgoal.
Qed.

(** L11: f' >= m > 0 implies f strictly increasing *)
Lemma ftc_strict_monotone : forall (f f' : Q -> Q) (a b m : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> m <= f' x) ->
  0 < m ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    0 < f (walk_point a step (S N)) - f a.
Proof.
  intros f f' a b m Hudiff Hlo Hm.
  exact (pos_deriv_increases f f' a b m Hudiff Hlo Hm).
Qed.

(** L12: FTC for difference f-g *)
Lemma ftc_difference : forall (f f' g g' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' x - g' x) a step (S N) -
          ((f (walk_point a step (S N)) - g (walk_point a step (S N))) -
           (f a - g a))) <= eps * (b - a).
Proof.
  intros f f' g g' a b eps Huf Hug Heps.
  assert (Hsub : udiff_on (fun x => f x - g x) (fun x => f' x - g' x) a b).
  { apply udiff_sub; assumption. }
  exact (ftc_grid _ _ a b eps Hsub Heps).
Qed.

(** L13: |RS(f)| <= M*(b-a) when |f| <= M on the grid *)
Lemma ftc_absolute_value_bound : forall (f : Q -> Q) (a b M : Q) (N : nat),
  a < b ->
  (forall k : nat, (k < S N)%nat ->
    Qabs (f (walk_point a ((b - a) / inject_Z (Z.of_nat (S N))) k)) <= M) ->
  0 <= M ->
  Qabs (riemann_sum f a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) <= M * (b - a).
Proof.
  intros f a b M N Hab HM HMnn.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hstep_nn : 0 <= step) by lra.
  assert (Hbd := riemann_sum_abs_bound f a step (S N) M HM Hstep_nn HMnn).
  assert (Hwidth : inject_Z (Z.of_nat (S N)) * step == b - a).
  { unfold step. field.
    intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  assert (Hgoal : M * inject_Z (Z.of_nat (S N)) * step == M * (b - a)).
  { assert (Hring : M * inject_Z (Z.of_nat (S N)) * step == M * (inject_Z (Z.of_nat (S N)) * step)) by ring.
    rewrite Hring. rewrite Hwidth. reflexivity. }
  rewrite Hgoal in Hbd. exact Hbd.
Qed.

(** L14: FTC for sum f+g *)
Lemma ftc_sum_rule : forall (f f' g g' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' x + g' x) a step (S N) -
          ((f (walk_point a step (S N)) + g (walk_point a step (S N))) -
           (f a + g a))) <= eps * (b - a).
Proof.
  intros f f' g g' a b eps Huf Hug Heps.
  exact (ftc_linearity f f' g g' a b eps Huf Hug Heps).
Qed.

(** L15: Integral of zero derivative is zero *)
Lemma ftc_constant_function : forall (a b eps : Q),
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun _ => 0) a step (S N)) <= eps * (b - a).
Proof.
  intros a b eps Hab Heps.
  exact (ftc_constant a b eps Hab Heps).
Qed.

(** L16: FTC for c*f *)
Lemma ftc_scale_rule : forall (c : Q) (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => c * f' x) a step (S N) -
          (c * f (walk_point a step (S N)) - c * f a)) <= eps * (b - a).
Proof.
  intros c f f' a b eps Huf Heps.
  assert (Hscale : udiff_on (fun x => c * f x) (fun x => c * f' x) a b).
  { apply udiff_scale. exact Huf. }
  exact (ftc_grid _ _ a b eps Hscale Heps).
Qed.

(* ========================================================================= *)
(* SECTION 3: U-SUBSTITUTION (3 lemmas)                                      *)
(* ========================================================================= *)

(** L17: Chain rule for affine inner function g(x) = c*x + d *)
Lemma udiff_chain_affine : forall (f f' : Q -> Q) (a b c d : Q),
  Proper (Qeq ==> Qeq) f ->
  c > 0 ->
  udiff_on f f' (c * a + d) (c * b + d) ->
  a < b ->
  udiff_on (fun x => f (c * x + d)) (fun x => f' (c * x + d) * c) a b.
Proof.
  intros f f' a b c d Hf_proper Hc [Hcd Huf] Hab.
  split; [exact Hab |].
  intros eps Heps.
  assert (Hc_abs : Qabs c == c) by (rewrite Qabs_pos; lra).
  assert (Heps_c : 0 < eps / c).
  { apply Qlt_shift_div_l; [exact Hc | lra]. }
  destruct (Huf (eps / c) Heps_c) as [delta [Hdelta Hbd]].
  exists (delta / c).
  split.
  { apply Qlt_shift_div_l; [exact Hc | lra]. }
  intros x h Hax Hxb Hh_pos Hh_lt.
  assert (Hassoc : c * (x + h) + d == (c * x + d) + c * h) by ring.
  assert (Herr_eq : f (c * (x + h) + d) - f (c * x + d) - f' (c * x + d) * c * h ==
                     f ((c * x + d) + c * h) - f (c * x + d) - f' (c * x + d) * (c * h)).
  { rewrite (Hf_proper _ _ Hassoc). ring. }
  qabs_rw Herr_eq.
  assert (Hx0_lo : c * a + d <= c * x + d).
  { assert (Hdiff : 0 <= c * (x - a)) by (apply Qmult_le_0_compat; lra). lra. }
  assert (Hx0_hi : c * x + d <= c * b + d).
  { assert (Hdiff : 0 <= c * (b - x)) by (apply Qmult_le_0_compat; lra). lra. }
  assert (Hch_abs : Qabs (c * h) == c * Qabs h).
  { rewrite Qabs_Qmult. rewrite Hc_abs. reflexivity. }
  assert (Hch_pos : 0 < Qabs (c * h)).
  { rewrite Hch_abs. apply Qmult_lt_0_compat; [exact Hc | exact Hh_pos]. }
  assert (Hch_lt : Qabs (c * h) < delta).
  { rewrite Hch_abs.
    assert (H1 : c * Qabs h < c * (delta / c)).
    { apply Qmult_lt_l; [exact Hc | exact Hh_lt]. }
    assert (H2 : c * (delta / c) == delta) by (field; lra).
    lra. }
  specialize (Hbd (c * x + d) (c * h) Hx0_lo Hx0_hi Hch_pos Hch_lt).
  assert (Hsimp : eps / c * Qabs (c * h) == eps * Qabs h).
  { rewrite Hch_abs. field. lra. }
  lra.
Qed.

(** L18: FTC for u-substitution with affine inner function *)
Lemma ftc_u_substitution_affine :
  forall (f f' : Q -> Q) (a b c d eps : Q),
  Proper (Qeq ==> Qeq) f ->
  c > 0 ->
  udiff_on f f' (c * a + d) (c * b + d) ->
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' (c * x + d) * c) a step (S N) -
          (f (c * walk_point a step (S N) + d) - f (c * a + d))) <=
    eps * (b - a).
Proof.
  intros f f' a b c d eps Hf_proper Hc Huf Hab Heps.
  assert (Hcomp : udiff_on (fun x => f (c * x + d)) (fun x => f' (c * x + d) * c) a b).
  { apply udiff_chain_affine; assumption. }
  exact (ftc_grid _ _ a b eps Hcomp Heps).
Qed.

(** L19: udiff for negative scaling of inner function *)
Lemma udiff_chain_affine_neg : forall (f f' : Q -> Q) (a b c d : Q),
  Proper (Qeq ==> Qeq) f ->
  c < 0 ->
  udiff_on f f' (c * b + d) (c * a + d) ->
  a < b ->
  udiff_on (fun x => f (c * x + d)) (fun x => f' (c * x + d) * c) a b.
Proof.
  intros f f' a b c d Hf_proper Hc [Hcd Huf] Hab.
  split; [exact Hab |].
  intros eps Heps.
  assert (Hc_abs : Qabs c == -c) by (rewrite Qabs_neg; lra).
  assert (Hnc : 0 < -c) by lra.
  assert (Heps_c : 0 < eps / (-c)).
  { apply Qlt_shift_div_l; [exact Hnc | lra]. }
  destruct (Huf (eps / (-c)) Heps_c) as [delta [Hdelta Hbd]].
  exists (delta / (-c)).
  split.
  { apply Qlt_shift_div_l; [exact Hnc | lra]. }
  intros x h Hax Hxb Hh_pos Hh_lt.
  assert (Hassoc : c * (x + h) + d == (c * x + d) + c * h) by ring.
  assert (Herr_eq : f (c * (x + h) + d) - f (c * x + d) - f' (c * x + d) * c * h ==
                     f ((c * x + d) + c * h) - f (c * x + d) - f' (c * x + d) * (c * h)).
  { rewrite (Hf_proper _ _ Hassoc). ring. }
  qabs_rw Herr_eq.
  (* c < 0 so c*b+d <= c*x+d <= c*a+d *)
  assert (Hx0_lo : c * b + d <= c * x + d).
  { assert (Hdiff : 0 <= (-c) * (b - x)) by (apply Qmult_le_0_compat; lra).
    assert (Hring : (-c) * (b - x) == c * x - c * b) by ring.
    assert (Hle : c * b <= c * x).
    { set (P := (-c) * (b - x)) in *. lra. }
    lra. }
  assert (Hx0_hi : c * x + d <= c * a + d).
  { assert (Hdiff : 0 <= (-c) * (x - a)) by (apply Qmult_le_0_compat; lra).
    assert (Hring : (-c) * (x - a) == c * a - c * x) by ring.
    assert (Hle : c * x <= c * a).
    { set (P := (-c) * (x - a)) in *. lra. }
    lra. }
  assert (Hch_abs : Qabs (c * h) == (-c) * Qabs h).
  { rewrite Qabs_Qmult. rewrite Hc_abs. ring. }
  assert (Hch_pos : 0 < Qabs (c * h)).
  { rewrite Hch_abs. apply Qmult_lt_0_compat; [exact Hnc | exact Hh_pos]. }
  assert (Hch_lt : Qabs (c * h) < delta).
  { rewrite Hch_abs.
    assert (H1 : (-c) * Qabs h < (-c) * (delta / (-c))).
    { apply Qmult_lt_l; [exact Hnc | exact Hh_lt]. }
    assert (H2 : (-c) * (delta / (-c)) == delta) by (field; lra).
    lra. }
  specialize (Hbd (c * x + d) (c * h) Hx0_lo Hx0_hi Hch_pos Hch_lt).
  assert (Hsimp : eps / (-c) * Qabs (c * h) == eps * Qabs h).
  { rewrite Hch_abs. field. lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: RIEMANN SUM INFRASTRUCTURE (4 lemmas)                          *)
(* ========================================================================= *)

(** L20: RS(-f) = -RS(f) *)
Lemma riemann_sum_negate_fn : forall (f : Q -> Q) (a step : Q) (n : nat),
  riemann_sum (fun x => - f x) a step n == - riemann_sum f a step n.
Proof.
  intros f a step n.
  assert (Hscale : riemann_sum (fun x => -(1) * f x) a step n ==
                    -(1) * riemann_sum f a step n).
  { apply riemann_sum_scale. }
  assert (Hext : riemann_sum (fun x => - f x) a step n ==
                  riemann_sum (fun x => -(1) * f x) a step n).
  { apply riemann_sum_ext. intros k Hk. ring. }
  lra.
Qed.

(** L21: RS(f-g) = RS(f) - RS(g) *)
Lemma riemann_sum_sub : forall (f g : Q -> Q) (a step : Q) (n : nat),
  riemann_sum (fun x => f x - g x) a step n ==
  riemann_sum f a step n - riemann_sum g a step n.
Proof.
  intros f g a step n.
  assert (Hadd : riemann_sum (fun x => f x + (- g x)) a step n ==
                  riemann_sum f a step n + riemann_sum (fun x => - g x) a step n).
  { apply riemann_sum_add. }
  assert (Hext : riemann_sum (fun x => f x - g x) a step n ==
                  riemann_sum (fun x => f x + (- g x)) a step n).
  { apply riemann_sum_ext. intros k Hk. ring. }
  assert (Hneg : riemann_sum (fun x => - g x) a step n ==
                  - riemann_sum g a step n).
  { apply riemann_sum_negate_fn. }
  lra.
Qed.

(** L22: f <= g pointwise on grid implies RS(f) <= RS(g) *)
Lemma riemann_sum_sandwich : forall (f g : Q -> Q) (a step : Q) (n : nat),
  (forall k : nat, (k < n)%nat -> f (walk_point a step k) <= g (walk_point a step k)) ->
  0 <= step ->
  riemann_sum f a step n <= riemann_sum g a step n.
Proof.
  intros f g a step n Hfg Hstep.
  exact (riemann_sum_monotone f g a step n Hfg Hstep).
Qed.

(** L23: RS >= m * n * step when f >= m pointwise *)
Lemma riemann_sum_bound_below : forall (f : Q -> Q) (a step : Q) (n : nat) (m : Q),
  (forall k : nat, (k < n)%nat -> m <= f (walk_point a step k)) ->
  0 <= step ->
  m * inject_Z (Z.of_nat n) * step <= riemann_sum f a step n.
Proof.
  intros f a step n m Hf Hstep.
  assert (Hlo : riemann_sum (fun _ => m) a step n <= riemann_sum f a step n).
  { apply riemann_sum_monotone; [| exact Hstep].
    intros k Hk. apply Hf. exact Hk. }
  assert (Hconst : riemann_sum (fun _ => m) a step n == m * inject_Z (Z.of_nat n) * step).
  { apply riemann_sum_const. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: BRIDGE LEMMAS (5 lemmas)                                       *)
(* ========================================================================= *)

(** L24: udiff + bounded derivative implies approximate Lipschitz bound
    on the walk_point grid endpoint *)
Lemma udiff_approx_lipschitz : forall (f f' : Q -> Q) (a b M eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 <= M ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a) <= (M + eps) * (b - a).
Proof.
  intros f f' a b M eps Hudiff HM HMnn Heps.
  exact (bounded_deriv_bounded_increment f f' a b M eps Hudiff HM Heps).
Qed.

(** L25: udiff + bounded derivative implies value bound relative to f(a) *)
Lemma udiff_implies_bounded : forall (f f' : Q -> Q) (a b M eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 <= M ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N))) <= Qabs (f a) + (M + eps) * (b - a).
Proof.
  intros f f' a b M eps Hudiff HM HMnn Heps.
  destruct (bounded_deriv_bounded_increment f f' a b M eps Hudiff HM Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* |f(end)| = |f(a) + (f(end)-f(a))| <= |f(a)| + |f(end)-f(a)| *)
  assert (Hdecomp : f (walk_point a step (S N)) ==
                     f a + (f (walk_point a step (S N)) - f a)) by ring.
  assert (Habs_eq := Qabs_wd _ _ Hdecomp).
  assert (Htri := Qabs_triangle (f a) (f (walk_point a step (S N)) - f a)).
  (* Habs_eq : Qabs(f(wp)) == Qabs(f(a) + (f(wp)-f(a)))
     Htri : Qabs(f(a) + (f(wp)-f(a))) <= Qabs(f(a)) + Qabs(f(wp)-f(a))
     HN : Qabs(f(wp) - f(a)) <= (M+eps)*(b-a) *)
  apply Qle_trans with (Qabs (f a + (f (walk_point a step (S N)) - f a))).
  { exact (Qeq_Qle _ _ Habs_eq). }
  apply Qle_trans with (Qabs (f a) + Qabs (f (walk_point a step (S N)) - f a)).
  { exact Htri. }
  (* Goal: Qabs(f a) + Qabs(f(wp)-f(a)) <= Qabs(f a) + (M+eps)*(b-a)
     HN: Qabs(f(wp)-f(a)) <= (M+eps)*(b-a) *)
  apply Qplus_le_compat.
  { lra. }
  { exact HN. }
Qed.

(** L26: Lipschitz on [a,b] implies bounded on [a,b] relative to f(a) *)
Lemma lipschitz_bounded : forall (f : Q -> Q) (a b K : Q),
  Lipschitz_on f a b K ->
  forall x : Q, a <= x -> x <= b ->
    Qabs (f x - f a) <= K * Qabs (b - a).
Proof.
  intros f a b K [HK Hlip] x Hax Hxb.
  assert (Hab : a <= b) by lra.
  specialize (Hlip x a Hax Hxb (Qle_refl a) Hab).
  apply Qle_trans with (K * Qabs (x - a)); [exact Hlip |].
  assert (Hxa : 0 <= x - a) by lra.
  assert (Hba : 0 <= b - a) by lra.
  assert (Hxa_abs : Qabs (x - a) == x - a) by (rewrite Qabs_pos; lra).
  assert (Hba_abs : Qabs (b - a) == b - a) by (rewrite Qabs_pos; lra).
  assert (Hdiff : 0 <= K * (Qabs (b - a) - Qabs (x - a))).
  { apply Qmult_le_0_compat; [exact HK | lra]. }
  assert (Hring2 : K * (Qabs (b - a) - Qabs (x - a)) ==
                     K * Qabs (b - a) - K * Qabs (x - a)) by ring.
  lra.
Qed.

(** L27: udiff sub-interval: udiff on [a,b] implies udiff on [c,d] for a<=c<d<=b *)
Lemma udiff_sub_interval : forall (f f' : Q -> Q) (a b c d : Q),
  udiff_on f f' a b ->
  a <= c -> c < d -> d <= b ->
  udiff_on f f' c d.
Proof.
  intros f f' a b c d [Hab Huf] Hac Hcd Hdb.
  split; [exact Hcd |].
  intros eps Heps.
  destruct (Huf eps Heps) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta |].
  intros x h Hcx Hxd Hh_pos Hh_lt.
  assert (Hax : a <= x) by lra.
  assert (Hxb : x <= b) by lra.
  exact (Hbd x h Hax Hxb Hh_pos Hh_lt).
Qed.

(** L28: Affine function is Lipschitz with constant |c| *)
Lemma lipschitz_affine : forall (c d a b : Q),
  a <= b ->
  Lipschitz_on (fun x => c * x + d) a b (Qabs c).
Proof.
  intros c d a b Hab.
  split; [apply Qabs_nonneg |].
  intros x y Hax Hxb Hay Hyb.
  assert (Herr : (c * x + d) - (c * y + d) == c * (x - y)) by ring.
  qabs_rw Herr. rewrite Qabs_Qmult.
  lra.
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                               *)
(* ========================================================================= *)

Check lipschitz_const.            (* L1  *)
Check lipschitz_identity.         (* L2  *)
Check lipschitz_scale.            (* L3  *)
Check lipschitz_add.              (* L4  *)
Check lipschitz_sub.              (* L5  *)
Check lipschitz_negate.           (* L6  *)
Check lipschitz_compose.          (* L7  *)
Check lipschitz_uniform_cont.     (* L8  *)
Check ftc_increment_bound.        (* L9  *)
Check ftc_monotone.               (* L10 *)
Check ftc_strict_monotone.        (* L11 *)
Check ftc_difference.             (* L12 *)
Check ftc_absolute_value_bound.   (* L13 *)
Check ftc_sum_rule.               (* L14 *)
Check ftc_constant_function.      (* L15 *)
Check ftc_scale_rule.             (* L16 *)
Check udiff_chain_affine.         (* L17 *)
Check ftc_u_substitution_affine.  (* L18 *)
Check udiff_chain_affine_neg.     (* L19 *)
Check riemann_sum_negate_fn.      (* L20 *)
Check riemann_sum_sub.            (* L21 *)
Check riemann_sum_sandwich.       (* L22 *)
Check riemann_sum_bound_below.    (* L23 *)
Check udiff_approx_lipschitz.     (* L24 *)
Check udiff_implies_bounded.      (* L25 *)
Check lipschitz_bounded.          (* L26 *)
Check udiff_sub_interval.         (* L27 *)
Check lipschitz_affine.           (* L28 *)

Print Assumptions lipschitz_compose.
Print Assumptions lipschitz_uniform_cont.
Print Assumptions ftc_u_substitution_affine.
Print Assumptions udiff_sub_interval.
