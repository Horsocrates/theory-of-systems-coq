(** * ConvexAnalysis.v -- Convex Sets and Functions

    Theory of Systems -- Verified Standard Library (Batch 5)

    Elements: points in domain, function values
    Roles:    minimum -> OptimalPoint, gradient -> Direction
    Rules:    convexity inequality (constitution)
    Status:   minimum | saddle | interior | boundary

    Connection: Hessian.v (positive_definite -> convex)
    Connection: GradientDescent.v (convex -> GD converges)
    Connection: Statistics.v (Jensen for expectation)

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Core Definitions                                                  *)
(* ================================================================ *)

Definition convex_set (S : Q -> Prop) : Prop :=
  forall x y lambda, S x -> S y -> 0 <= lambda -> lambda <= 1 ->
    S (lambda * x + (1 - lambda) * y).

Definition convex_function (f : Q -> Q) (S : Q -> Prop) : Prop :=
  forall x y lambda, S x -> S y -> 0 <= lambda -> lambda <= 1 ->
    f (lambda * x + (1 - lambda) * y) <= lambda * f x + (1 - lambda) * f y.

Definition strictly_convex (f : Q -> Q) (S : Q -> Prop) : Prop :=
  forall x y lambda, S x -> S y -> ~(x == y) -> 0 < lambda -> lambda < 1 ->
    f (lambda * x + (1 - lambda) * y) < lambda * f x + (1 - lambda) * f y.

Definition strongly_convex_mu (f : Q -> Q) (S : Q -> Prop) (mu : Q) : Prop :=
  0 < mu /\
  forall x y lambda, S x -> S y -> 0 <= lambda -> lambda <= 1 ->
    f (lambda * x + (1 - lambda) * y) <=
    lambda * f x + (1 - lambda) * f y - mu / 2 * lambda * (1 - lambda) * (x - y) * (x - y).

Definition interval_set (a b : Q) : Q -> Prop := fun x => a <= x /\ x <= b.

Definition all_Q : Q -> Prop := fun _ => True.

Definition concave_function (f : Q -> Q) (S : Q -> Prop) : Prop :=
  convex_function (fun x => - f x) S.

Definition is_local_min (f : Q -> Q) (x : Q) : Prop :=
  exists delta, 0 < delta /\ forall y, Qabs (y - x) < delta -> f x <= f y.

Definition is_global_min (f : Q -> Q) (S : Q -> Prop) (x : Q) : Prop :=
  S x /\ forall y, S y -> f x <= f y.

(* ================================================================ *)
(* Theorems about Convex Sets                                        *)
(* ================================================================ *)

Lemma interval_is_convex : forall a b, a <= b -> convex_set (interval_set a b).
Proof.
  unfold convex_set, interval_set. intros a b Hab x y lam [Hax Hxb] [Hay Hyb] Hl0 Hl1.
  split.
  - assert (0 <= lam * (x - a)) by (apply Qmult_le_0_compat; lra).
    assert (0 <= (1 - lam) * (y - a)) by (apply Qmult_le_0_compat; lra). lra.
  - assert (0 <= lam * (b - x)) by (apply Qmult_le_0_compat; lra).
    assert (0 <= (1 - lam) * (b - y)) by (apply Qmult_le_0_compat; lra). lra.
Qed.

Lemma all_Q_is_convex : convex_set all_Q.
Proof.
  unfold convex_set, all_Q. intros. exact I.
Qed.

Lemma convex_set_intersection : forall S1 S2,
  convex_set S1 -> convex_set S2 -> convex_set (fun x => S1 x /\ S2 x).
Proof.
  unfold convex_set. intros S1 S2 H1 H2 x y lam [Hx1 Hx2] [Hy1 Hy2] Hl0 Hl1.
  split.
  - apply H1; assumption.
  - apply H2; assumption.
Qed.

Lemma interval_midpoint_in_interval : forall a b,
  a <= b -> interval_set a b ((1#2) * a + (1#2) * b).
Proof.
  unfold interval_set. intros a b Hab. split; lra.
Qed.

Lemma empty_set_convex : convex_set (fun _ => False).
Proof.
  unfold convex_set. intros x y lam Hx. contradiction.
Qed.

Lemma singleton_convex : forall p, convex_set (fun x => x == p).
Proof.
  unfold convex_set. intros p x y lam Hx Hy Hl0 Hl1.
  rewrite Hx, Hy. ring_simplify. reflexivity.
Qed.

(* ================================================================ *)
(* Theorems about Convex Functions                                   *)
(* ================================================================ *)

Lemma constant_function_convex : forall (c : Q) (S : Q -> Prop),
  convex_function (fun _ => c) S.
Proof.
  unfold convex_function. intros c S x y lam _ _ Hl0 Hl1.
  assert (c == lam * c + (1 - lam) * c) as Hc by ring.
  lra.
Qed.

Lemma linear_function_convex : forall a b,
  convex_function (fun x => a * x + b) all_Q.
Proof.
  unfold convex_function, all_Q. intros a b x y lam _ _ Hl0 Hl1.
  assert (a * (lam * x + (1 - lam) * y) + b ==
          lam * (a * x + b) + (1 - lam) * (a * y + b)) as Heq by ring.
  lra.
Qed.

Lemma affine_is_convex : forall a b (S : Q -> Prop),
  convex_function (fun x => a * x + b) S.
Proof.
  unfold convex_function. intros a b S x y lam _ _ Hl0 Hl1.
  assert (a * (lam * x + (1 - lam) * y) + b ==
          lam * (a * x + b) + (1 - lam) * (a * y + b)) as Heq by ring.
  lra.
Qed.

Lemma sum_of_convex : forall f g (S : Q -> Prop),
  convex_function f S -> convex_function g S ->
  convex_function (fun x => f x + g x) S.
Proof.
  unfold convex_function. intros f g S Hf Hg x y lam Hx Hy Hl0 Hl1.
  specialize (Hf x y lam Hx Hy Hl0 Hl1).
  specialize (Hg x y lam Hx Hy Hl0 Hl1).
  assert (lam * (f x + g x) + (1 - lam) * (f y + g y) ==
          (lam * f x + (1 - lam) * f y) + (lam * g x + (1 - lam) * g y)) as Heq by ring.
  lra.
Qed.

Lemma scale_pos_convex : forall c f (S : Q -> Prop),
  0 <= c -> convex_function f S ->
  convex_function (fun x => c * f x) S.
Proof.
  unfold convex_function. intros c f S Hc Hf x y lam Hx Hy Hl0 Hl1.
  specialize (Hf x y lam Hx Hy Hl0 Hl1).
  assert (0 <= c * (lam * f x + (1 - lam) * f y - f (lam * x + (1 - lam) * y))) by (apply Qmult_le_0_compat; lra). lra.
Qed.

Lemma convex_function_nonneg_combination : forall a b f g (S : Q -> Prop),
  0 <= a -> 0 <= b ->
  convex_function f S -> convex_function g S ->
  convex_function (fun x => a * f x + b * g x) S.
Proof.
  intros a0 b0 f g S Ha Hb Hf Hg.
  apply sum_of_convex.
  - apply scale_pos_convex; assumption.
  - apply scale_pos_convex; assumption.
Qed.

Lemma convex_midpoint : forall f (S : Q -> Prop) x y,
  convex_function f S -> S x -> S y ->
  f ((1#2) * x + (1 - (1#2)) * y) <= (1#2) * f x + (1 - (1#2)) * f y.
Proof.
  unfold convex_function. intros f S x y Hf Hx Hy.
  apply Hf; [assumption | assumption | lra | lra].
Qed.

Lemma neg_convex_is_concave : forall f (S : Q -> Prop),
  convex_function f S ->
  forall x y lambda, S x -> S y -> 0 <= lambda -> lambda <= 1 ->
    lambda * (- f x) + (1 - lambda) * (- f y) <= - f (lambda * x + (1 - lambda) * y).
Proof.
  unfold convex_function. intros f S Hf x y lam Hx Hy Hl0 Hl1.
  specialize (Hf x y lam Hx Hy Hl0 Hl1).
  lra.
Qed.

Lemma jensen_two_point : forall f w1 w2 x1 x2,
  0 <= w1 -> 0 <= w2 -> w1 + w2 == 1 -> convex_function f all_Q ->
  f (w1 * x1 + (1 - w1) * x2) <= w1 * f x1 + (1 - w1) * f x2.
Proof.
  unfold convex_function, all_Q. intros f w1 w2 x1 x2 Hw1 Hw2 Hsum Hf.
  assert (w1 <= 1) as Hw1le by lra.
  apply (Hf x1 x2 w1 I I Hw1 Hw1le).
Qed.

Lemma Q_sq_nonneg : forall x : Q, 0 <= x * x.
Proof. intros x. nra. Qed.

Lemma Q_sq_zero_eq : forall x : Q, x * x == 0 -> x == 0.
Proof. intros x Hsq. nra. Qed.

Lemma strongly_convex_implies_convex : forall f (S : Q -> Prop) mu, strongly_convex_mu f S mu -> convex_function f S.
Proof.
  unfold strongly_convex_mu, convex_function.
  intros f S mu [Hmu Hsc] x y lam Hx Hy Hl0 Hl1.
  specialize (Hsc x y lam Hx Hy Hl0 Hl1).
  assert (0 <= (x - y) * (x - y)) by apply Q_sq_nonneg.
  assert (Hmu2 : 0 <= mu * (1 # 2)) by (apply Qmult_le_0_compat; lra).
  assert (Hdiveq : mu / 2 == mu * (1 # 2)) by (unfold Qdiv; reflexivity).
  assert (0 <= mu / 2 * lam * (1 - lam)) as Hcoeff by (rewrite Hdiveq; apply Qmult_le_0_compat; [apply Qmult_le_0_compat; [exact Hmu2|lra]|lra]).
  assert (mu / 2 * lam * (1 - lam) * (x - y) * (x - y) == (mu / 2 * lam * (1 - lam)) * ((x - y) * (x - y))) as Hassoc by ring.
  assert (0 <= mu / 2 * lam * (1 - lam) * (x - y) * (x - y)) by (rewrite Hassoc; apply Qmult_le_0_compat; assumption). lra.
Qed.

Lemma quadratic_convex_nonneg_coeff : forall a, 0 <= a -> convex_function (fun x => a * x * x) all_Q.
Proof.
  unfold convex_function, all_Q. intros a Ha x y lam _ _ Hl0 Hl1.
  assert (lam * (a * x * x) + (1 - lam) * (a * y * y) - a * (lam * x + (1 - lam) * y) * (lam * x + (1 - lam) * y) == a * lam * (1 - lam) * ((x - y) * (x - y))) as Halg by ring.
  assert (0 <= (x - y) * (x - y)) as Hnn by apply Q_sq_nonneg.
  assert (0 <= a * lam * (1 - lam)) as Hcoeff by (apply Qmult_le_0_compat; [apply Qmult_le_0_compat|]; lra).
  assert (0 <= a * lam * (1 - lam) * ((x - y) * (x - y))) as Hprod by (apply Qmult_le_0_compat; assumption). lra.
Qed.

Lemma convex_local_is_global : forall f x, convex_function f all_Q -> is_local_min f x -> is_global_min f all_Q x.
Proof.
  unfold convex_function, all_Q, is_local_min, is_global_min.
  intros f x Hcvx [delta [Hdelta Hloc]]. split; [exact I|]. intros y _.
  destruct (Qlt_le_dec (f y) (f x)) as [Hlt | Hge]; [|exact Hge]. exfalso.
  destruct (Qlt_le_dec 0 (Qabs (y - x))) as [Hyx_pos | Hyx_zero].
  - set (denom := Qabs (y - x) + delta).
    assert (Hdenom_pos : 0 < denom) by (unfold denom; lra).
    set (t := delta / (2 * denom)).
    assert (Ht_pos : 0 < t) by (unfold t; apply Qlt_shift_div_l; lra).
    assert (Ht_le1 : t <= 1).
    { unfold t. apply Qle_shift_div_r. lra.
      pose proof (Qabs_nonneg (y - x)). unfold denom. nra. }
    assert (Hcvx_ineq := Hcvx y x t I I). assert (0 <= t) as Ht0 by lra.
    specialize (Hcvx_ineq Ht0 Ht_le1).
    assert (Hstrict : t * f y + (1 - t) * f x < f x).
    { nra. }
    set (z := t * y + (1 - t) * x) in *.
    assert (Hfz : f z < f x) by lra.
    assert (Hzx : z - x == t * (y - x)) by (unfold z; ring).
    assert (HQabs_eq : Qabs (z - x) == t * Qabs (y - x)).
    { rewrite Hzx. rewrite Qabs_Qmult.
      assert (Qabs t == t) by (apply Qabs_pos; lra).
      rewrite H. reflexivity. }
    assert (HQabs_lt : Qabs (z - x) < delta).
    { rewrite HQabs_eq. unfold t.
      assert (Hrw : delta / (2 * denom) * Qabs (y - x) == (delta * Qabs (y - x)) / (2 * denom)) by (field; lra).
      rewrite Hrw.
      apply Qlt_shift_div_r. lra.
      pose proof (Qabs_nonneg (y - x)). unfold denom. nra. }
    specialize (Hloc z HQabs_lt). lra.
  - assert (Qabs (y - x) == 0) by (pose proof (Qabs_nonneg (y - x)); lra).
    assert (Qabs (y - x) < delta) by lra.
    specialize (Hloc y H0). lra.
Qed.

Lemma strongly_convex_unique_min : forall f mu x y, strongly_convex_mu f all_Q mu -> is_global_min f all_Q x -> is_global_min f all_Q y -> x == y.
Proof.
  unfold strongly_convex_mu, is_global_min, all_Q.
  intros f mu x y [Hmu Hsc] [_ Hx_min] [_ Hy_min].
  specialize (Hsc x y (1#2) I I).
  assert (H12a : (0:Q) <= (1#2)) by lra. assert (H12b : (1#2:Q) <= 1) by lra.
  specialize (Hsc H12a H12b).
  set (z := (1#2) * x + (1 - (1#2)) * y) in *.
  assert (Hfx_le_fy : f x <= f y) by auto. assert (Hfy_le_fx : f y <= f x) by auto.
  assert (Hfz_ge : f x <= f z) by auto.
  assert (Hfeq : f x == f y) by lra.
  assert ((1#2) * f x + (1 - (1#2)) * f y == f x) by lra.
  assert (mu / 2 * (1 # 2) * (1 - (1 # 2)) * (x - y) * (x - y) <= 0) by lra.
  assert ((1 - (1#2)) == (1#2)) as H12eq by lra. rewrite H12eq in H0.
  assert (0 < mu / 2 * (1#2) * (1#2)) as Hcoeff. { assert (mu / 2 == mu * (1#2)) by (unfold Qdiv; reflexivity). nra. }
  assert (0 <= (x - y) * (x - y)) as Hsq_nn by apply Q_sq_nonneg.
  assert ((x - y) * (x - y) == 0).
  { destruct (Qlt_le_dec 0 ((x-y)*(x-y))); [|lra].
    assert (0 < mu / 2 * (1 # 2) * (1 # 2) * ((x - y) * (x - y))). { assert (mu / 2 == mu * (1#2)) by (unfold Qdiv; reflexivity). nra. }
    assert (mu / 2 * (1 # 2) * (1 # 2) * (x - y) * (x - y) == mu / 2 * (1 # 2) * (1 # 2) * ((x - y) * (x - y))) as Hassoc by ring.
    lra. }
  assert (x - y == 0) by (apply Q_sq_zero_eq; exact H1). lra.
Qed.

Require Import Coq.Classes.Morphisms.

Lemma convex_at_endpoints : forall f (S : Q -> Prop) a b x,
  Proper (Qeq ==> Qeq) f ->
  convex_function f S -> S a -> S b -> a < b -> a <= x -> x <= b ->
  f x <= ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b.
Proof.
  unfold convex_function.
  intros f S a b x Hfp Hf Ha Hb Hab Hax Hxb.
  set (lam := (b - x) / (b - a)).
  assert (Hba_pos : 0 < b - a) by lra.
  assert (Hlam0 : 0 <= lam) by (unfold lam; apply Qle_shift_div_l; lra).
  assert (Hlam1 : lam <= 1) by (unfold lam; apply Qle_shift_div_r; lra).
  assert (Hlam_eq : 1 - lam == (x - a) / (b - a)) by (unfold lam; field; lra).
  assert (Hx_eq : lam * a + (1 - lam) * b == x) by (unfold lam; field; lra).
  specialize (Hf a b lam Ha Hb Hlam0 Hlam1).
  assert (Hfx : f x == f (lam * a + (1 - lam) * b)).
  { apply Hfp. symmetry. exact Hx_eq. }
  assert (Hrhs : lam * f a + (1 - lam) * f b == ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b).
  { rewrite Hlam_eq. unfold lam. reflexivity. }
  apply Qle_trans with (lam * f a + (1 - lam) * f b).
  - rewrite Hfx. exact Hf.
  - rewrite Hrhs. apply Qle_refl.
Qed.
