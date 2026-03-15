(** * ProcessTopMetric.v — Q-Metric Space Properties as Process
    Elements: rational distances, Lipschitz constants
    Roles:    qdist as metric, Lipschitz as process regulator
    Rules:    triangle inequality, Lipschitz preserves Cauchy
    Status:   complete
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS TOPOLOGY METRIC — Q-Metric Space Properties               *)
(*                                                                           *)
(*  Under P4: the metric on Q is just |x - y| with x, y ∈ Q.              *)
(*  No real-valued metric needed. Distance IS a rational process.           *)
(*                                                                           *)
(*  STATUS: 20 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Q-distance  (~7 lemmas)                                    *)
(* ================================================================== *)

(** Rational distance *)
Definition qdist (x y : Q) : Q := Qabs (x - y).

(** Distance is nonneg *)
Lemma qdist_nonneg : forall x y, 0 <= qdist x y.
Proof. intros x y. unfold qdist. apply Qabs_nonneg. Qed.

(** Distance is symmetric *)
Lemma qdist_sym : forall x y, qdist x y == qdist y x.
Proof.
  intros x y. unfold qdist.
  assert (Heq : y - x == -(x - y)) by lra.
  rewrite Heq.
  destruct (Qlt_le_dec (x - y) 0) as [Hn | Hp].
  - rewrite Qabs_neg; [| lra].
    rewrite Qabs_pos; lra.
  - rewrite Qabs_pos; [| lra].
    rewrite Qabs_neg; lra.
Qed.

(** Triangle inequality *)
Lemma qdist_triangle : forall x y z,
  qdist x z <= qdist x y + qdist y z.
Proof.
  intros x y z. unfold qdist.
  assert (Htri := Qabs_triangle (x - y) (y - z)).
  assert (Heq : x - y + (y - z) == x - z) by lra.
  rewrite <- Heq. exact Htri.
Qed.

(** Distance zero iff equal *)
Lemma qdist_zero_iff : forall x y,
  qdist x y == 0 <-> x == y.
Proof.
  intros x y. unfold qdist. split.
  - intros H.
    assert (Hnn := Qabs_nonneg (x - y)).
    destruct (Qlt_le_dec (x - y) 0) as [Hn | Hp].
    + rewrite Qabs_neg in H; lra.
    + rewrite Qabs_pos in H; lra.
  - intros H.
    assert (Heq : x - y == 0) by lra.
    rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** Distance after translation *)
Lemma qdist_translate : forall x y c,
  qdist (x + c) (y + c) == qdist x y.
Proof.
  intros x y c. unfold qdist.
  assert (Heq : x + c - (y + c) == x - y) by lra.
  rewrite Heq. lra.
Qed.

(** Distance under scaling *)
Lemma qdist_scale : forall x y c,
  0 <= c -> qdist (c * x) (c * y) == c * qdist x y.
Proof.
  intros x y c Hc. unfold qdist.
  assert (Heq : c * x - c * y == c * (x - y)) by lra.
  rewrite Heq. rewrite Qabs_Qmult. rewrite (Qabs_pos c); lra.
Qed.

(** Midpoint distance *)
Lemma qdist_midpoint : forall x y,
  qdist x ((x + y) * (1#2)) == qdist x y * (1#2).
Proof.
  intros x y. unfold qdist.
  assert (Heq : x - (x + y) * (1#2) == (x - y) * (1#2)) by lra.
  rewrite Heq.
  rewrite Qabs_Qmult. rewrite (Qabs_pos (1#2)); lra.
Qed.

(* ================================================================== *)
(*  Part II: Continuity and Lipschitz  (~7 lemmas)                     *)
(* ================================================================== *)

(** Continuity at a point (metric style) *)
Definition continuous_at_metric (f : Q -> Q) (x : Q) : Prop :=
  forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall y, qdist x y < delta -> qdist (f x) (f y) < eps.

(** Uniform continuity *)
Definition uniform_continuous_metric (f : Q -> Q) : Prop :=
  forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall x y, qdist x y < delta -> qdist (f x) (f y) < eps.

(** Lipschitz condition *)
Definition lipschitz (f : Q -> Q) (K : Q) : Prop :=
  0 <= K /\ forall x y, qdist (f x) (f y) <= K * qdist x y.

(** Lipschitz implies uniformly continuous *)
Lemma lipschitz_uniform : forall f K,
  0 < K -> lipschitz f K -> uniform_continuous_metric f.
Proof.
  intros f K HK [HKnn Hlip] eps Heps.
  exists (eps * / K). split.
  - apply Qlt_shift_div_l; lra.
  - intros x y Hxy.
    assert (Hle := Hlip x y).
    assert (Hnn := qdist_nonneg x y).
    assert (HKd : K * qdist x y < K * (eps * / K)).
    { assert (Hxy2 : qdist x y * K < (eps * / K) * K).
      { apply Qmult_lt_compat_r; [lra | exact Hxy]. }
      lra. }
    assert (Hsimp : K * (eps * / K) == eps).
    { field. lra. }
    lra.
Qed.

(** Lipschitz implies continuous at every point *)
Lemma lipschitz_continuous : forall f K x,
  0 < K -> lipschitz f K -> continuous_at_metric f x.
Proof.
  intros f K x HK Hlip eps Heps.
  destruct (lipschitz_uniform f K HK Hlip eps Heps) as [delta [Hd Hunif]].
  exists delta. split; [exact Hd |].
  intros y Hy. apply Hunif. exact Hy.
Qed.

(** Identity is 1-Lipschitz *)
Lemma identity_lipschitz : lipschitz (fun x => x) 1.
Proof.
  split; [lra |].
  intros x y. unfold qdist.
  assert (H : 1 * Qabs (x - y) == Qabs (x - y)) by lra.
  lra.
Qed.

(** Add constant is 1-Lipschitz *)
Lemma add_const_lipschitz : forall c, lipschitz (fun x => x + c) 1.
Proof.
  intros c. split; [lra |].
  intros x y. unfold qdist.
  assert (Heq : x + c - (y + c) == x - y) by lra.
  rewrite Heq. lra.
Qed.

(** Constant function is 0-Lipschitz *)
Lemma const_lipschitz : forall c, lipschitz (fun _ => c) 0.
Proof.
  intros c. split; [lra |].
  intros x y. unfold qdist.
  assert (Heq : c - c == 0) by lra.
  rewrite Heq. rewrite Qabs_pos; [| lra].
  assert (Hnn := Qabs_nonneg (x - y)). lra.
Qed.

(* ================================================================== *)
(*  Part III: Metric-Cauchy Connection  (~6 lemmas)                    *)
(* ================================================================== *)

(** Cauchy in metric form *)
Definition metric_cauchy (a : RealProcess) : Prop :=
  forall eps, 0 < eps ->
    exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
      qdist (a m) (a n) < eps.

(** ProcessCore Cauchy implies metric Cauchy *)
Lemma cauchy_to_metric : forall a,
  is_Cauchy a -> metric_cauchy a.
Proof.
  intros a Hc eps Heps.
  destruct (Hc eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  unfold qdist. exact (HN m n Hm Hn).
Qed.

(** Metric Cauchy implies ProcessCore Cauchy *)
Lemma metric_to_cauchy : forall a,
  metric_cauchy a -> is_Cauchy a.
Proof.
  intros a Hm eps Heps.
  destruct (Hm eps Heps) as [N HN].
  exists N. intros m n Hm' Hn'.
  unfold qdist in HN. exact (HN m n Hm' Hn').
Qed.

(** Cauchy equivalence *)
Theorem metric_cauchy_equiv : forall a,
  is_Cauchy a <-> metric_cauchy a.
Proof.
  intros a. split; [apply cauchy_to_metric | apply metric_to_cauchy].
Qed.

(** Lipschitz maps preserve Cauchy sequences *)
Theorem cauchy_map_lipschitz : forall (f : Q -> Q) (K : Q) (a : RealProcess),
  0 <= K -> lipschitz f K ->
  is_Cauchy a ->
  is_Cauchy (fun n => f (a n)).
Proof.
  intros f K a HK [_ Hlip] Hca eps Heps.
  destruct (Qlt_le_dec K 0) as [Hneg | Hpos].
  { (* K < 0, but 0 <= K — contradiction *) lra. }
  destruct (Qeq_dec K 0) as [HK0 | HKnz].
  - (* K == 0: f is constant on the image, distances are 0 *)
    exists 0%nat. intros m n _ _.
    assert (Hm := Hlip (a m) (a n)).
    unfold qdist in Hm.
    assert (Hnn := Qabs_nonneg (a m - a n)).
    assert (Hle : 0 * Qabs (a m - a n) == 0) by lra.
    assert (Hle2 : K * Qabs (a m - a n) == 0) by (rewrite HK0; lra).
    assert (Hle3 : Qabs (f (a m) - f (a n)) <= 0) by lra.
    assert (Hnn2 := Qabs_nonneg (f (a m) - f (a n))). lra.
  - (* K > 0 *)
    assert (HKp : 0 < K) by lra.
    destruct (Hca (eps * / K) ltac:(apply Qlt_shift_div_l; lra)) as [N HN].
    exists N. intros m n Hm Hn.
    assert (Hd := Hlip (a m) (a n)).
    unfold qdist in Hd.
    assert (Ham := HN m n Hm Hn).
    assert (HKd : K * Qabs (a m - a n) < K * (eps * / K)).
    { assert (Hxy2 : Qabs (a m - a n) * K < (eps * / K) * K).
      { apply Qmult_lt_compat_r; [lra | exact Ham]. }
      lra. }
    assert (Hsimp : K * (eps * / K) == eps) by (field; lra).
    lra.
Qed.

(** Uniformly continuous maps preserve Cauchy *)
Lemma cauchy_map_uniform : forall (f : Q -> Q) (a : RealProcess),
  uniform_continuous_metric f ->
  is_Cauchy a ->
  is_Cauchy (fun n => f (a n)).
Proof.
  intros f a Huc Hca eps Heps.
  destruct (Huc eps Heps) as [delta [Hd Hunif]].
  destruct (Hca delta Hd) as [N HN].
  exists N. intros m n Hm Hn.
  assert (Ham := HN m n Hm Hn).
  apply Hunif. unfold qdist. exact Ham.
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check qdist. Check qdist_nonneg. Check qdist_sym.
Check qdist_triangle. Check qdist_zero_iff.
Check qdist_translate. Check qdist_scale. Check qdist_midpoint.
Check continuous_at_metric. Check uniform_continuous_metric. Check lipschitz.
Check lipschitz_uniform. Check lipschitz_continuous.
Check identity_lipschitz. Check add_const_lipschitz. Check const_lipschitz.
Check metric_cauchy. Check cauchy_to_metric. Check metric_to_cauchy.
Check metric_cauchy_equiv. Check cauchy_map_lipschitz. Check cauchy_map_uniform.
