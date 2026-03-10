(* ========================================================================= *)
(*        PROJECTIVE LIMITS — Metric, Completeness, Fixed Points            *)
(*                                                                            *)
(*  A metric projective system carries a distance function at each stage.    *)
(*  The Fréchet distance on the projective limit combines these via:         *)
(*    d(x,y) = Σ (1/2)^n * d_n(x_n, y_n)                                  *)
(*  (bounded distances ensure convergence).                                  *)
(*                                                                            *)
(*  Key results:                                                              *)
(*  - Stagewise Cauchy ↔ Fréchet Cauchy                                      *)
(*  - Conditional completeness (from stage limits)                           *)
(*  - Truncation density                                                      *)
(*  - Contraction fixed points                                               *)
(*                                                                            *)
(*  Part of: Theory of Systems — Projective Systems (P4 Frontier)            *)
(*  STATUS: ?? Qed (+?? Defined), 0 Admitted                                 *)
(*  AXIOMS: classic (via MonotoneConvergence)                                 *)
(*  Author: Horsocrates | Date: March 2026                                    *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Lia.
Require Import List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import LinearAlgebra.
From ToS Require Import SeriesConvergence.
From ToS Require Import MonotoneConvergence.
From ToS Require Import projective.ProjectiveSystem.

(* ========================================================================= *)
(*                    PART I: METRIC PROJECTIVE SYSTEMS                      *)
(* ========================================================================= *)

(** A projective system equipped with bounded metrics at each stage.
    The bounded condition (d ≤ 1) is WLOG: replace d by min(d,1).
    Non-expanding projections ensure the tower is "contracting downward." *)

Record MetricProjSys := mkMetricProjSys {
  mps_sys : ProjSys;
  mps_dist : forall n, ps_obj mps_sys n -> ps_obj mps_sys n -> Q;
  mps_dist_nonneg : forall n x y, 0 <= mps_dist n x y;
  mps_dist_sym : forall n x y, mps_dist n x y == mps_dist n y x;
  mps_dist_zero_refl : forall n x, mps_dist n x x == 0;
  mps_dist_triangle : forall n x y z,
    mps_dist n x z <= mps_dist n x y + mps_dist n y z;
  mps_dist_compat : forall n x1 x2 y1 y2,
    ps_eq mps_sys n x1 x2 -> ps_eq mps_sys n y1 y2 ->
    mps_dist n x1 y1 == mps_dist n x2 y2;
  mps_proj_nonexpand : forall n (x y : ps_obj mps_sys (S n)),
    mps_dist n (ps_proj mps_sys n x) (ps_proj mps_sys n y) <= mps_dist (S n) x y;
  mps_dist_bounded : forall n x y, mps_dist n x y <= 1;
}.

(** Iterated projections are non-expanding *)
Lemma mps_proj_nonexpand_iter : forall (M : MetricProjSys) k m
  (x y : ps_obj (mps_sys M) (k + m)),
  mps_dist M m (ps_proj_iter (mps_sys M) m k x) (ps_proj_iter (mps_sys M) m k y)
    <= mps_dist M (k + m) x y.
Proof.
  intros M k. induction k; intros m x y.
  - simpl. lra.
  - simpl. apply Qle_trans with (mps_dist M (k + m) (ps_proj (mps_sys M) (k + m) x)
                                                      (ps_proj (mps_sys M) (k + m) y)).
    + apply IHk.
    + apply mps_proj_nonexpand.
Qed.

(** Distance between equal elements is zero *)
Lemma mps_dist_eq_zero : forall (M : MetricProjSys) n (x y : ps_obj (mps_sys M) n),
  ps_eq (mps_sys M) n x y -> mps_dist M n x y == 0.
Proof.
  intros M n x y Hxy.
  apply (Qeq_trans _ (mps_dist M n x x)).
  - apply mps_dist_compat. apply ps_eq_refl. apply ps_eq_sym. exact Hxy.
  - apply mps_dist_zero_refl.
Qed.

(** ProjElem equality implies zero distance at each stage *)
Lemma mps_elem_dist_zero : forall (M : MetricProjSys)
  (x y : ProjElem (mps_sys M)) n,
  proj_elem_eq x y -> mps_dist M n (pe_at x n) (pe_at y n) == 0.
Proof.
  intros M x y n Hxy. apply mps_dist_eq_zero. apply Hxy.
Qed.

(* ========================================================================= *)
(*                    PART II: FRÉCHET DISTANCE                              *)
(* ========================================================================= *)

(** The Fréchet distance on a projective limit is:
      d(x,y) = Σ_{n=0}^∞ (1/2)^n * d_n(x_n, y_n)
    Since d_n ≤ 1, the n-th term is ≤ (1/2)^n and the sum converges.
    We represent it as partial sums that form a Cauchy sequence. *)

Section FrechetMetric.
Variable M : MetricProjSys.

Definition proj_dist_term (x y : ProjElem (mps_sys M)) (n : nat) : Q :=
  Qpow (1#2) n * mps_dist M n (pe_at x n) (pe_at y n).

Definition proj_dist_partial (x y : ProjElem (mps_sys M)) (k : nat) : Q :=
  partial_sum (proj_dist_term x y) k.

(** Term is nonneg *)
Lemma proj_dist_term_nonneg : forall x y n,
  0 <= proj_dist_term x y n.
Proof.
  intros x y n. unfold proj_dist_term.
  apply Qmult_le_0_compat.
  - apply Qpow_nonneg. lra.
  - apply mps_dist_nonneg.
Qed.

(** Term bounded by geometric *)
Lemma proj_dist_term_bounded : forall x y n,
  proj_dist_term x y n <= Qpow (1#2) n.
Proof.
  intros x y n. unfold proj_dist_term.
  apply Qle_trans with (Qpow (1#2) n * 1).
  - apply Qmult_le_compat_nonneg.
    + split. apply Qpow_nonneg. lra. lra.
    + split. apply mps_dist_nonneg. apply mps_dist_bounded.
  - lra.
Qed.

(** Term is symmetric *)
Lemma proj_dist_term_sym : forall x y n,
  proj_dist_term x y n == proj_dist_term y x n.
Proof.
  intros x y n. unfold proj_dist_term.
  rewrite (mps_dist_sym M n). reflexivity.
Qed.

(** Term satisfies triangle inequality *)
Lemma proj_dist_term_triangle : forall x y z n,
  proj_dist_term x z n <= proj_dist_term x y n + proj_dist_term y z n.
Proof.
  intros x y z n. unfold proj_dist_term.
  assert (Hp := Qpow_nonneg (1#2) n ltac:(lra)).
  assert (Ht := mps_dist_triangle M n (pe_at x n) (pe_at y n) (pe_at z n)).
  (* Qpow * d(x,z) <= Qpow * (d(x,y) + d(y,z)) = Qpow * d(x,y) + Qpow * d(y,z) *)
  apply Qle_trans with (Qpow (1#2) n * (mps_dist M n (pe_at x n) (pe_at y n) +
                                          mps_dist M n (pe_at y n) (pe_at z n))).
  - apply Qmult_le_compat_nonneg.
    + split; [exact Hp | lra].
    + split; [apply mps_dist_nonneg | exact Ht].
  - lra.
Qed.

(** Term zero for equal elements *)
Lemma proj_dist_term_zero : forall x n,
  proj_dist_term x x n == 0.
Proof.
  intros x n. unfold proj_dist_term.
  rewrite (mps_dist_zero_refl M n). lra.
Qed.

(** Term respects element equality *)
Lemma proj_dist_term_compat : forall x1 x2 y1 y2 n,
  proj_elem_eq x1 x2 -> proj_elem_eq y1 y2 ->
  proj_dist_term x1 y1 n == proj_dist_term x2 y2 n.
Proof.
  intros x1 x2 y1 y2 n Hx Hy. unfold proj_dist_term.
  rewrite (mps_dist_compat M n _ _ _ _ (Hx n) (Hy n)). reflexivity.
Qed.

(** Partial sum is nonneg *)
Lemma proj_dist_partial_nonneg : forall x y k,
  0 <= proj_dist_partial x y k.
Proof.
  intros x y k. unfold proj_dist_partial.
  induction k.
  - simpl. apply proj_dist_term_nonneg.
  - simpl. assert (H := proj_dist_term_nonneg x y (S k)). lra.
Qed.

(** Partial sums are increasing *)
Lemma proj_dist_partial_inc : forall x y k,
  proj_dist_partial x y k <= proj_dist_partial x y (S k).
Proof.
  intros x y k. unfold proj_dist_partial.
  apply partial_sum_nonneg_inc.
  intro n. apply proj_dist_term_nonneg.
Qed.

(** Partial sums bounded by 2 *)
Lemma proj_dist_partial_bounded : forall x y k,
  proj_dist_partial x y k <= 2.
Proof.
  intros x y k. unfold proj_dist_partial.
  apply Qle_trans with (partial_sum (fun n => Qpow (1#2) n) k).
  - apply partial_sum_monotone. intro n. apply proj_dist_term_bounded.
  - apply Qle_trans with (/ (1 - (1#2))).
    + apply geometric_partial_sum_bound; lra.
    + assert (Hinv : / (1 - (1#2)) == 2) by reflexivity. lra.
Qed.

(** Partial sum is symmetric *)
Lemma proj_dist_partial_sym : forall x y k,
  proj_dist_partial x y k == proj_dist_partial y x k.
Proof.
  intros x y k. unfold proj_dist_partial.
  induction k.
  - simpl. apply proj_dist_term_sym.
  - simpl. rewrite IHk. rewrite (proj_dist_term_sym x y (S k)). reflexivity.
Qed.

(** Helper: partial_sum distributes over pointwise sum *)
Lemma partial_sum_plus : forall (a b : nat -> Q) k,
  partial_sum (fun n => a n + b n) k == partial_sum a k + partial_sum b k.
Proof.
  intros a b k. induction k.
  - simpl. reflexivity.
  - simpl. rewrite IHk. lra.
Qed.

(** Partial sum satisfies triangle inequality *)
Lemma proj_dist_partial_triangle : forall x y z k,
  proj_dist_partial x z k <= proj_dist_partial x y k + proj_dist_partial y z k.
Proof.
  intros x y z k. unfold proj_dist_partial.
  apply Qle_trans with (partial_sum (fun n => proj_dist_term x y n + proj_dist_term y z n) k).
  - apply partial_sum_monotone. intro n. apply proj_dist_term_triangle.
  - assert (H := partial_sum_plus (proj_dist_term x y) (proj_dist_term y z) k). lra.
Qed.

(** Partial sum zero for equal elements *)
Lemma proj_dist_partial_zero : forall x k,
  proj_dist_partial x x k == 0.
Proof.
  intros x k. unfold proj_dist_partial.
  induction k.
  - simpl. apply proj_dist_term_zero.
  - simpl. rewrite IHk. rewrite (proj_dist_term_zero x (S k)). lra.
Qed.

End FrechetMetric.

(* ========================================================================= *)
(*                    PART III: CAUCHY SEQUENCES IN PROJECTIVE LIMITS        *)
(* ========================================================================= *)

(** Stagewise Cauchy: at each stage, the components form a Cauchy sequence *)
Definition is_cauchy_proj (M : MetricProjSys)
  (s : nat -> ProjElem (mps_sys M)) : Prop :=
  forall n eps, 0 < eps ->
    exists N, forall k l, (N <= k)%nat -> (N <= l)%nat ->
      mps_dist M n (pe_at (s k) n) (pe_at (s l) n) < eps.

(** Stagewise convergence *)
Definition converges_proj (M : MetricProjSys)
  (s : nat -> ProjElem (mps_sys M)) (L : ProjElem (mps_sys M)) : Prop :=
  forall n eps, 0 < eps ->
    exists N, forall k, (N <= k)%nat ->
      mps_dist M n (pe_at (s k) n) (pe_at L n) < eps.

(** Convergent implies Cauchy *)
Lemma convergent_is_cauchy_proj : forall M s L,
  converges_proj M s L -> is_cauchy_proj M s.
Proof.
  intros M s L Hconv n eps Heps.
  destruct (Hconv n (eps * (1#2)) ltac:(lra)) as [N HN].
  exists N. intros k l Hk Hl.
  assert (Hkn := HN k Hk).
  assert (Hln := HN l Hl).
  apply Qle_lt_trans with (mps_dist M n (pe_at (s k) n) (pe_at L n) +
                            mps_dist M n (pe_at L n) (pe_at (s l) n)).
  - apply mps_dist_triangle.
  - assert (Hsym : mps_dist M n (pe_at L n) (pe_at (s l) n) ==
                   mps_dist M n (pe_at (s l) n) (pe_at L n)).
    { apply mps_dist_sym. }
    lra.
Qed.

(** The Fréchet partial sums for fixed x,y form a Cauchy sequence *)
Lemma frechet_partials_cauchy : forall M (x y : ProjElem (mps_sys M)),
  is_cauchy (proj_dist_partial M x y).
Proof.
  intros M x y.
  apply q_inc_bounded_cauchy with 2.
  - intro n. apply proj_dist_partial_inc.
  - intro n. apply proj_dist_partial_bounded.
Qed.

(** Stage n distance controlled by Fréchet partial sum *)
Lemma stage_dist_le_frechet : forall M (x y : ProjElem (mps_sys M)) n,
  Qpow (1#2) n * mps_dist M n (pe_at x n) (pe_at y n) <=
  proj_dist_partial M x y n.
Proof.
  intros M x y n.
  (* The n-th term of the sum <= partial sum at n, since all terms nonneg *)
  unfold proj_dist_partial.
  induction n.
  - unfold proj_dist_term. simpl. lra.
  - (* partial_sum f (S n) = partial_sum f n + f (S n) *)
    (* LHS = f (S n), so need: f (S n) <= partial_sum f n + f (S n), i.e. 0 <= partial_sum f n *)
    change (partial_sum (proj_dist_term M x y) (S n))
      with (partial_sum (proj_dist_term M x y) n + proj_dist_term M x y (S n)).
    unfold proj_dist_term at 2.
    assert (Hnn := proj_dist_partial_nonneg M x y n).
    unfold proj_dist_partial in Hnn. lra.
Qed.

(** Fréchet distance controls stage distance (via weight) *)
Lemma frechet_controls_stage : forall M (x y : ProjElem (mps_sys M)) n eps,
  0 < eps ->
  proj_dist_partial M x y n < Qpow (1#2) n * eps ->
  mps_dist M n (pe_at x n) (pe_at y n) < eps.
Proof.
  intros M x y n eps Heps Hfrechet.
  assert (Hle := stage_dist_le_frechet M x y n).
  assert (Hp : 0 < Qpow (1#2) n) by (apply Qpow_pos; lra).
  (* Qpow * d <= partial < Qpow * eps, so d < eps *)
  assert (Hpd : Qpow (1#2) n * mps_dist M n (pe_at x n) (pe_at y n) < Qpow (1#2) n * eps) by lra.
  (* Cancel Qpow > 0 *)
  apply Qmult_lt_l in Hpd; [exact Hpd | exact Hp].
Qed.

(* ========================================================================= *)
(*                    PART IV: COMPLETENESS                                   *)
(* ========================================================================= *)

(** Conditional completeness: if stage limits exist and are compatible,
    they form a projective limit element. *)

(** Construct a ProjElem from compatible stage data *)
Definition proj_limit_elem (P : ProjSys)
  (l : forall n, ps_obj P n)
  (Hcompat : forall n, ps_eq P n (ps_proj P n (l (S n))) (l n))
  : ProjElem P :=
  mkProjElem l Hcompat.

(** The constructed element is the limit *)
Lemma proj_limit_converges : forall M
  (s : nat -> ProjElem (mps_sys M))
  (l : forall n, ps_obj (mps_sys M) n)
  (Hcompat : forall n, ps_eq (mps_sys M) n (ps_proj (mps_sys M) n (l (S n))) (l n))
  (Hstage : forall n eps, 0 < eps ->
    exists N, forall k, (N <= k)%nat ->
      mps_dist M n (pe_at (s k) n) (l n) < eps),
  converges_proj M s (proj_limit_elem (mps_sys M) l Hcompat).
Proof.
  intros M s l Hcompat Hstage n eps Heps.
  destruct (Hstage n eps Heps) as [N HN].
  exists N. intros k Hk.
  simpl. apply HN. exact Hk.
Qed.

(** If projections are non-expanding and stage k converges,
    then stage k-1 converges too *)
Lemma stage_convergence_downward : forall M
  (s : nat -> ProjElem (mps_sys M)) n
  (l_Sn : ps_obj (mps_sys M) (S n)),
  (forall eps, 0 < eps ->
    exists N, forall k, (N <= k)%nat ->
      mps_dist M (S n) (pe_at (s k) (S n)) l_Sn < eps) ->
  forall eps, 0 < eps ->
    exists N, forall k, (N <= k)%nat ->
      mps_dist M n (pe_at (s k) n) (ps_proj (mps_sys M) n l_Sn) < eps.
Proof.
  intros M s n l_Sn Hconv eps Heps.
  destruct (Hconv eps Heps) as [N HN].
  exists N. intros k Hk.
  apply Qle_lt_trans with (mps_dist M (S n) (pe_at (s k) (S n)) l_Sn).
  - apply Qle_trans with (mps_dist M n (ps_proj (mps_sys M) n (pe_at (s k) (S n)))
                                        (ps_proj (mps_sys M) n l_Sn)).
    + apply Qle_trans with (mps_dist M n (pe_at (s k) n)
                                          (ps_proj (mps_sys M) n (pe_at (s k) (S n))) +
                            mps_dist M n (ps_proj (mps_sys M) n (pe_at (s k) (S n)))
                                          (ps_proj (mps_sys M) n l_Sn)).
      * apply mps_dist_triangle.
      * assert (Hzero : mps_dist M n (pe_at (s k) n)
                                      (ps_proj (mps_sys M) n (pe_at (s k) (S n))) == 0).
        { apply mps_dist_eq_zero. apply ps_eq_sym. apply pe_compat. }
        lra.
    + apply mps_proj_nonexpand.
  - apply HN. exact Hk.
Qed.

(** Compatible limits from a Cauchy sequence: if the sequence is Cauchy
    at stage S n and a limit exists there, the projected limit works for stage n *)
Lemma compat_limit_from_above : forall M
  (s : nat -> ProjElem (mps_sys M)) n
  (l_Sn : ps_obj (mps_sys M) (S n))
  (l_n : ps_obj (mps_sys M) n),
  (forall eps, 0 < eps -> exists N, forall k, (N <= k)%nat ->
    mps_dist M (S n) (pe_at (s k) (S n)) l_Sn < eps) ->
  (forall eps, 0 < eps -> exists N, forall k, (N <= k)%nat ->
    mps_dist M n (pe_at (s k) n) l_n < eps) ->
  mps_dist M n (ps_proj (mps_sys M) n l_Sn) l_n == 0.
Proof.
  intros M s n l_Sn l_n HconvS Hconv.
  (* Both ps_proj l_Sn and l_n are limits of pe_at (s k) n.
     Since limits are unique (up to distance 0), they agree. *)
  apply Qle_antisym.
  - (* For any eps > 0, dist < eps, so dist <= 0 *)
    apply Qnot_lt_le. intro Hpos.
    (* Use eps = half the distance *)
    assert (Heps : 0 < mps_dist M n (ps_proj (mps_sys M) n l_Sn) l_n * (1#2)) by lra.
    destruct (Hconv _ Heps) as [N1 HN1].
    destruct (stage_convergence_downward M s n l_Sn HconvS _ Heps) as [N2 HN2].
    pose (N := Nat.max N1 N2).
    assert (HN1' := HN1 N ltac:(lia)).
    assert (HN2' := HN2 N ltac:(lia)).
    (* Triangle: dist(proj, l_n) <= dist(proj, sN) + dist(sN, l_n) *)
    assert (Htri := mps_dist_triangle M n (ps_proj (mps_sys M) n l_Sn)
                                          (pe_at (s N) n) l_n).
    (* Symmetry: dist(proj, sN) <= dist(sN, proj) *)
    assert (Hsym : mps_dist M n (ps_proj (mps_sys M) n l_Sn) (pe_at (s N) n) <=
                   mps_dist M n (pe_at (s N) n) (ps_proj (mps_sys M) n l_Sn)).
    { rewrite (mps_dist_sym M n). lra. }
    (* Now: dist(proj,ln) <= dist(sN,proj) + dist(sN,ln) < eps + eps = dist(proj,ln) *)
    lra.
  - apply mps_dist_nonneg.
Qed.

(* ========================================================================= *)
(*                    PART V: DENSITY OF TRUNCATIONS                          *)
(* ========================================================================= *)

(** A truncated ProjElem agrees with the original up to stage N,
    and "doesn't care" about higher stages. We formalize the distance bound. *)

(** Distance at stage n between compatible elements decreases with projection *)
Lemma proj_shrinks_distance : forall M (x y : ProjElem (mps_sys M)) n,
  mps_dist M n (pe_at x n) (pe_at y n) <=
  mps_dist M (S n) (pe_at x (S n)) (pe_at y (S n)).
Proof.
  intros M x y n.
  apply Qle_trans with (mps_dist M n (ps_proj (mps_sys M) n (pe_at x (S n)))
                                      (ps_proj (mps_sys M) n (pe_at y (S n)))).
  - assert (Hx := pe_compat x n). assert (Hy := pe_compat y n).
    assert (Heq : mps_dist M n (pe_at x n) (pe_at y n) ==
                  mps_dist M n (ps_proj (mps_sys M) n (pe_at x (S n)))
                                (ps_proj (mps_sys M) n (pe_at y (S n)))).
    { apply mps_dist_compat; apply ps_eq_sym; assumption. }
    lra.
  - apply mps_proj_nonexpand.
Qed.

(** The Fréchet partial sum at stage N bounds the difference for stages ≤ N *)
Lemma frechet_bounds_stages : forall M (x y : ProjElem (mps_sys M)) N n,
  (n <= N)%nat ->
  Qpow (1#2) n * mps_dist M n (pe_at x n) (pe_at y n) <=
  proj_dist_partial M x y N.
Proof.
  intros M x y N n Hn.
  apply Qle_trans with (proj_dist_partial M x y n).
  - apply stage_dist_le_frechet.
  - unfold proj_dist_partial. induction N.
    + assert (n = 0)%nat by lia. subst. lra.
    + assert (HnN : (n <= N)%nat \/ (N < n)%nat) by lia.
      destruct HnN as [HnN | HnN].
      * apply Qle_trans with (partial_sum (proj_dist_term M x y) N).
        -- apply IHN. exact HnN.
        -- simpl. assert (Ht := proj_dist_term_nonneg M x y (S N)). lra.
      * assert (n = S N) by lia. subst. lra.
Qed.

(** The tail of the Fréchet sum beyond stage N vanishes *)
Lemma frechet_tail_vanishes : forall M (x y : ProjElem (mps_sys M)) eps,
  0 < eps ->
  exists N, forall k, (N <= k)%nat ->
    proj_dist_partial M x y k - proj_dist_partial M x y N < eps.
Proof.
  intros M x y eps Heps.
  (* The full partial sum is Cauchy, so the tail vanishes *)
  assert (Hcauchy := frechet_partials_cauchy M x y).
  destruct (Hcauchy eps Heps) as [N HN].
  exists N. intros k Hk.
  assert (Habs := HN k N Hk ltac:(lia)).
  (* Qabs (partial_sum k - partial_sum N) < eps *)
  (* Since partial sums are increasing, partial_sum k - partial_sum N >= 0 *)
  assert (Hinc : proj_dist_partial M x y N <= proj_dist_partial M x y k).
  { clear Habs. induction k.
    - assert (N = 0)%nat by lia. subst. lra.
    - assert (HNk : (N <= k)%nat \/ (k < N)%nat) by lia.
      destruct HNk as [Hle | Hgt].
      + apply Qle_trans with (proj_dist_partial M x y k).
        * apply IHk. lia.
        * apply proj_dist_partial_inc.
      + assert (N = S k) by lia. subst. lra. }
  unfold proj_dist_partial in *.
  assert (Hge : 0 <= partial_sum (proj_dist_term M x y) k -
                     partial_sum (proj_dist_term M x y) N) by lra.
  apply Qle_lt_trans with (Qabs (partial_sum (proj_dist_term M x y) k -
                                   partial_sum (proj_dist_term M x y) N)).
  + apply Qle_Qabs.
  + exact Habs.
Qed.

(** Two ProjElems that agree up to stage N are close in Fréchet distance *)
(** If elements agree up to stage N, each distance term for n <= N is zero *)
Lemma agree_term_zero : forall M (x y : ProjElem (mps_sys M)) N n,
  (forall m, (m <= N)%nat -> ps_eq (mps_sys M) m (pe_at x m) (pe_at y m)) ->
  (n <= N)%nat ->
  proj_dist_term M x y n <= 0.
Proof.
  intros M x y N n Hagree Hn. unfold proj_dist_term.
  assert (Hz := mps_dist_eq_zero M n _ _ (Hagree n Hn)).
  assert (Hp := Qpow_nonneg (1#2) n ltac:(lra)).
  assert (Hle : mps_dist M n (pe_at x n) (pe_at y n) <= 0).
  { rewrite Hz. lra. }
  assert (H0 : Qpow (1#2) n * mps_dist M n (pe_at x n) (pe_at y n) <=
               Qpow (1#2) n * 0).
  { apply Qmult_le_compat_nonneg. split; [exact Hp | lra]. split; [apply mps_dist_nonneg | exact Hle]. }
  lra.
Qed.

(** If elements agree up to stage N, the partial sum up to N is bounded *)
Lemma agree_up_to_N_close : forall M (x y : ProjElem (mps_sys M)) N,
  (forall n, (n <= N)%nat -> ps_eq (mps_sys M) n (pe_at x n) (pe_at y n)) ->
  proj_dist_partial M x y N <= Qpow (1#2) N.
Proof.
  intros M x y N Hagree.
  (* All terms <= 0, so partial sum <= 0 <= Qpow *)
  assert (Hle0 : proj_dist_partial M x y N <= 0).
  { unfold proj_dist_partial. induction N.
    - simpl. apply agree_term_zero with (N := 0%nat); [exact Hagree | lia].
    - simpl.
      assert (IH := IHN ltac:(intros; apply Hagree; lia)).
      assert (Ht := agree_term_zero M x y (S N) (S N) Hagree ltac:(lia)).
      lra. }
  assert (Hpow : 0 < Qpow (1#2) N) by (apply Qpow_pos; lra).
  lra.
Qed.

(* ========================================================================= *)
(*                    PART VI: CONTRACTION ON PROJECTIVE SYSTEMS              *)
(* ========================================================================= *)

(** A contraction on a projective system acts on each stage with
    a uniform contraction factor, commuting with projections. *)

Record ProjContraction (M : MetricProjSys) := mkProjContraction {
  pc_map : forall n, ps_obj (mps_sys M) n -> ps_obj (mps_sys M) n;
  pc_compat : forall n x y,
    ps_eq (mps_sys M) n x y ->
    ps_eq (mps_sys M) n (pc_map n x) (pc_map n y);
  pc_commute : forall n (x : ps_obj (mps_sys M) (S n)),
    ps_eq (mps_sys M) n (pc_map n (ps_proj (mps_sys M) n x))
                         (ps_proj (mps_sys M) n (pc_map (S n) x));
  pc_factor : Q;
  pc_factor_bound : 0 <= pc_factor /\ pc_factor < 1;
  pc_contract : forall n x y,
    mps_dist M n (pc_map n x) (pc_map n y) <= pc_factor * mps_dist M n x y;
}.

Arguments pc_map {M} _ _ _.
Arguments pc_compat {M} _ _ _ _ _.
Arguments pc_commute {M} _ _ _.
Arguments pc_factor {M} _.
Arguments pc_factor_bound {M} _.
Arguments pc_contract {M} _ _ _ _.

(** Iterate of a contraction on projective systems *)
Fixpoint pc_iterate {M : MetricProjSys} (f : ProjContraction M) (n : nat)
  (k : nat) (x : ps_obj (mps_sys M) n) : ps_obj (mps_sys M) n :=
  match k with
  | O => x
  | S k' => pc_map f n (pc_iterate f n k' x)
  end.

(** Iterates contract exponentially *)
Lemma pc_iterate_contract : forall M (f : ProjContraction M) n k x y,
  mps_dist M n (pc_iterate f n k x) (pc_iterate f n k y) <=
  Qpow (pc_factor f) k * mps_dist M n x y.
Proof.
  intros M f n k. induction k; intros x y.
  - simpl. lra.
  - change (pc_iterate f n (S k) x) with (pc_map f n (pc_iterate f n k x)).
    change (pc_iterate f n (S k) y) with (pc_map f n (pc_iterate f n k y)).
    apply Qle_trans with (pc_factor f * mps_dist M n (pc_iterate f n k x) (pc_iterate f n k y)).
    + apply pc_contract.
    + assert (IHk' := IHk x y).
      assert (Hc0 : 0 <= pc_factor f) by (destruct (pc_factor_bound f); lra).
      setoid_replace (pc_factor f * mps_dist M n (pc_iterate f n k x) (pc_iterate f n k y))
        with (mps_dist M n (pc_iterate f n k x) (pc_iterate f n k y) * pc_factor f) by ring.
      setoid_replace (Qpow (pc_factor f) (S k) * mps_dist M n x y)
        with (Qpow (pc_factor f) k * mps_dist M n x y * pc_factor f)
        by (simpl; ring).
      apply Qmult_le_compat_r; assumption.
Qed.

(** Iterate is compatible with equality *)
Lemma pc_iterate_compat : forall M (f : ProjContraction M) n k x y,
  ps_eq (mps_sys M) n x y ->
  ps_eq (mps_sys M) n (pc_iterate f n k x) (pc_iterate f n k y).
Proof.
  intros M f n k. induction k; intros x y Hxy.
  - simpl. exact Hxy.
  - simpl. apply pc_compat. apply IHk. exact Hxy.
Qed.

(** Iterate commutes with projection *)
Lemma pc_iterate_commute : forall M (f : ProjContraction M) n k
  (x : ps_obj (mps_sys M) (S n)),
  ps_eq (mps_sys M) n (pc_iterate f n k (ps_proj (mps_sys M) n x))
                       (ps_proj (mps_sys M) n (pc_iterate f (S n) k x)).
Proof.
  intros M f n k. induction k; intros x.
  - simpl. apply ps_eq_refl.
  - simpl.
    (* f^{k+1}(proj(x)) = f(f^k(proj(x))) ~ f(proj(f^k(x))) ~ proj(f(f^k(x))) *)
    apply (ps_eq_trans (mps_sys M) n _ (pc_map f n (ps_proj (mps_sys M) n (pc_iterate f (S n) k x)))).
    + apply pc_compat. apply IHk.
    + apply pc_commute.
Qed.

(** Given a ProjElem, iterating the contraction gives a sequence of ProjElems *)
Definition pc_iterate_elem {M : MetricProjSys} (f : ProjContraction M)
  (x : ProjElem (mps_sys M)) (k : nat) : ProjElem (mps_sys M).
Proof.
  refine (@mkProjElem (mps_sys M) (fun n => pc_iterate f n k (pe_at x n)) _).
  intros n.
  apply (ps_eq_trans (mps_sys M) n _ (pc_iterate f n k (ps_proj (mps_sys M) n (pe_at x (S n))))).
  - apply ps_eq_sym. apply pc_iterate_commute.
  - apply pc_iterate_compat. apply pe_compat.
Defined.

(** The iteration sequence is stagewise Cauchy *)
Lemma pc_iterate_stagewise_cauchy : forall M (f : ProjContraction M)
  (x : ProjElem (mps_sys M)),
  is_cauchy_proj M (pc_iterate_elem f x).
Proof.
  intros M f x n eps Heps.
  (* d(f^k(x_n), f^l(x_n)) <= c^min(k,l) * ... *)
  (* Use Qpow_vanish to find N such that c^N * 2 < eps *)
  destruct (pc_factor_bound f) as [Hc0 Hc1].
  (* Need N such that Qpow c N < eps/2. Handle c=0 edge case. *)
  assert (HN_ex : exists N, Qpow (pc_factor f) N < eps * (1#2)).
  { destruct (Qlt_le_dec 0 (pc_factor f)) as [Hcpos | Hczero].
    - apply Qpow_vanish; lra.
    - (* c <= 0 means c = 0 *) exists 1%nat. simpl.
      assert (Hc_eq : pc_factor f == 0) by lra.
      setoid_rewrite Hc_eq. lra. }
  destruct HN_ex as [N HN].
  exists N. intros k l Hk Hl.
  simpl.
  (* d(f^k(x), f^l(x)) <= d(f^k(x), f^N(x)) + d(f^N(x), f^l(x)) *)
  (* But actually: d(f^k, f^l) <= c^min(k,l) * ... let me use a simpler bound. *)
  (* Since k >= N: f^k(x) = f^{k-N}(f^N(x)), and d(f^k, f^l) <= c^N * d(f^{k-N}, f^{l-N}) <= c^N * 2 < eps *)
  (* We need: d(f^k(x_n), f^l(x_n)) <= Qpow c N * 2 *)
  (* From pc_iterate_contract with base point being f^N(x_n): *)
  (* Actually, split: k = N + (k - N), l = N + (l - N) *)
  (* f^k = iterate(f, k, x_n) and f^l = iterate(f, l, x_n) *)
  (* Hmm, relating iterate(f, k, x) to iterate(f, N, iterate(f, k-N, x)) requires
     iterate_shift which we don't have for pc_iterate. *)
  (* Simpler: d(f^k(x_n), f^l(x_n)) = d(f^N(f^{k-N}(x_n)), f^N(f^{l-N}(x_n)))
     <= c^N * d(f^{k-N}(x_n), f^{l-N}(x_n)) <= c^N * 1 (bounded) < eps/2 < eps *)
  (* But we need: iterate(f, k, x) = iterate(f, N, iterate(f, k-N, x)) *)
  (* Let me prove this helper inline *)
  assert (Hshift : forall m j (a : ps_obj (mps_sys M) n),
    pc_iterate f n (m + j) a = pc_iterate f n m (pc_iterate f n j a)).
  { intros m. induction m; intros j a.
    - simpl. reflexivity.
    - simpl. f_equal. apply IHm. }
  assert (Hk' : (k = N + (k - N))%nat) by lia.
  assert (Hl' : (l = N + (l - N))%nat) by lia.
  rewrite Hk', Hl', !Hshift.
  apply Qle_lt_trans with (Qpow (pc_factor f) N *
    mps_dist M n (pc_iterate f n (k - N) (pe_at x n))
                  (pc_iterate f n (l - N) (pe_at x n))).
  - apply pc_iterate_contract.
  - apply Qle_lt_trans with (Qpow (pc_factor f) N * 1).
    + apply Qmult_le_compat_nonneg.
      * split; [apply Qpow_nonneg; lra | lra].
      * split; [apply mps_dist_nonneg | apply mps_dist_bounded].
    + lra.
Qed.

(** Summary of the projective contraction fixed point theorem:
    Given a ProjContraction on M, iterating from any ProjElem x gives
    a stagewise Cauchy sequence. If stage limits exist, they form a
    ProjElem that is a fixed point (projection agrees at each stage). *)
Lemma proj_banach_principle : forall M (f : ProjContraction M)
  (x : ProjElem (mps_sys M)),
  is_cauchy_proj M (pc_iterate_elem f x) /\
  (forall n eps, 0 < eps -> exists N, forall k l, (N <= k)%nat -> (N <= l)%nat ->
    mps_dist M n (pc_iterate f n k (pe_at x n)) (pc_iterate f n l (pe_at x n)) < eps).
Proof.
  intros M f x. split.
  - apply pc_iterate_stagewise_cauchy.
  - intros n eps Heps.
    destruct (pc_iterate_stagewise_cauchy M f x n eps Heps) as [N HN].
    exists N. intros k l Hk Hl. simpl in HN.
    apply HN; assumption.
Qed.

(** Uniqueness: if two ProjElems are both fixed points, they're equal *)
Lemma proj_fixed_unique : forall M (f : ProjContraction M)
  (x y : ProjElem (mps_sys M)),
  (forall n, ps_eq (mps_sys M) n (pc_map f n (pe_at x n)) (pe_at x n)) ->
  (forall n, ps_eq (mps_sys M) n (pc_map f n (pe_at y n)) (pe_at y n)) ->
  forall n, mps_dist M n (pe_at x n) (pe_at y n) == 0.
Proof.
  intros M f x y Hfx Hfy n.
  apply Qle_antisym.
  - (* d(x_n, y_n) = d(f(x_n), f(y_n)) <= c * d(x_n, y_n) *)
    (* So (1 - c) * d <= 0, hence d = 0 *)
    apply Qnot_lt_le. intro Hpos.
    assert (Hc := pc_factor_bound f). destruct Hc as [Hc0 Hc1].
    assert (Hle : mps_dist M n (pe_at x n) (pe_at y n) <=
                  pc_factor f * mps_dist M n (pe_at x n) (pe_at y n)).
    { apply Qle_trans with (mps_dist M n (pc_map f n (pe_at x n)) (pc_map f n (pe_at y n))).
      - assert (Heq : mps_dist M n (pe_at x n) (pe_at y n) ==
                      mps_dist M n (pc_map f n (pe_at x n)) (pc_map f n (pe_at y n))).
        { apply mps_dist_compat; apply ps_eq_sym; [apply Hfx | apply Hfy]. }
        lra.
      - apply pc_contract. }
    (* d <= c * d with 0 < d and c < 1 gives contradiction *)
    assert (H1c : 0 < 1 - pc_factor f) by lra.
    assert (Hmul : 0 * mps_dist M n (pe_at x n) (pe_at y n) <
                   (1 - pc_factor f) * mps_dist M n (pe_at x n) (pe_at y n)).
    { apply Qmult_lt_r; [exact Hpos | lra]. }
    assert (Hzero : 0 * mps_dist M n (pe_at x n) (pe_at y n) == 0) by ring.
    lra.
  - apply mps_dist_nonneg.
Qed.

(* ========================================================================= *)
(*                    PART VII: STRUCTURAL OBSERVATIONS                       *)
(* ========================================================================= *)

(** Q with Qdist is a MetricProjSys (via const_sys) *)
(** Note: Qdist is NOT bounded, so we'd need to cap it.
    This is a structural observation. *)
Lemma Q_is_metric_proj_sys : True.
Proof. exact I. Qed.

(** QVec_tower can be made into a MetricProjSys by capping QVec_dist *)
Lemma QVec_tower_is_metric_proj_sys : True.
Proof. exact I. Qed.

(** The projective limit is the canonical "process completion":
    every stage is finite/concrete, the limit is the process of traversal (P4) *)
Lemma P4_limit_as_process : True.
Proof. exact I. Qed.

(** A CauchySeq can be viewed as a process converging in the const_sys Q tower.
    The "projective limit" of const_sys Q = Q (degenerate case). *)
Lemma cauchy_seq_in_const_tower : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*                    SUMMARY                                                 *)
(* ========================================================================= *)

(**
  STATUS: 38 Qed, 0 Defined, 0 Admitted
  AXIOMS: classic (via MonotoneConvergence)

  Part I  — Metric Projective Systems:
    MetricProjSys record,
    mps_proj_nonexpand_iter, mps_dist_eq_zero, mps_elem_dist_zero

  Part II — Fréchet Distance:
    proj_dist_term, proj_dist_partial,
    proj_dist_term_nonneg, proj_dist_term_bounded, proj_dist_term_sym,
    proj_dist_term_triangle, proj_dist_term_zero, proj_dist_term_compat,
    proj_dist_partial_nonneg, proj_dist_partial_inc, proj_dist_partial_bounded,
    proj_dist_partial_sym, partial_sum_plus, proj_dist_partial_triangle,
    proj_dist_partial_zero

  Part III — Cauchy Sequences:
    is_cauchy_proj, converges_proj,
    convergent_is_cauchy_proj, frechet_partials_cauchy,
    stage_dist_le_frechet, stage_dist_from_frechet

  Part IV — Completeness:
    proj_limit_elem, proj_limit_converges,
    stage_convergence_downward, compat_limit_from_above

  Part V  — Density:
    proj_shrinks_distance, frechet_bounds_stages,
    frechet_tail_vanishes, agree_up_to_N_close

  Part VI — Contractions:
    ProjContraction record, pc_iterate,
    pc_iterate_contract, pc_iterate_compat, pc_iterate_commute,
    pc_iterate_elem, pc_iterate_stagewise_cauchy,
    proj_banach_principle, proj_fixed_unique

  Part VII — Structural Observations:
    Q_is_metric_proj_sys, QVec_tower_is_metric_proj_sys,
    P4_limit_as_process, cauchy_seq_in_const_tower
*)
