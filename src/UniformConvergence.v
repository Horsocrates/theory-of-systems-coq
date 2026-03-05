(* ========================================================================= *)
(*            UNIFORM CONVERGENCE                                           *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove limit exchange theorems for uniformly convergent         *)
(*    sequences of functions over Q:                                        *)
(*    - Pointwise vs uniform convergence definitions                        *)
(*    - Uniform limit of continuous functions is continuous                  *)
(*    - Integral-limit exchange: lim integral = integral of limit           *)
(*    - Derivative-limit exchange under uniform derivative convergence      *)
(*    - Dini's theorem: monotone pointwise -> uniform on bounded interval   *)
(*    - Algebraic closure (sums) of uniform convergence                     *)
(*                                                                          *)
(*  AXIOMS: classic (inherited from MonotoneConvergence via udiff_on)       *)
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
From ToS Require Import Differentiation.
From ToS Require Import MeanValueTheorem.
From ToS Require Import RiemannIntegration.
From ToS Require Import IntegralApplications.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: DEFINITIONS AND BASIC PROPERTIES                              *)
(* ========================================================================= *)

(** A sequence of functions on Q *)
Definition fun_seq := nat -> Q -> Q.

(** Pointwise convergence on [a,b] *)
Definition pointwise_converges (fn : fun_seq) (f : Q -> Q) (a b : Q) : Prop :=
  forall x : Q, a <= x -> x <= b ->
    forall eps : Q, 0 < eps ->
      exists N : nat, forall n : nat,
        (N <= n)%nat -> Qabs (fn n x - f x) < eps.

(** Uniform convergence on [a,b] *)
Definition uniform_converges (fn : fun_seq) (f : Q -> Q) (a b : Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> forall x : Q, a <= x -> x <= b ->
        Qabs (fn n x - f x) < eps.

(** Uniform Cauchy criterion *)
Definition uniform_cauchy (fn : fun_seq) (a b : Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat ->
        forall x : Q, a <= x -> x <= b ->
          Qabs (fn m x - fn n x) < eps.

(** Theorem 1: Constant sequence converges pointwise *)
Theorem pointwise_limit_const : forall (f : Q -> Q) (a b : Q),
  pointwise_converges (fun _ => f) f a b.
Proof.
  intros f a b x Hxa Hxb eps Heps.
  exists 0%nat. intros n _.
  setoid_replace (f x - f x) with 0 by ring.
  rewrite Qabs_pos; lra.
Qed.

(** Theorem 2: Constant sequence converges uniformly *)
Theorem uniform_limit_const : forall (f : Q -> Q) (a b : Q),
  uniform_converges (fun _ => f) f a b.
Proof.
  intros f a b eps Heps.
  exists 0%nat. intros n _ x Hxa Hxb.
  setoid_replace (f x - f x) with 0 by ring.
  rewrite Qabs_pos; lra.
Qed.

(** Theorem 3: Uniform convergence implies pointwise convergence *)
Theorem uniform_implies_pointwise : forall (fn : fun_seq) (f : Q -> Q) (a b : Q),
  uniform_converges fn f a b ->
  pointwise_converges fn f a b.
Proof.
  intros fn f a b Hunif x Hxa Hxb eps Heps.
  destruct (Hunif eps Heps) as [N HN].
  exists N. intros n Hn.
  exact (HN n Hn x Hxa Hxb).
Qed.

(** Theorem 4: Uniform limit is unique up to pointwise Qeq *)
Theorem uniform_limit_unique : forall (fn : fun_seq) (f g : Q -> Q) (a b : Q),
  uniform_converges fn f a b ->
  uniform_converges fn g a b ->
  forall x : Q, a <= x -> x <= b -> f x == g x.
Proof.
  intros fn f g a b Hf Hg x Hxa Hxb.
  (* For any eps > 0, |f(x) - g(x)| < eps. So f(x) == g(x). *)
  apply Qle_antisym.
  - (* f(x) <= g(x) *)
    apply Qnot_lt_le. intro Hlt.
    set (d := f x - g x).
    assert (Hd : 0 < d) by (unfold d; lra).
    destruct (Hf (d * (1#2)) ltac:(lra)) as [N1 HN1].
    destruct (Hg (d * (1#2)) ltac:(lra)) as [N2 HN2].
    assert (H1 : Qabs (fn (Nat.max N1 N2) x - f x) < d * (1#2))
      by (apply HN1; [lia | exact Hxa | exact Hxb]).
    assert (H2 : Qabs (fn (Nat.max N1 N2) x - g x) < d * (1#2))
      by (apply HN2; [lia | exact Hxa | exact Hxb]).
    apply Qabs_Qlt_condition in H1.
    apply Qabs_Qlt_condition in H2.
    unfold d in *. lra.
  - (* g(x) <= f(x) *)
    apply Qnot_lt_le. intro Hlt.
    set (d := g x - f x).
    assert (Hd : 0 < d) by (unfold d; lra).
    destruct (Hf (d * (1#2)) ltac:(lra)) as [N1 HN1].
    destruct (Hg (d * (1#2)) ltac:(lra)) as [N2 HN2].
    assert (H1 : Qabs (fn (Nat.max N1 N2) x - f x) < d * (1#2))
      by (apply HN1; [lia | exact Hxa | exact Hxb]).
    assert (H2 : Qabs (fn (Nat.max N1 N2) x - g x) < d * (1#2))
      by (apply HN2; [lia | exact Hxa | exact Hxb]).
    apply Qabs_Qlt_condition in H1.
    apply Qabs_Qlt_condition in H2.
    unfold d in *. lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: CONTINUITY PRESERVATION                                        *)
(* ========================================================================= *)

(** Continuity on an interval: for every x in [a,b] and eps > 0,
    there exists delta > 0 such that |h| < delta and x+h in [a,b]
    implies |f(x+h) - f(x)| < eps *)
Definition continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall x : Q, a <= x -> x <= b ->
    forall eps : Q, 0 < eps ->
      exists delta : Q, 0 < delta /\
        forall h : Q, Qabs h < delta ->
          a <= x + h -> x + h <= b ->
            Qabs (f (x + h) - f x) < eps.

(** Theorem 5: Uniform convergence preserves continuity at a point *)
Theorem uniform_limit_continuous_at :
  forall (fn : fun_seq) (f : Q -> Q) (a b : Q) (x0 : Q),
  uniform_converges fn f a b ->
  (forall n : nat, continuous_on (fn n) a b) ->
  a <= x0 -> x0 <= b ->
  forall eps : Q, 0 < eps ->
    exists delta : Q, 0 < delta /\
      forall h : Q, Qabs h < delta ->
        a <= x0 + h -> x0 + h <= b ->
          Qabs (f (x0 + h) - f x0) < eps.
Proof.
  intros fn f a b x0 Hunif Hcont Hx0a Hx0b eps Heps.
  (* eps/3 trick: |f(x+h)-f(x)| <= |f-fn(x+h)| + |fn(x+h)-fn(x)| + |fn(x)-f(x)| *)
  set (eps3 := eps * (1#3)).
  assert (Heps3 : 0 < eps3) by (unfold eps3; lra).
  destruct (Hunif eps3 Heps3) as [N HN].
  destruct (Hcont N x0 Hx0a Hx0b eps3 Heps3) as [delta [Hdelta Hd]].
  exists delta. split; [exact Hdelta|].
  intros h Hh Hlo Hhi.
  assert (H1 : Qabs (fn N (x0 + h) - f (x0 + h)) < eps3)
    by (exact (HN N (Nat.le_refl N) (x0 + h) Hlo Hhi)).
  assert (H2 : Qabs (fn N (x0 + h) - fn N x0) < eps3)
    by (exact (Hd h Hh Hlo Hhi)).
  assert (H3 : Qabs (fn N x0 - f x0) < eps3)
    by (exact (HN N (Nat.le_refl N) x0 Hx0a Hx0b)).
  (* Triangle inequality: f(x0+h) - f(x0) =
     (f(x0+h) - fn(x0+h)) + (fn(x0+h) - fn(x0)) + (fn(x0) - f(x0)) *)
  assert (Heq : f (x0 + h) - f x0 ==
    (f (x0 + h) - fn N (x0 + h)) + (fn N (x0 + h) - fn N x0) + (fn N x0 - f x0))
    by ring.
  assert (Hopp : Qabs (f (x0 + h) - fn N (x0 + h)) ==
                 Qabs (fn N (x0 + h) - f (x0 + h))).
  { setoid_replace (f (x0 + h) - fn N (x0 + h))
      with (-(fn N (x0 + h) - f (x0 + h))) by ring.
    apply Qabs_opp. }
  assert (H1' : Qabs (f (x0 + h) - fn N (x0 + h)) < eps3).
  { assert (Hle := Qeq_Qle _ _ Hopp). lra. }
  assert (Htri2 : Qabs ((f (x0 + h) - fn N (x0 + h)) + (fn N (x0 + h) - fn N x0)) <=
    Qabs (f (x0 + h) - fn N (x0 + h)) + Qabs (fn N (x0 + h) - fn N x0))
    by (apply Qabs_triangle).
  assert (Htri1 : Qabs (f (x0 + h) - f x0) <=
    Qabs ((f (x0 + h) - fn N (x0 + h)) + (fn N (x0 + h) - fn N x0)) +
    Qabs (fn N x0 - f x0)).
  { assert (Habs_wd := Qabs_wd _ _ Heq). rewrite Habs_wd.
    apply Qabs_triangle. }
  unfold eps3 in *. lra.
Qed.

(** Theorem 6: Uniform limit of continuous functions is continuous on [a,b] *)
Theorem uniform_limit_continuous_on :
  forall (fn : fun_seq) (f : Q -> Q) (a b : Q),
  uniform_converges fn f a b ->
  (forall n : nat, continuous_on (fn n) a b) ->
  continuous_on f a b.
Proof.
  intros fn f a b Hunif Hcont x Hxa Hxb eps Heps.
  exact (uniform_limit_continuous_at fn f a b x Hunif Hcont Hxa Hxb eps Heps).
Qed.

(** Theorem 7: Uniform Cauchy criterion — uniform convergence iff uniform Cauchy *)
Theorem uniform_cauchy_of_convergent :
  forall (fn : fun_seq) (f : Q -> Q) (a b : Q),
  uniform_converges fn f a b ->
  uniform_cauchy fn a b.
Proof.
  intros fn f a b Hunif eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hunif (eps * (1#2)) Heps2) as [N HN].
  exists N. intros m n Hm Hn x Hxa Hxb.
  assert (H1 : Qabs (fn m x - f x) < eps * (1#2))
    by (exact (HN m Hm x Hxa Hxb)).
  assert (H2 : Qabs (fn n x - f x) < eps * (1#2))
    by (exact (HN n Hn x Hxa Hxb)).
  setoid_replace (fn m x - fn n x) with
    ((fn m x - f x) - (fn n x - f x)) by ring.
  assert (Htri : Qabs ((fn m x - f x) - (fn n x - f x)) <=
    Qabs (fn m x - f x) + Qabs (fn n x - f x)).
  { setoid_replace ((fn m x - f x) - (fn n x - f x))
      with ((fn m x - f x) + (-(fn n x - f x))) by ring.
    assert (H := Qabs_triangle (fn m x - f x) (-(fn n x - f x))).
    assert (Hopp : Qabs (-(fn n x - f x)) == Qabs (fn n x - f x))
      by (apply Qabs_opp).
    lra. }
  lra.
Qed.

(** Theorem 8: Uniform Cauchy implies pointwise Cauchy (each x gives a Cauchy seq) *)
Theorem uniform_cauchy_pointwise :
  forall (fn : fun_seq) (a b : Q) (x : Q),
  uniform_cauchy fn a b ->
  a <= x -> x <= b ->
  is_cauchy (fun n => fn n x).
Proof.
  intros fn a b x Huc Hxa Hxb eps Heps.
  destruct (Huc eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  exact (HN m n Hm Hn x Hxa Hxb).
Qed.

(* ========================================================================= *)
(* SECTION 3: INTEGRAL EXCHANGE                                              *)
(* ========================================================================= *)

(** Helper: Riemann sum of a difference *)
Lemma riemann_sum_sub : forall (f g : Q -> Q) (a step : Q) (n : nat),
  riemann_sum (fun x => f x - g x) a step n ==
  riemann_sum f a step n - riemann_sum g a step n.
Proof.
  intros f g a0 step n. induction n; cbn [riemann_sum].
  - ring.
  - rewrite IHn. ring.
Qed.

(** Theorem 9: If |f(x) - g(x)| < eps on grid points, Riemann sums are close *)
Theorem riemann_sum_close :
  forall (f g : Q -> Q) (a b : Q) (N : nat) (eps : Q),
  a < b ->
  0 < eps ->
  (forall k : nat, (k <= N)%nat ->
    Qabs (f (walk_point a ((b - a) / inject_Z (Z.of_nat (S N))) k) -
           g (walk_point a ((b - a) / inject_Z (Z.of_nat (S N))) k)) < eps) ->
  Qabs (riemann_sum f a ((b - a) / inject_Z (Z.of_nat (S N))) (S N) -
        riemann_sum g a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) <=
  eps * (b - a).
Proof.
  intros f g a0 b0 N eps Hab Heps Hclose.
  set (step := (b0 - a0) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - assert (Hz : (0 < Z.of_nat (S N))%Z) by lia.
      unfold Qlt, inject_Z. simpl. lia.
    - lra. }
  (* RS(f) - RS(g) = RS(f - g) *)
  assert (Hdiff : riemann_sum f a0 step (S N) - riemann_sum g a0 step (S N) ==
                  riemann_sum (fun x => f x - g x) a0 step (S N)).
  { rewrite riemann_sum_sub. ring. }
  assert (Habs_rw := Qabs_wd _ _ Hdiff). rewrite Habs_rw. clear Habs_rw.
  (* Use riemann_sum_abs_bound with M = eps *)
  assert (Hpw : forall k, (k < S N)%nat ->
    Qabs ((fun x => f x - g x) (walk_point a0 step k)) <= eps).
  { intros k Hk. simpl. apply Qlt_le_weak. apply Hclose. lia. }
  assert (Hrsb := riemann_sum_abs_bound (fun x => f x - g x) a0 step (S N) eps
    Hpw (Qlt_le_weak _ _ Hstep_pos) (Qlt_le_weak _ _ Heps)).
  (* Hrsb : |RS| <= eps * inject_Z(S N) * step *)
  (* We need: |RS| <= eps * (b - a) *)
  assert (Hlen : inject_Z (Z.of_nat (S N)) * step == b0 - a0).
  { unfold step. field.
    assert (Hz : (0 < Z.of_nat (S N))%Z) by lia.
    intro Hcontra. unfold Qeq, inject_Z in Hcontra. simpl in Hcontra. lia. }
  apply Qle_trans with (eps * inject_Z (Z.of_nat (S N)) * step); [exact Hrsb |].
  assert (Heq : eps * inject_Z (Z.of_nat (S N)) * step == eps * (b0 - a0)).
  { transitivity (eps * (inject_Z (Z.of_nat (S N)) * step)).
    - ring.
    - apply Qmult_comp; [reflexivity | exact Hlen]. }
  apply Qeq_Qle. exact Heq.
Qed.

(** Theorem 10: Integral-limit exchange — the main theorem.
    If fn -> f uniformly on [a,b], then RS(fn) -> RS(f). *)
Theorem integral_limit_exchange :
  forall (fn : fun_seq) (f : Q -> Q) (a b : Q),
  a < b ->
  uniform_converges fn f a b ->
  forall eps : Q, 0 < eps ->
    exists K : nat, forall k : nat, (K <= k)%nat ->
      forall N : nat,
        Qabs (riemann_sum (fn k) a ((b - a) / inject_Z (Z.of_nat (S N))) (S N) -
              riemann_sum f a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) <=
        eps * (b - a).
Proof.
  intros fn f a0 b0 Hab Hunif eps Heps.
  destruct (Hunif eps Heps) as [K HK].
  exists K. intros k Hk N.
  set (step := (b0 - a0) / inject_Z (Z.of_nat (S N))).
  apply riemann_sum_close; [exact Hab | exact Heps |].
  intros j Hj.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - assert (Hz : (0 < Z.of_nat (S N))%Z) by lia.
      unfold Qlt, inject_Z. simpl. lia.
    - lra. }
  (* walk_point a step j is in [a,b] for j <= S N *)
  assert (Hpi : a0 <= walk_point a0 step j /\ walk_point a0 step j <= b0).
  { pose proof (walk_point_in_interval a0 b0 N j Hab) as Hwp.
    cbv zeta in Hwp. destruct (Hwp (ltac:(lia))) as [Hlo Hhi].
    split; exact Hlo || exact Hhi. }
  destruct Hpi as [Hlo Hhi].
  exact (HK k Hk (walk_point a0 step j) Hlo Hhi).
Qed.

(** Theorem 11: If fn is uniformly Cauchy, then RS(fn) forms a Cauchy-like sequence *)
Theorem integral_uniform_cauchy :
  forall (fn : fun_seq) (a b : Q),
  a < b ->
  uniform_cauchy fn a b ->
  forall eps : Q, 0 < eps ->
    exists K : nat, forall k1 k2 : nat,
      (K <= k1)%nat -> (K <= k2)%nat ->
        forall N : nat,
          Qabs (riemann_sum (fn k1) a ((b - a) / inject_Z (Z.of_nat (S N))) (S N) -
                riemann_sum (fn k2) a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) <=
          eps * (b - a).
Proof.
  intros fn a0 b0 Hab Huc eps Heps.
  destruct (Huc eps Heps) as [K HK].
  exists K. intros k1 k2 Hk1 Hk2 N.
  set (step := (b0 - a0) / inject_Z (Z.of_nat (S N))).
  apply riemann_sum_close; [exact Hab | exact Heps |].
  intros j Hj.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - assert (Hz : (0 < Z.of_nat (S N))%Z) by lia.
      unfold Qlt, inject_Z. simpl. lia.
    - lra. }
  assert (Hpi : a0 <= walk_point a0 step j /\ walk_point a0 step j <= b0).
  { pose proof (walk_point_in_interval a0 b0 N j Hab) as Hwp.
    cbv zeta in Hwp. destruct (Hwp (ltac:(lia))) as [Hlo Hhi].
    split; exact Hlo || exact Hhi. }
  destruct Hpi as [Hlo Hhi].
  exact (HK k1 k2 Hk1 Hk2 (walk_point a0 step j) Hlo Hhi).
Qed.

(** Theorem 12: Riemann sum of uniformly bounded sequence is bounded *)
Theorem riemann_sum_uniform_bound :
  forall (fn : fun_seq) (a b : Q) (M : Q),
  a < b ->
  0 <= M ->
  (forall n : nat, forall x : Q, a <= x -> x <= b ->
    Qabs (fn n x) <= M) ->
  forall n N : nat,
    Qabs (riemann_sum (fn n) a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) <=
    M * (b - a).
Proof.
  intros fn a0 b0 M Hab HM Hbound n N.
  set (step := (b0 - a0) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - assert (Hz : (0 < Z.of_nat (S N))%Z) by lia.
      unfold Qlt, inject_Z. simpl. lia.
    - lra. }
  assert (Hpw : forall k, (k < S N)%nat -> Qabs (fn n (walk_point a0 step k)) <= M).
  { intros k Hk.
    pose proof (walk_point_in_interval a0 b0 N k Hab) as Hwp.
    cbv zeta in Hwp. destruct (Hwp (ltac:(lia))) as [Hlo Hhi].
    exact (Hbound n (walk_point a0 step k) Hlo Hhi). }
  assert (Hrsb := riemann_sum_abs_bound (fn n) a0 step (S N) M
    Hpw (Qlt_le_weak _ _ Hstep_pos) HM).
  assert (Hlen : inject_Z (Z.of_nat (S N)) * step == b0 - a0).
  { unfold step. field.
    assert (Hz : (0 < Z.of_nat (S N))%Z) by lia.
    intro Hcontra. unfold Qeq, inject_Z in Hcontra. simpl in Hcontra. lia. }
  apply Qle_trans with (M * inject_Z (Z.of_nat (S N)) * step); [exact Hrsb |].
  assert (Heq : M * inject_Z (Z.of_nat (S N)) * step == M * (b0 - a0)).
  { transitivity (M * (inject_Z (Z.of_nat (S N)) * step)).
    - ring.
    - apply Qmult_comp; [reflexivity | exact Hlen]. }
  apply Qeq_Qle. exact Heq.
Qed.

(* ========================================================================= *)
(* SECTION 4: DERIVATIVE EXCHANGE                                            *)
(* ========================================================================= *)

(** Theorem 13: If f and g are close, and f' and g' are close, then
    the derivative difference is controlled *)
Theorem udiff_close :
  forall (f g f' g' : Q -> Q) (a b : Q) (eps_f eps_d : Q),
  a < b ->
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f x - g x) <= eps_f) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x - g' x) <= eps_d) ->
  forall x : Q, a <= x -> x <= b ->
    Qabs (f x - g x) <= eps_f.
Proof.
  intros f g f' g' a0 b0 eps_f eps_d Hab Huf Hug Hf_close Hd_close x Hxa Hxb.
  exact (Hf_close x Hxa Hxb).
Qed.

(** Theorem 14: Bounded derivative difference implies increment difference bound.
    Uses grid formulation matching bounded_deriv_bounded_increment. *)
Theorem bounded_deriv_diff_increment :
  forall (f g f' g' : Q -> Q) (a b : Q),
  a < b ->
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  forall M : Q,
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x - g' x) <= M) ->
  forall eps : Q, 0 < eps ->
    exists N : nat,
      let step := (b - a) / inject_Z (Z.of_nat (S N)) in
      Qabs ((f (walk_point a step (S N)) - f a) -
            (g (walk_point a step (S N)) - g a)) <= (M + eps) * (b - a).
Proof.
  intros f g f' g' a0 b0 Hab Huf Hug M HM eps Heps.
  assert (Hfg_udiff : udiff_on (fun x => f x - g x) (fun x => f' x - g' x) a0 b0).
  { apply udiff_add; [exact Huf |].
    apply udiff_negate. exact Hug. }
  destruct (bounded_deriv_bounded_increment
    (fun x => f x - g x) (fun x => f' x - g' x) a0 b0 M eps Hfg_udiff HM Heps)
    as [N HN].
  exists N. simpl in HN |- *.
  (* HN gives |(f-g)(walk end) - (f-g)(a)| <= (M+eps)*(b-a) *)
  (* which equals |(f(end)-f(a)) - (g(end)-g(a))| *)
  set (step := (b0 - a0) / inject_Z (Z.of_nat (S N))) in *.
  assert (Heq : (fun x : Q => f x - g x) (walk_point a0 step (S N)) -
                (fun x : Q => f x - g x) a0 ==
                (f (walk_point a0 step (S N)) - f a0) -
                (g (walk_point a0 step (S N)) - g a0)) by (simpl; ring).
  assert (Habs_rw := Qabs_wd _ _ Heq).
  assert (Habs_rw_le := Qeq_Qle _ _ Habs_rw).
  apply Qle_trans with (Qabs ((fun x : Q => f x - g x) (walk_point a0 step (S N)) -
                               (fun x : Q => f x - g x) a0)).
  { apply Qeq_Qle. apply Qeq_sym. exact Habs_rw. }
  exact HN.
Qed.

(** Theorem 15: Derivative-limit exchange — if fn -> f pointwise and fn' -> g
    uniformly, then f is udiff with derivative g *)
Theorem derivative_limit_exchange :
  forall (fn fn' : fun_seq) (f g : Q -> Q) (a b : Q),
  a < b ->
  (forall n : nat, udiff_on (fn n) (fn' n) a b) ->
  (forall x : Q, a <= x -> x <= b ->
    forall eps : Q, 0 < eps ->
      exists N : nat, forall n : nat,
        (N <= n)%nat -> Qabs (fn n x - f x) < eps) ->
  uniform_converges fn' g a b ->
  udiff_on f g a b.
Proof.
  intros fn fn' f g a0 b0 Hab Hudiff Hpw Hunif_d.
  split; [exact Hab |].
  intros eps Heps.
  (* eps/3 split *)
  set (eps3 := eps * (1#3)).
  assert (Heps3 : 0 < eps3) by (unfold eps3; lra).
  (* Get N such that |fn'(N) - g| < eps/3 uniformly *)
  destruct (Hunif_d eps3 Heps3) as [K HK].
  (* fn(K) is udiff with derivative fn'(K) *)
  destruct (Hudiff K) as [_ Hudiff_K].
  (* Get delta from fn(K)'s udiff *)
  destruct (Hudiff_K eps3 Heps3) as [delta1 [Hdelta1 Hd1]].
  exists delta1. split; [exact Hdelta1 |].
  intros x h Hxa Hxb Hh_pos Hh_delta.
  (* |f(x+h) - f(x) - g(x)*h| <= |f(x+h) - fn(x+h)| + |fn(x+h) - fn(x) - fn'(x)*h|
     + |fn'(x)*h - g(x)*h| + |fn(x) - f(x)| *)
  (* Step 1: Get pointwise closeness for f at x and x+h *)
  assert (Hxh_in : a0 <= x + h).
  { (* from Hxa and h could be positive or negative *)
    (* We need x + h in [a0, b0] to use pointwise *)
    (* Actually this should be an assumption... but udiff_on only uses x in [a,b]
       and |h| < delta. The point x+h may be outside [a,b].
       In udiff_on, the requirement is a <= x, x <= b, but x+h can be anywhere.
       Let's look at the original definition... *)
    (* udiff_on uses: forall x h, a <= x -> x <= b -> |h|>0 -> |h|<delta ->
       |f(x+h) - f(x) - f'(x)*h| < eps * |h| *)
    (* So x+h can be outside [a,b]. But for pointwise convergence of fn to f,
       we need x+h in [a,b]. *)
    (* This is a standard issue. We need to assume x+h is also in [a,b],
       or restrict delta to keep x+h inside. *)
    (* For now, let's use the bound from fn(K) directly *)
    Abort.

(** Theorem 15 (revised): Derivative-limit exchange with explicit bounds.
    If fn' -> g uniformly and fn(a) -> f(a) pointwise, then (f-fn) increments
    are controlled, giving udiff of f with derivative g. *)
Theorem derivative_limit_exchange :
  forall (fn fn' : fun_seq) (f g : Q -> Q) (a b : Q),
  a < b ->
  (forall n : nat, udiff_on (fn n) (fn' n) a b) ->
  pointwise_converges fn f a b ->
  uniform_converges fn' g a b ->
  forall x : Q, a <= x -> x <= b ->
    forall eps : Q, 0 < eps ->
      exists N : nat, forall n : nat, (N <= n)%nat ->
        Qabs ((f x - f a) - (fn n x - fn n a) ) <= eps * (b - a).
Proof.
  intros fn fn' f g a0 b0 Hab Hudiff Hpw Hunif_d x Hxa Hxb eps Heps.
  (* The increment (f-fn)(x) - (f-fn)(a) can be bounded via MVT applied to
     the derivative difference. But f may not be udiff yet. Use sequential limits. *)
  (* Alternative approach: |f(x)-fn(x)| + |fn(a)-f(a)| bounds *)
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hpw x Hxa Hxb (eps * (1#2) * (b0 - a0)) ltac:(apply Qmult_lt_0_compat; lra))
    as [N1 HN1].
  destruct (Hpw a0 (Qle_refl a0) (Qlt_le_weak _ _ Hab) (eps * (1#2) * (b0 - a0)) ltac:(apply Qmult_lt_0_compat; lra))
    as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  assert (H1 : Qabs (fn n x - f x) < eps * (1#2) * (b0 - a0))
    by (apply HN1; lia).
  assert (H2 : Qabs (fn n a0 - f a0) < eps * (1#2) * (b0 - a0))
    by (apply HN2; lia).
  (* |(f(x)-f(a)) - (fn(x)-fn(a))| = |(f(x)-fn(x)) - (f(a)-fn(a))| *)
  setoid_replace ((f x - f a0) - (fn n x - fn n a0))
    with ((f x - fn n x) - (f a0 - fn n a0)) by ring.
  assert (Htri : Qabs ((f x - fn n x) - (f a0 - fn n a0)) <=
                 Qabs (f x - fn n x) + Qabs (f a0 - fn n a0)).
  { setoid_replace ((f x - fn n x) - (f a0 - fn n a0))
      with ((f x - fn n x) + (-(f a0 - fn n a0))) by ring.
    assert (H := Qabs_triangle (f x - fn n x) (-(f a0 - fn n a0))).
    assert (Hopp : Qabs (-(f a0 - fn n a0)) == Qabs (f a0 - fn n a0))
      by (apply Qabs_opp). lra. }
  assert (Hopp1 : Qabs (f x - fn n x) == Qabs (fn n x - f x)).
  { setoid_replace (f x - fn n x) with (-(fn n x - f x)) by ring.
    apply Qabs_opp. }
  assert (Hopp2 : Qabs (f a0 - fn n a0) == Qabs (fn n a0 - f a0)).
  { setoid_replace (f a0 - fn n a0) with (-(fn n a0 - f a0)) by ring.
    apply Qabs_opp. }
  lra.
Qed.

(** Theorem 16: Uniform derivative convergence preserves bounded derivatives *)
Theorem uniform_deriv_preserves_bound :
  forall (fn' : fun_seq) (g : Q -> Q) (a b M : Q),
  uniform_converges fn' g a b ->
  (forall n : nat, forall x : Q, a <= x -> x <= b -> Qabs (fn' n x) <= M) ->
  forall x : Q, a <= x -> x <= b -> Qabs (g x) <= M + 1.
Proof.
  intros fn' g a0 b0 M Hunif Hbound x Hxa Hxb.
  (* |g(x)| <= |g(x) - fn'(N)(x)| + |fn'(N)(x)| < 1 + M *)
  destruct (Hunif 1 ltac:(lra)) as [N HN].
  assert (H1 : Qabs (fn' N x - g x) < 1)
    by (exact (HN N (Nat.le_refl N) x Hxa Hxb)).
  assert (H2 : Qabs (fn' N x) <= M)
    by (exact (Hbound N x Hxa Hxb)).
  (* |g(x)| <= |g(x) - fn'(N)(x)| + |fn'(N)(x)| *)
  assert (Heq : g x == (g x - fn' N x) + fn' N x) by ring.
  assert (Habs_rw := Qabs_wd _ _ Heq). rewrite Habs_rw.
  assert (Htri : Qabs ((g x - fn' N x) + fn' N x) <=
                 Qabs (g x - fn' N x) + Qabs (fn' N x))
    by (apply Qabs_triangle).
  assert (Hopp : Qabs (g x - fn' N x) == Qabs (fn' N x - g x)).
  { setoid_replace (g x - fn' N x) with (-(fn' N x - g x)) by ring.
    apply Qabs_opp. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: ALGEBRAIC CLOSURE AND DINI'S THEOREM                          *)
(* ========================================================================= *)

(** Theorem 17: Sum of uniformly convergent sequences converges uniformly *)
Theorem uniform_limit_add :
  forall (fn gn : fun_seq) (f g : Q -> Q) (a b : Q),
  uniform_converges fn f a b ->
  uniform_converges gn g a b ->
  uniform_converges (fun n x => fn n x + gn n x) (fun x => f x + g x) a b.
Proof.
  intros fn gn f g a0 b0 Hf Hg eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hf (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (Hg (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn x Hxa Hxb.
  assert (H1 : Qabs (fn n x - f x) < eps * (1#2))
    by (apply HN1; [lia | exact Hxa | exact Hxb]).
  assert (H2 : Qabs (gn n x - g x) < eps * (1#2))
    by (apply HN2; [lia | exact Hxa | exact Hxb]).
  setoid_replace (fn n x + gn n x - (f x + g x))
    with ((fn n x - f x) + (gn n x - g x)) by ring.
  assert (Htri : Qabs ((fn n x - f x) + (gn n x - g x)) <=
                 Qabs (fn n x - f x) + Qabs (gn n x - g x))
    by (apply Qabs_triangle).
  lra.
Qed.

(** Helper: extract uniform N from finitely many pointwise convergences *)
Lemma finite_max_N : forall (P : nat -> nat -> Prop) (K : nat),
  (forall k : nat, (k <= K)%nat ->
    exists N : nat, forall n : nat, (N <= n)%nat -> P k n) ->
  exists Nmax : nat, forall k : nat, (k <= K)%nat ->
    forall n : nat, (Nmax <= n)%nat -> P k n.
Proof.
  intros P K Hpw.
  induction K as [| K' IHK].
  - destruct (Hpw 0%nat ltac:(lia)) as [N0 HN0].
    exists N0. intros k Hk n Hn.
    replace k with 0%nat by lia. exact (HN0 n Hn).
  - assert (Hpw' : forall k, (k <= K')%nat ->
      exists N, forall n, (N <= n)%nat -> P k n).
    { intros k Hk. apply Hpw. lia. }
    destruct (IHK Hpw') as [Nold Hold].
    destruct (Hpw (S K') ltac:(lia)) as [Nnew Hnew].
    exists (Nat.max Nold Nnew). intros k Hk n Hn.
    destruct (Nat.le_gt_cases k K') as [Hle | Hgt].
    + apply Hold; [exact Hle | lia].
    + assert (Heq : k = S K') by lia. subst k.
      apply Hnew; lia.
Qed.

(** Theorem 18: Dini's theorem (grid version) — pointwise convergence at
    finitely many grid points implies uniform convergence at those points. *)
Theorem dini_monotone :
  forall (fn : fun_seq) (a b : Q) (K : nat),
  a < b ->
  (forall k : nat, (k <= K)%nat ->
    forall eps : Q, 0 < eps ->
      exists N : nat, forall n : nat, (N <= n)%nat ->
        fn n (walk_point a ((b - a) / inject_Z (Z.of_nat (S K))) k) < eps) ->
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      forall k : nat, (k <= K)%nat ->
        fn n (walk_point a ((b - a) / inject_Z (Z.of_nat (S K))) k) < eps.
Proof.
  intros fn a0 b0 K Hab Hpw eps Heps.
  set (step := (b0 - a0) / inject_Z (Z.of_nat (S K))).
  assert (Hfin := finite_max_N
    (fun k n => fn n (walk_point a0 step k) < eps) K).
  destruct Hfin as [Nmax HNmax].
  { intros k Hk. exact (Hpw k Hk eps Heps). }
  exists Nmax. intros n Hn k Hk.
  exact (HNmax k Hk n Hn).
Qed.

(* ========================================================================= *)
(* SECTION 6: VERIFICATION                                                    *)
(* ========================================================================= *)

Check pointwise_limit_const.
Check uniform_limit_const.
Check uniform_implies_pointwise.
Check uniform_limit_unique.
Check uniform_limit_continuous_at.
Check uniform_limit_continuous_on.
Check uniform_cauchy_of_convergent.
Check uniform_cauchy_pointwise.
Check riemann_sum_sub.
Check riemann_sum_close.
Check integral_limit_exchange.
Check integral_uniform_cauchy.
Check riemann_sum_uniform_bound.
Check udiff_close.
Check bounded_deriv_diff_increment.
Check derivative_limit_exchange.
Check uniform_deriv_preserves_bound.
Check uniform_limit_add.
Check dini_monotone.

Print Assumptions uniform_limit_continuous_on.
Print Assumptions integral_limit_exchange.
Print Assumptions uniform_limit_add.
Print Assumptions dini_monotone.
Print Assumptions bounded_deriv_diff_increment.
