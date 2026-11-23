(** * ProcessPicardStepContraction.v -- The Picard operator with the integral process on functions Q -> Q: contraction, geometric gap, uniform Cauchy property of the iterates, as a ToS System

    Elements: functions y : Q -> Q read at the rational points of [0, T];
              the iterates [picard_iterate f y0 n t N] (ProcessPicard.v); the
              stage N of the integral process (a Riemann sum with N + 1 pieces
              on [0, t]); the natural numbers n (iteration) and N (stage).
    Roles:    [picard_step] -- role-operator on functions: it turns a whole
              candidate y into the function t |-> y0 + (stage N of the
              integral of f(s, y(s)) over [0, t]); a bound D of |y - z| on
              [0, t] -- role-metric (uniform distance over the rational points
              of the segment); L * T -- role-rate; the number K of the
              convergence theorems -- role-modulus, one for all stages N.
    Rules:    the difference of two images is a Riemann sum of the difference
              of the integrands; every node of that sum lies in [0, t]; hence
              |Phi(y)(t) - Phi(z)(t)| <= (L t) D at every stage N. A sequence
              with the gap |a_(n+1) - a_n| <= r^n C, r < 1, is a Cauchy
              process, with a number that depends on r, C and eps only.

    Proved (no axioms):
      - [geom_gap_modulus], [geom_gap_is_cauchy]: "geometric gap => Cauchy
        process" for an arbitrary rational sequence; the number is common to
        all sequences with the given r and C;
      - [picard_step_contraction]: the operator [picard_step] contracts the
        uniform distance on [0, t] with the coefficient L t -- for a
        right-hand side Lipschitz in y, at every stage N;
      - [picard_iterate_gap]: the gap of the iterates on [0, T] is at most
        (L T)^n C;
      - [picard_iterate_uniformly_cauchy]: for L T < 1 the iterates form a
        Cauchy process uniformly over the rational points of [0, T];
      - [picard_first_gap_bound], [picard_iterate_modulus_stage_free]: if
        |f(s, y0)| <= M0 on [0, T], the first gap is at most M0 T, and the
        number from which the iterates are eps-close is chosen before the
        stage N of the integral process;
      - [picard_iterate_linear_uniformly_cauchy]: the premises are
        satisfiable (f(t, y) = y, y0 = 1, the segment [0, 1/2]).

    P4 diagnostic: at a fixed stage N the operator reads the candidate at
      finitely many rational nodes, and every statement is an inequality
      between rationals. "The space of functions" is not a completed object
      here: it is the functions Q -> Q together with a uniform bound over the
      rational points of a segment. The stage N of the integral and the number
      n of the iteration are two directions of one process; no limit is taken
      along either of them.

    NOT claimed:
      - a limit over the stage N (the integral as a completed value), or that
        the iterates of different stages draw together;
      - that a fixed point of the operator at a stage N exists as a function
        Q -> Q, or that it solves the differential equation;
      - the completed space C([a, b]) and its completeness;
      - anything for a right-hand side that is Lipschitz only locally, or
        outside the regime L T < 1.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import CauchyReal SeriesConvergence FixedPoint.
From ToS Require Import MeanValueTheorem RiemannIntegration.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessDerivative.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import process.ProcessPicard.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. "Geometric gap => Cauchy process", without axioms                  *)
(*     The number K depends on r, C, eps only: it is common to all        *)
(*     sequences with such a gap.                                         *)
(* ===================================================================== *)

Lemma geom_gap_tel : forall (a : nat -> Q) (r C : Q),
  0 <= r -> r < 1 -> 0 <= C ->
  (forall n, Qabs (a (S n) - a n) <= Qpow r n * C) ->
  forall n m, (n <= m)%nat ->
    (1 - r) * Qabs (a m - a n) <= C * (Qpow r n - Qpow r m).
Proof.
  intros a r C Hr0 Hr1 HC Hgap n m. induction m as [|m IH]; intros Hnm.
  - assert (n = 0%nat) by lia. subst n.
    setoid_replace (a 0%nat - a 0%nat) with 0 by ring.
    setoid_replace (Qpow r 0 - Qpow r 0) with 0 by ring.
    change (Qabs 0) with 0. lra.
  - destruct (Nat.eq_dec n (S m)) as [E|E].
    + subst n.
      setoid_replace (a (S m) - a (S m)) with 0 by ring.
      setoid_replace (Qpow r (S m) - Qpow r (S m)) with 0 by ring.
      change (Qabs 0) with 0. lra.
    + assert (Hnm' : (n <= m)%nat) by lia. specialize (IH Hnm').
      pose proof (Hgap m) as Hs.
      assert (Htri : Qabs (a (S m) - a n)
                     <= Qabs (a (S m) - a m) + Qabs (a m - a n)).
      { setoid_replace (a (S m) - a n) with ((a (S m) - a m) + (a m - a n)) by ring.
        apply Qabs_triangle. }
      cbn [Qpow].
      assert (Hm1 : (1 - r) * Qabs (a (S m) - a n)
                    <= (1 - r) * (Qabs (a (S m) - a m) + Qabs (a m - a n)))
        by (apply FixedPoint.Qmult_le_compat_l; [ exact Htri | lra ]).
      assert (Hm2 : (1 - r) * Qabs (a (S m) - a m) <= (1 - r) * (Qpow r m * C))
        by (apply FixedPoint.Qmult_le_compat_l; [ exact Hs | lra ]).
      lra.
Qed.

Theorem geom_gap_modulus : forall (r C eps : Q),
  0 <= r -> r < 1 -> 0 <= C -> 0 < eps ->
  exists K : nat, forall a : nat -> Q,
    (forall n, Qabs (a (S n) - a n) <= Qpow r n * C) ->
    forall m n, (K <= m)%nat -> (K <= n)%nat -> Qabs (a m - a n) < eps.
Proof.
  intros r C eps Hr0 Hr1 HC Heps.
  assert (H1r : 0 < 1 - r) by lra.
  assert (Ht : 0 < eps * (1 - r) / (C + 1)).
  { apply Qlt_shift_div_l; [ lra | ].
    assert (0 < eps * (1 - r)) by (apply Qmult_lt_0_compat; lra). lra. }
  destruct (Qpow_limit_zero r Hr0 Hr1 _ Ht) as [K HK].
  exists K. intros a Hgap.
  assert (Key : forall n m, (K <= n)%nat -> (n <= m)%nat -> Qabs (a m - a n) < eps).
  { intros n m Hn Hnm.
    pose proof (geom_gap_tel a r C Hr0 Hr1 HC Hgap n m Hnm) as Htel.
    pose proof (HK n Hn) as HPn.
    assert (HPm : 0 <= Qpow r m) by (apply SeriesConvergence.Qpow_nonneg; exact Hr0).
    assert (HPn0 : 0 <= Qpow r n) by (apply SeriesConvergence.Qpow_nonneg; exact Hr0).
    assert (HPnC : Qpow r n * (C + 1) < eps * (1 - r)).
    { assert (H1 : Qpow r n * (C + 1) < eps * (1 - r) / (C + 1) * (C + 1))
        by (apply Qmult_lt_compat_r; [ lra | exact HPn ]).
      assert (H2 : eps * (1 - r) / (C + 1) * (C + 1) == eps * (1 - r)) by (field; lra).
      lra. }
    assert (HCPm : 0 <= C * Qpow r m) by (apply Qmult_le_0_compat; assumption).
    assert (HA : (1 - r) * Qabs (a m - a n) < (1 - r) * eps) by lra.
    apply (proj1 (Qmult_lt_l _ _ (1 - r) H1r)). exact HA. }
  intros m n Hm Hn. destruct (Nat.le_ge_cases n m) as [H|H].
  - apply Key; assumption.
  - rewrite Qabs_Qminus. apply Key; assumption.
Qed.

Corollary geom_gap_is_cauchy : forall (a : nat -> Q) (r C : Q),
  0 <= r -> r < 1 -> 0 <= C ->
  (forall n, Qabs (a (S n) - a n) <= Qpow r n * C) -> is_cauchy a.
Proof.
  intros a r C Hr0 Hr1 HC Hgap eps Heps.
  destruct (geom_gap_modulus r C eps Hr0 Hr1 HC Heps) as [K HK].
  exists K. intros m n Hm Hn. apply (HK a Hgap); assumption.
Qed.

(* ===================================================================== *)
(*  2. The Picard operator with the integral process (picard_step)        *)
(*     On functions Q -> Q: if y and z are uniformly close on [0, t],     *)
(*     their images differ at the point t by at most L t D -- at every    *)
(*     stage N of the integral process.                                   *)
(* ===================================================================== *)

Lemma riemann_sum_sub : forall (F G : Q -> Q) (a step : Q) (n : nat),
  riemann_sum (fun x => F x - G x) a step n
  == riemann_sum F a step n - riemann_sum G a step n.
Proof.
  intros F G a step n. induction n as [|n IH]; cbn [riemann_sum].
  - ring.
  - rewrite IH. ring.
Qed.

(** The nodes of the stage N on [0, t] lie in [0, t]. *)
Lemma walk_point_0_range : forall (t : Q) (N k : nat), 0 <= t -> (k <= N)%nat ->
  0 <= walk_point 0 (integral_step 0 t N) k /\
  walk_point 0 (integral_step 0 t N) k <= t.
Proof.
  intros t N k Ht Hk. rewrite walk_point_qeq. unfold integral_step.
  set (d := inject_Z (Z.of_nat (S N))).
  assert (Hd : 0 < d) by apply inject_Z_Sn_pos.
  assert (Hk0 : 0 <= inject_Z (Z.of_nat k))
    by (change 0 with (inject_Z 0); rewrite <- Zle_Qle; lia).
  assert (Hkd : inject_Z (Z.of_nat k) <= d) by (unfold d; rewrite <- Zle_Qle; lia).
  assert (Hs : 0 <= (t - 0) / d) by (apply Qle_shift_div_l; lra).
  split.
  - assert (H0 : 0 <= inject_Z (Z.of_nat k) * ((t - 0) / d))
      by (apply Qmult_le_0_compat; assumption).
    lra.
  - assert (H1 : inject_Z (Z.of_nat k) * ((t - 0) / d) <= d * ((t - 0) / d))
      by (apply Qmult_le_compat_r; assumption).
    assert (H2 : d * ((t - 0) / d) == t) by (field; lra).
    lra.
Qed.

(** The contraction of the Picard operator on functions Q -> Q. *)
Theorem picard_step_contraction :
  forall (f : VectorField) (L y0 : Q) (y z : Q -> Q) (D t : Q) (N : nat),
  is_lipschitz f L -> 0 <= t -> 0 <= D ->
  (forall s, 0 <= s -> s <= t -> Qabs (y s - z s) <= D) ->
  Qabs (picard_step f y0 y t N - picard_step f y0 z t N) <= (L * t) * D.
Proof.
  intros f L y0 y z D t N [HL Hlip] Ht HD Hyz.
  unfold picard_step, integral_process.
  pose proof (riemann_sum_sub (fun s => f s (y s)) (fun s => f s (z s))
                0 (integral_step 0 t N) (S N)) as HS.
  cbv beta in HS.
  assert (E : y0 + riemann_sum (fun s => f s (y s)) 0 (integral_step 0 t N) (S N)
              - (y0 + riemann_sum (fun s => f s (z s)) 0 (integral_step 0 t N) (S N))
              == riemann_sum (fun s => f s (y s) - f s (z s)) 0 (integral_step 0 t N) (S N)).
  { rewrite HS. ring. }
  rewrite E.
  pose proof (inject_Z_Sn_pos N) as Hd.
  assert (Hst : 0 <= integral_step 0 t N).
  { unfold integral_step. apply Qle_shift_div_l; [ exact Hd | lra ]. }
  eapply Qle_trans.
  - apply (riemann_sum_abs_bound (fun s => f s (y s) - f s (z s))
             0 (integral_step 0 t N) (S N) (L * D)).
    + intros k Hk. cbv beta.
      destruct (walk_point_0_range t N k Ht) as [H0 H1]; [ lia | ].
      eapply Qle_trans; [ apply Hlip | ].
      apply FixedPoint.Qmult_le_compat_l; [ apply Hyz; assumption | lra ].
    + exact Hst.
    + apply Qmult_le_0_compat; lra.
  - unfold integral_step.
    set (d := inject_Z (Z.of_nat (S N))) in *.
    assert (Eq : L * D * d * ((t - 0) / d) == L * t * D) by (field; lra).
    rewrite Eq. apply Qle_refl.
Qed.

(** The geometric gap of the Picard iterates on functions Q -> Q, on [0, T]. *)
Theorem picard_iterate_gap :
  forall (f : VectorField) (L y0 T C : Q) (N n : nat),
  is_lipschitz f L -> 0 <= T -> 0 <= C ->
  (forall t, 0 <= t -> t <= T ->
     Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= C) ->
  forall t, 0 <= t -> t <= T ->
    Qabs (picard_iterate f y0 (S n) t N - picard_iterate f y0 n t N)
      <= Qpow (L * T) n * C.
Proof.
  intros f L y0 T C N n Hlip HT HC H1.
  assert (HL : 0 < L) by (destruct Hlip; assumption).
  assert (HLT : 0 <= L * T) by (apply Qmult_le_0_compat; lra).
  induction n as [|n IH]; intros t Ht0 HtT.
  - cbn [Qpow]. rewrite Qmult_1_l. apply H1; assumption.
  - change (picard_iterate f y0 (S (S n)) t N)
      with (picard_step f y0 (fun s => picard_iterate f y0 (S n) s N) t N).
    change (picard_iterate f y0 (S n) t N)
      with (picard_step f y0 (fun s => picard_iterate f y0 n s N) t N).
    assert (HD : 0 <= Qpow (L * T) n * C)
      by (apply Qmult_le_0_compat; [ apply SeriesConvergence.Qpow_nonneg; exact HLT | exact HC ]).
    eapply Qle_trans.
    + apply (picard_step_contraction f L y0 _ _ (Qpow (L * T) n * C) t N Hlip Ht0 HD).
      intros s Hs0 Hst. cbv beta. apply IH; [ exact Hs0 | lra ].
    + cbn [Qpow].
      assert (HLt : L * t <= L * T) by (apply FixedPoint.Qmult_le_compat_l; lra).
      assert (Hm : (L * t) * (Qpow (L * T) n * C) <= (L * T) * (Qpow (L * T) n * C))
        by (apply Qmult_le_compat_r; assumption).
      setoid_replace (L * T * Qpow (L * T) n * C)
        with ((L * T) * (Qpow (L * T) n * C)) by ring.
      exact Hm.
Qed.

(** The Picard iterates form a Cauchy process uniformly on [0, T] for
    L T < 1 (at every stage N of the integral process). *)
Theorem picard_iterate_uniformly_cauchy :
  forall (f : VectorField) (L y0 T C : Q) (N : nat),
  is_lipschitz f L -> 0 <= T -> L * T < 1 -> 0 <= C ->
  (forall t, 0 <= t -> t <= T ->
     Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= C) ->
  forall eps, 0 < eps ->
  exists K : nat, forall m n, (K <= m)%nat -> (K <= n)%nat ->
    forall t, 0 <= t -> t <= T ->
      Qabs (picard_iterate f y0 m t N - picard_iterate f y0 n t N) < eps.
Proof.
  intros f L y0 T C N Hlip HT Hrate HC H1 eps Heps.
  assert (HL : 0 < L) by (destruct Hlip; assumption).
  assert (HLT : 0 <= L * T) by (apply Qmult_le_0_compat; lra).
  destruct (geom_gap_modulus (L * T) C eps HLT Hrate HC Heps) as [K HK].
  exists K. intros m n Hm Hn t Ht0 HtT.
  apply (HK (fun i => picard_iterate f y0 i t N)); [ | exact Hm | exact Hn ].
  intro i. apply (picard_iterate_gap f L y0 T C N i Hlip HT HC H1 t Ht0 HtT).
Qed.

(** The first gap is bounded when f(s, y0) is bounded on [0, T]. *)
Lemma picard_first_gap_bound : forall (f : VectorField) (y0 T M0 : Q) (N : nat),
  0 <= T -> 0 <= M0 ->
  (forall s, 0 <= s -> s <= T -> Qabs (f s y0) <= M0) ->
  forall t, 0 <= t -> t <= T ->
    Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= M0 * T.
Proof.
  intros f y0 T M0 N HT HM0 Hb t Ht0 HtT.
  change (picard_iterate f y0 1 t N)
    with (y0 + integral_process (fun s => f s y0) 0 t N).
  change (picard_iterate f y0 0 t N) with y0.
  setoid_replace (y0 + integral_process (fun s => f s y0) 0 t N - y0)
    with (integral_process (fun s => f s y0) 0 t N) by ring.
  unfold integral_process.
  pose proof (inject_Z_Sn_pos N) as Hd.
  assert (Hst : 0 <= integral_step 0 t N).
  { unfold integral_step. apply Qle_shift_div_l; [ exact Hd | lra ]. }
  eapply Qle_trans.
  - apply (riemann_sum_abs_bound (fun s => f s y0) 0 (integral_step 0 t N) (S N) M0).
    + intros k Hk. cbv beta.
      destruct (walk_point_0_range t N k Ht0) as [H0 H1]; [ lia | ].
      apply Hb; [ exact H0 | lra ].
    + exact Hst.
    + exact HM0.
  - unfold integral_step.
    set (d := inject_Z (Z.of_nat (S N))) in *.
    assert (Eq : M0 * d * ((t - 0) / d) == M0 * t) by (field; lra).
    rewrite Eq. apply FixedPoint.Qmult_le_compat_l; assumption.
Qed.

(** On [0, T] with L T < 1 and |f(s, y0)| <= M0 the number from which the
    iterates are eps-close is ONE for all stages of the integral process:
    it is chosen before N. *)
Theorem picard_iterate_modulus_stage_free :
  forall (f : VectorField) (L y0 T M0 : Q),
  is_lipschitz f L -> 0 <= T -> L * T < 1 -> 0 <= M0 ->
  (forall s, 0 <= s -> s <= T -> Qabs (f s y0) <= M0) ->
  forall eps, 0 < eps ->
  exists K : nat, forall (N m n : nat), (K <= m)%nat -> (K <= n)%nat ->
    forall t, 0 <= t -> t <= T ->
      Qabs (picard_iterate f y0 m t N - picard_iterate f y0 n t N) < eps.
Proof.
  intros f L y0 T M0 Hlip HT Hrate HM0 Hb eps Heps.
  assert (HL : 0 < L) by (destruct Hlip; assumption).
  assert (HLT : 0 <= L * T) by (apply Qmult_le_0_compat; lra).
  assert (HC : 0 <= M0 * T) by (apply Qmult_le_0_compat; assumption).
  destruct (geom_gap_modulus (L * T) (M0 * T) eps HLT Hrate HC Heps) as [K HK].
  exists K. intros N m n Hm Hn t Ht0 HtT.
  apply (HK (fun i => picard_iterate f y0 i t N)); [ | exact Hm | exact Hn ].
  intro i.
  apply (picard_iterate_gap f L y0 T (M0 * T) N i Hlip HT HC); [ | exact Ht0 | exact HtT ].
  intros t' Ht'0 Ht'T.
  apply (picard_first_gap_bound f y0 T M0 N HT HM0 Hb t' Ht'0 Ht'T).
Qed.

(** The premises are satisfiable: f(t, y) = y, y0 = 1, the segment
    [0, 1/2], every stage N -- with one number for all stages. *)
Example picard_iterate_linear_uniformly_cauchy : forall eps : Q, 0 < eps ->
  exists K : nat, forall (N m n : nat), (K <= m)%nat -> (K <= n)%nat ->
    forall t, 0 <= t -> t <= 1#2 ->
      Qabs (picard_iterate (fun _ y : Q => y) 1 m t N
            - picard_iterate (fun _ y : Q => y) 1 n t N) < eps.
Proof.
  intros eps Heps.
  assert (Hlip : is_lipschitz (fun _ y : Q => y) 1)
    by (split; [ lra | intros t y1 y2; lra ]).
  assert (HT : 0 <= 1#2) by (rewrite Qle_alt; discriminate).
  assert (Hrate : 1 * (1#2) < 1) by (rewrite Qlt_alt; reflexivity).
  apply (picard_iterate_modulus_stage_free (fun _ y : Q => y) 1 1 (1#2) 1
           Hlip HT Hrate).
  - lra.
  - intros s _ _. cbv beta. change (Qabs 1) with 1. apply Qle_refl.
  - exact Heps.
Qed.
