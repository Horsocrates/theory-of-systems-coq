(** * ProcessGronwallInequality.v -- The discrete Gronwall inequality for an arbitrary sequence, stability as its instance, and the mesh-free divergence bound, as a ToS System

    Elements: rational sequences u_n subject to a recurrent estimate; the
              comparison iteration [gronwall_iterate] (ProcessGronwall.v);
              the divergences |Delta_n| of two Euler polygons
              (ProcessODEStability.v); the stages [expt_process (L t) k] of
              the growth-factor ladder (ProcessExpProcess.v); fixed points of
              the grid Picard operator (ProcessPicardOperator.v).
    Roles:    1 + alpha h -- role-growth factor of one step; beta h --
              role-inflow; [gronwall_iterate] -- role-majorant (the sequence
              every subordinate sequence is compared with); the stage
              (1 + L t/n)^n -- role-growth of the divergence up to the moment
              t; the number (1 - L t/(k0+1))^(-(k0+1)) -- role-ceiling, one
              for all meshes; the initial perturbation |y0 - z0| -- role-cause.
    Rules:    comparison by induction (a nonnegative factor preserves the
              order); the one-step divergence estimate [euler_step_diff];
              the substitution h = t/(k+1); monotonicity and boundedness of
              the growth-factor ladder (ProcessExpLadder.v).

    Proved (no axioms):
      - [gronwall_inequality_from], [gronwall_inequality],
        [gronwall_inequality_hom], [gronwall_inequality_forced]: every
        sequence that grows no faster than the Gronwall step is bounded by
        the Gronwall iteration (for a nonnegative factor 1 + alpha h; the
        condition is essential -- [gronwall_inequality_needs_nonneg_factor]);
      - [gronwall_iterate_closed], [gronwall_iterate_alpha_zero]: the
        iteration with inflow in closed form (an equality);
      - [qpow_is_Qpow], [euler_bound_is_gronwall_iterate],
        [euler_divergence_gronwall]: the divergence estimate of two Euler
        polygons IS the Gronwall inequality applied to |Delta_n|; the bound
        is attained for f(t, y) = L y ([euler_diff_bound_sharp]);
      - [euler_same_start], [euler_is_picard_fixed],
        [picard_fixed_stability], [picard_unique_as_zero_perturbation]:
        uniqueness of the fixed point of the grid Picard operator as
        stability under zero perturbation;
      - [euler_continuous_dependence]: eps-delta dependence on the initial
        value at a given step;
      - [euler_divergence_expt]: with the step t/(k+1) the divergence at the
        moment t is bounded by the stage k of the ladder (1 + L t/n)^n;
        [euler_divergence_uniform], [euler_divergence_expt_small],
        [euler_stability_uniform]: bounds that do not depend on the number
        of steps; [euler_continuous_dependence_uniform]: one delta for all
        meshes of the interval [0, t];
      - [growth_factor_is_Cauchy]: the ladder of growth factors is a Cauchy
        process;
      - [gronwall_iterate_decay], [gronwall_iterate_decay_monotone]
        (factor in [0, 1], u0 >= 0; the condition u0 >= 0 is essential --
        [decay_factor_needs_u0_nonneg]); [gronwall_iterate_abs],
        [gronwall_iterate_abs_decay], [gronwall_iterate_abs_monotone],
        [gronwall_iterate_vanishes]: decay of the absolute value for every
        u0 when |1 + alpha h| <= 1, and vanishing when |1 + alpha h| < 1.

    P4 diagnostic: all statements are about finite rational stages: a
      sequence, a number of steps, a mesh. The moment t enters as a rational
      parameter; the ceiling of the growth factor is a rational number. The
      exponential e^{L t} does not occur: its place is taken by the ladder
      of stages and the ceiling.

    NOT claimed:
      - the number e^{L t} as a completed object, or that the ceiling equals
        it;
      - an estimate on an unbounded time interval;
      - the divergence of two Euler polygons with different steps (that is
        ProcessEulerRefinement.v), or of two solutions of the Cauchy problem;
      - the Gronwall inequality in the integral (continuous) form.

    STATUS: 37 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessMCT.   (* q_sum *)
From ToS Require Import process.ProcessExpProcess.
From ToS Require Import process.ProcessExpLadder.
From ToS Require Import process.ProcessGronwall.
From ToS Require Import process.ProcessODEStability.
From ToS Require Import process.ProcessPicardOperator.
From ToS Require process.ProcessPicardGridSolution.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The Gronwall inequality for an arbitrary sequence                  *)
(* ===================================================================== *)

(** Every sequence that grows no faster than the Gronwall step is bounded by
    the iteration of that step started above it. *)
Theorem gronwall_inequality_from : forall (alpha beta h : Q) (u : nat -> Q) (u0 : Q),
  0 <= 1 + alpha * h ->
  u 0%nat <= u0 ->
  (forall n, u (S n) <= (1 + alpha * h) * u n + beta * h) ->
  forall n, u n <= gronwall_iterate alpha beta h u0 n.
Proof.
  intros alpha beta h u u0 Hf H0 Hrec n. induction n as [|n IH].
  - cbn [gronwall_iterate]. exact H0.
  - cbn [gronwall_iterate]. unfold gronwall_step.
    eapply Qle_trans; [ apply Hrec | ].
    apply Qplus_le_compat; [ | apply Qle_refl ].
    apply ProcessExpLadder.qmul_le_l; assumption.
Qed.

Corollary gronwall_inequality : forall (alpha beta h : Q) (u : nat -> Q),
  0 <= 1 + alpha * h ->
  (forall n, u (S n) <= (1 + alpha * h) * u n + beta * h) ->
  forall n, u n <= gronwall_iterate alpha beta h (u 0%nat) n.
Proof.
  intros alpha beta h u Hf Hrec n.
  apply gronwall_inequality_from; [ exact Hf | apply Qle_refl | exact Hrec ].
Qed.

(** The homogeneous case: growth by at most the factor 1 + alpha h per step
    implies the geometric bound. *)
Corollary gronwall_inequality_hom : forall (alpha h : Q) (u : nat -> Q),
  0 <= 1 + alpha * h ->
  (forall n, u (S n) <= (1 + alpha * h) * u n) ->
  forall n, u n <= u 0%nat * Qpow (1 + alpha * h) n.
Proof.
  intros alpha h u Hf Hrec n.
  rewrite <- gronwall_beta_zero.
  apply gronwall_inequality; [ exact Hf | ].
  intro k. eapply Qle_trans; [ apply Hrec | ].
  assert (E : (1 + alpha * h) * u k + 0 * h == (1 + alpha * h) * u k) by ring.
  rewrite E. apply Qle_refl.
Qed.

(** The iteration with inflow in closed form: the "bound" of
    ProcessGronwall.discrete_gronwall is an equality (for alpha <> 0; the
    conditions 0 <= beta and 0 < h are not needed). *)
Lemma gronwall_iterate_closed : forall alpha beta h u0 n,
  ~ alpha == 0 ->
  gronwall_iterate alpha beta h u0 n == gronwall_bound alpha beta h u0 n.
Proof.
  intros alpha beta h u0 n Ha. unfold gronwall_bound. induction n as [|n IH].
  - cbn [gronwall_iterate Qpow]. field. exact Ha.
  - cbn [gronwall_iterate Qpow]. unfold gronwall_step. rewrite IH. field. exact Ha.
Qed.

(** Without self-action (alpha = 0) the inflow accumulates linearly. *)
Lemma gronwall_iterate_alpha_zero : forall beta h u0 n,
  gronwall_iterate 0 beta h u0 n == u0 + inject_Z (Z.of_nat n) * (beta * h).
Proof.
  intros beta h u0 n. induction n as [|n IH].
  - cbn [gronwall_iterate]. change (inject_Z (Z.of_nat 0)) with 0. ring.
  - cbn [gronwall_iterate]. unfold gronwall_step. rewrite IH, inj_S. ring.
Qed.

(** The inequality with inflow: the explicit bound. *)
Corollary gronwall_inequality_forced : forall (alpha beta h : Q) (u : nat -> Q),
  0 < alpha -> 0 <= h ->
  (forall n, u (S n) <= (1 + alpha * h) * u n + beta * h) ->
  forall n, u n <= (u 0%nat + beta / alpha) * Qpow (1 + alpha * h) n - beta / alpha.
Proof.
  intros alpha beta h u Ha Hh Hrec n.
  assert (Hf : 0 <= 1 + alpha * h).
  { assert (0 <= alpha * h) by (apply Qmult_le_0_compat; lra). lra. }
  pose proof (gronwall_inequality alpha beta h u Hf Hrec n) as Hg.
  assert (Hne : ~ alpha == 0) by (intro Hc; rewrite Hc in Ha; apply (Qlt_irrefl 0); exact Ha).
  rewrite (gronwall_iterate_closed alpha beta h (u 0%nat) n Hne) in Hg.
  exact Hg.
Qed.

(** The condition 0 <= 1 + alpha h is essential: with a negative factor a
    sequence subordinate to the step can exceed the iteration. *)
Definition gronwall_cex (n : nat) : Q :=
  match n with
  | O => 0
  | S O => -1
  | S (S O) => 1
  | _ => -1
  end.

Lemma gronwall_inequality_needs_nonneg_factor :
  (forall n, gronwall_cex (S n) <= (1 + (-2) * 1) * gronwall_cex n + 0 * 1)
  /\ ~ (gronwall_cex 2%nat <= gronwall_iterate (-2) 0 1 (gronwall_cex 0%nat) 2).
Proof.
  split.
  - intro n. destruct n as [|[|[|n]]]; cbn [gronwall_cex]; unfold Qle; simpl; lia.
  - cbn [gronwall_cex gronwall_iterate]. unfold gronwall_step. unfold Qle. simpl. lia.
Qed.

(* ===================================================================== *)
(*  2. Stability is the Gronwall inequality for the divergence            *)
(* ===================================================================== *)

(** The two power functions (qpow of ProcessExpProcess.v and Qpow of
    SeriesConvergence.v) coincide. *)
Lemma qpow_is_Qpow : forall b n, qpow b n = Qpow b n.
Proof.
  intros b n. induction n as [|n IH]; cbn [qpow Qpow];
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** The right-hand side of euler_diff_bound is the homogeneous Gronwall
    iteration. *)
Lemma euler_bound_is_gronwall_iterate : forall L h d n,
  qpow (1 + L * h) n * d == gronwall_iterate L 0 h d n.
Proof.
  intros L h d n. rewrite gronwall_beta_zero, qpow_is_Qpow. ring.
Qed.

Lemma qpow_ge_one : forall b n, 1 <= b -> 1 <= qpow b n.
Proof.
  intros b n Hb. induction n as [|n IH]; cbn [qpow]; [ lra | ].
  apply Qle_trans with (b * 1); [ lra | ].
  apply ProcessExpLadder.qmul_le_l; [ lra | exact IH ].
Qed.

Section StabilityIsGronwall.

Variable f : Q -> Q -> Q.
Variable L : Q.
Hypothesis HL : 0 <= L.
Hypothesis Hlip : forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2).
Variable h : Q.
Hypothesis Hh : 0 <= h.

Lemma one_plus_Lh_nonneg : 0 <= 1 + L * h.
Proof. assert (0 <= L * h) by (apply Qmult_le_0_compat; assumption). lra. Qed.

Lemma one_le_one_plus_Lh : 1 <= 1 + L * h.
Proof. assert (0 <= L * h) by (apply Qmult_le_0_compat; assumption). lra. Qed.

(** Stability is Gronwall for the divergence: the estimate is obtained by
    applying the inequality of section 1 to the sequence |Delta_n|. *)
Theorem euler_divergence_gronwall : forall y0 z0 n,
  Qabs (euler f h y0 n - euler f h z0 n)
  <= gronwall_iterate L 0 h (Qabs (y0 - z0)) n.
Proof.
  intros y0 z0 n.
  apply (gronwall_inequality_from L 0 h
           (fun k => Qabs (euler f h y0 k - euler f h z0 k)) (Qabs (y0 - z0))).
  - exact one_plus_Lh_nonneg.
  - cbn [euler]. apply Qle_refl.
  - intro k. eapply Qle_trans; [ apply (euler_step_diff f L Hlip h Hh) | ].
    assert (E : (1 + L * h) * Qabs (euler f h y0 k - euler f h z0 k) + 0 * h
                == (1 + L * h) * Qabs (euler f h y0 k - euler f h z0 k)) by ring.
    rewrite E. apply Qle_refl.
Qed.

(** The same in the form of the page: |Delta_n| <= |Delta_0| (1 + L h)^n. *)
Corollary euler_divergence_gronwall_Qpow : forall y0 z0 n,
  Qabs (euler f h y0 n - euler f h z0 n) <= Qabs (y0 - z0) * Qpow (1 + L * h) n.
Proof.
  intros y0 z0 n. rewrite <- gronwall_beta_zero. apply euler_divergence_gronwall.
Qed.

(* ===================================================================== *)
(*  3. Uniqueness as zero perturbation                                    *)
(* ===================================================================== *)

(** Zero perturbation gives zero divergence: equal starts give equal Euler
    polygons. *)
Corollary euler_same_start : forall y0 z0 n,
  y0 == z0 -> euler f h y0 n == euler f h z0 n.
Proof.
  intros y0 z0 n E.
  pose proof (euler_diff_bound f L HL Hlip h Hh y0 z0 n) as Hb.
  assert (Hz : Qabs (y0 - z0) == 0).
  { assert (Ez : y0 - z0 == 0) by lra. rewrite Ez. reflexivity. }
  rewrite Hz in Hb.
  assert (H0 : qpow (1 + L * h) n * 0 == 0) by ring. rewrite H0 in Hb.
  apply Qabs_Qle_condition in Hb. lra.
Qed.

(** One step of the grid Picard operator. *)
Lemma picard_op_succ : forall y0 (y : nat -> Q) k,
  picard_op f h y0 y (S k) == picard_op f h y0 y k + h * f (tgrid h k) (y k).
Proof. intros y0 y k. unfold picard_op, picard_sum. cbn [q_sum]. ring. Qed.

(** The Euler polygon is a fixed point of the grid Picard operator -- for
    every step and every grid (no Lipschitz condition is used). *)
Theorem euler_is_picard_fixed : forall y0 k,
  picard_op f h y0 (euler f h y0) k == euler f h y0 k.
Proof.
  intros y0 k. induction k as [|k IH].
  - unfold picard_op, picard_sum. cbn [q_sum euler]. ring.
  - rewrite picard_op_succ, IH. cbn [euler]. reflexivity.
Qed.

(** Two fixed points of the grid Picard operator with starts y0, z0 diverge
    by at most the factor (1 + L h)^k of |y0 - z0|. *)
Theorem picard_fixed_stability : forall y0 z0 N (y z : nat -> Q),
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  (forall k, (k <= N)%nat -> picard_op f h z0 z k == z k) ->
  forall k, (k <= N)%nat ->
    Qabs (y k - z k) <= qpow (1 + L * h) k * Qabs (y0 - z0).
Proof.
  intros y0 z0 N y z Hy Hz k Hk.
  pose proof (ProcessPicardGridSolution.lipschitz_compat f L Hlip) as Hc.
  rewrite (ProcessPicardGridSolution.picard_fixed_eq_euler f h y0 N Hc y Hy k Hk).
  rewrite (ProcessPicardGridSolution.picard_fixed_eq_euler f h z0 N Hc z Hz k Hk).
  apply (euler_diff_bound f L HL Hlip h Hh).
Qed.

(** Uniqueness is the limiting case of stability: with equal starts the
    fixed points coincide. *)
Corollary picard_unique_as_zero_perturbation : forall y0 z0 N (y z : nat -> Q),
  y0 == z0 ->
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  (forall k, (k <= N)%nat -> picard_op f h z0 z k == z k) ->
  forall k, (k <= N)%nat -> y k == z k.
Proof.
  intros y0 z0 N y z E Hy Hz k Hk.
  pose proof (picard_fixed_stability y0 z0 N y z Hy Hz k Hk) as Hb.
  assert (Hz0 : Qabs (y0 - z0) == 0).
  { assert (Ez : y0 - z0 == 0) by lra. rewrite Ez. reflexivity. }
  rewrite Hz0 in Hb.
  assert (H0 : qpow (1 + L * h) k * 0 == 0) by ring. rewrite H0 in Hb.
  apply Qabs_Qle_condition in Hb. lra.
Qed.

(* ===================================================================== *)
(*  4. Continuous dependence at a given step                              *)
(* ===================================================================== *)

(** A small initial divergence gives a small divergence at the n-th step. *)
Theorem euler_continuous_dependence : forall n eps, 0 < eps ->
  exists delta, 0 < delta /\
    forall y0 z0, Qabs (y0 - z0) < delta ->
      Qabs (euler f h y0 n - euler f h z0 n) < eps.
Proof.
  intros n eps Heps.
  pose proof (qpow_ge_one (1 + L * h) n one_le_one_plus_Lh) as HM.
  set (M := qpow (1 + L * h) n) in *.
  exists (eps / M). split.
  - apply Qlt_shift_div_l; [ lra | ].
    assert (E : 0 * M == 0) by ring. rewrite E. exact Heps.
  - intros y0 z0 Hd.
    eapply Qle_lt_trans; [ apply (euler_diff_bound f L HL Hlip h Hh) | ].
    fold M.
    assert (H1 : M * Qabs (y0 - z0) < M * (eps / M)).
    { apply Qmult_lt_l; [ lra | exact Hd ]. }
    assert (H2 : M * (eps / M) == eps) by (field; lra).
    rewrite H2 in H1. exact H1.
Qed.

End StabilityIsGronwall.

(** The premises of the section are satisfiable and the estimate is sharp:
    for f(t, y) = L y the divergence equals (1 + L h)^n |y0 - z0|. *)
Lemma euler_linear_closed : forall L h y0 n,
  euler (fun _ y => L * y) h y0 n == y0 * qpow (1 + L * h) n.
Proof.
  intros L h y0 n. induction n as [|n IH].
  - cbn [euler qpow]. ring.
  - cbn [euler qpow]. rewrite IH. ring.
Qed.

Lemma linear_is_lipschitz : forall L, 0 <= L ->
  forall (t y1 y2 : Q), Qabs ((fun (_ : Q) y => L * y) t y1 - (fun (_ : Q) y => L * y) t y2)
                        <= L * Qabs (y1 - y2).
Proof.
  intros L HL t y1 y2. cbv beta.
  assert (E : L * y1 - L * y2 == L * (y1 - y2)) by ring.
  rewrite E, Qabs_Qmult, (Qabs_pos L HL). apply Qle_refl.
Qed.

Theorem euler_diff_bound_sharp : forall L h y0 z0 n, 0 <= L -> 0 <= h ->
  Qabs (euler (fun _ y => L * y) h y0 n - euler (fun _ y => L * y) h z0 n)
  == qpow (1 + L * h) n * Qabs (y0 - z0).
Proof.
  intros L h y0 z0 n HL Hh.
  rewrite !euler_linear_closed.
  assert (E : y0 * qpow (1 + L * h) n - z0 * qpow (1 + L * h) n
              == qpow (1 + L * h) n * (y0 - z0)) by ring.
  rewrite E, Qabs_Qmult.
  assert (Hp : 0 <= qpow (1 + L * h) n).
  { apply qpow_nonneg_base. assert (0 <= L * h) by (apply Qmult_le_0_compat; assumption). lra. }
  rewrite (Qabs_pos _ Hp). reflexivity.
Qed.

(* ===================================================================== *)
(*  5. The growth factor at the moment t: bounds free of the mesh          *)
(* ===================================================================== *)

(** The bridge: with the step t/(k+1) the divergence after k+1 steps (at the
    moment t) is bounded by the stage k of the ladder (1 + L t/n)^n times
    the initial perturbation. *)
Theorem euler_divergence_expt :
  forall (f : Q -> Q -> Q) (L : Q), 0 <= L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall t, 0 <= t ->
  forall (k : nat) (y0 z0 : Q),
    Qabs (euler f (t / inject_Z (Z.of_nat (S k))) y0 (S k)
          - euler f (t / inject_Z (Z.of_nat (S k))) z0 (S k))
    <= expt_process (L * t) k * Qabs (y0 - z0).
Proof.
  intros f L HL Hlip t Ht k y0 z0.
  pose proof (exp1_pos_denom k) as Hd.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (Hh : 0 <= t / d).
  { apply Qle_shift_div_l; [ exact Hd | ].
    assert (E : 0 * d == 0) by ring. rewrite E. exact Ht. }
  eapply Qle_trans; [ apply (euler_diff_bound f L HL Hlip (t / d) Hh) | ].
  unfold expt_process. fold d.
  assert (E : 1 + L * (t / d) == 1 + L * t / d) by (field; lra).
  rewrite (qpow_wd _ _ (S k) E). apply Qle_refl.
Qed.

(** The divergence at the moment t is bounded independently of the number of
    steps: if L t < k0 + 1, then for every number of steps k + 1
    |Delta| <= (1 - L t/(k0+1))^(-(k0+1)) |Delta_0|. *)
Corollary euler_divergence_uniform :
  forall (f : Q -> Q -> Q) (L : Q), 0 <= L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall t, 0 <= t ->
  forall k0 : nat, L * t < inject_Z (Z.of_nat (S k0)) ->
  forall (k : nat) (y0 z0 : Q),
    Qabs (euler f (t / inject_Z (Z.of_nat (S k))) y0 (S k)
          - euler f (t / inject_Z (Z.of_nat (S k))) z0 (S k))
    <= 1 / qpow (1 - L * t / inject_Z (Z.of_nat (S k0))) (S k0) * Qabs (y0 - z0).
Proof.
  intros f L HL Hlip t Ht k0 Hk0 k y0 z0.
  eapply Qle_trans; [ apply (euler_divergence_expt f L HL Hlip t Ht) | ].
  apply Qmult_le_compat_r; [ | apply Qabs_nonneg ].
  apply expt_bounded; [ apply Qmult_le_0_compat; assumption | exact Hk0 ].
Qed.

(** The short interval L t < 1: for every number of steps the divergence at
    the moment t is at most |Delta_0| / (1 - L t). *)
Corollary euler_divergence_expt_small :
  forall (f : Q -> Q -> Q) (L : Q), 0 <= L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall t, 0 <= t -> L * t < 1 ->
  forall (k : nat) (y0 z0 : Q),
    Qabs (euler f (t / inject_Z (Z.of_nat (S k))) y0 (S k)
          - euler f (t / inject_Z (Z.of_nat (S k))) z0 (S k))
    <= Qabs (y0 - z0) / (1 - L * t).
Proof.
  intros f L HL Hlip t Ht Hlt k y0 z0.
  eapply Qle_trans; [ apply (euler_divergence_expt f L HL Hlip t Ht) | ].
  assert (Hs : 0 <= L * t) by (apply Qmult_le_0_compat; assumption).
  pose proof (expt_upper (L * t) k Hs Hlt) as Hu.
  assert (Hd : 0 <= Qabs (y0 - z0)) by apply Qabs_nonneg.
  apply Qle_trans with (1 / (1 - L * t) * Qabs (y0 - z0)).
  - apply Qmult_le_compat_r; assumption.
  - assert (E : 1 / (1 - L * t) * Qabs (y0 - z0) == Qabs (y0 - z0) / (1 - L * t))
      by (field; lra).
    rewrite E. apply Qle_refl.
Qed.

(** The same for an arbitrary step: on a segment of n steps with
    n (L h) <= s < 1 the divergence is at most |Delta_0| / (1 - s). *)
Theorem euler_stability_uniform :
  forall (f : Q -> Q -> Q) (L : Q), 0 <= L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h ->
  forall n s y0 z0,
    inject_Z (Z.of_nat n) * (L * h) <= s -> s < 1 ->
    Qabs (euler f h y0 n - euler f h z0 n) <= Qabs (y0 - z0) / (1 - s).
Proof.
  intros f L HL Hlip h Hh n s y0 z0 Hs Hs1.
  eapply Qle_trans; [ apply (euler_diff_bound f L HL Hlip h Hh) | ].
  assert (Hx : 0 <= L * h) by (apply Qmult_le_0_compat; assumption).
  pose proof (qpow_uniform_bound (L * h) n s Hx Hs Hs1) as Hu.
  assert (Hd : 0 <= Qabs (y0 - z0)) by apply Qabs_nonneg.
  apply Qle_trans with (1 / (1 - s) * Qabs (y0 - z0)).
  - apply Qmult_le_compat_r; assumption.
  - assert (E : 1 / (1 - s) * Qabs (y0 - z0) == Qabs (y0 - z0) / (1 - s)) by (field; lra).
    rewrite E. apply Qle_refl.
Qed.

(** Continuous dependence on the interval [0, t], uniformly in the mesh: one
    delta serves every number of steps. *)
Theorem euler_continuous_dependence_uniform :
  forall (f : Q -> Q -> Q) (L : Q), 0 <= L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall t, 0 <= t -> forall eps, 0 < eps ->
  exists delta, 0 < delta /\
    forall (k : nat) (y0 z0 : Q), Qabs (y0 - z0) < delta ->
      Qabs (euler f (t / inject_Z (Z.of_nat (S k))) y0 (S k)
            - euler f (t / inject_Z (Z.of_nat (S k))) z0 (S k)) < eps.
Proof.
  intros f L HL Hlip t Ht eps Heps.
  assert (H01 : 0 < 1) by lra.
  destruct (ladder_archimedean (L * t) 1 H01) as [K0 HK0].
  assert (Hk0 : L * t < inject_Z (Z.of_nat (S K0))) by (rewrite inj_S; lra).
  pose proof (exp1_pos_denom K0) as Hd0.
  assert (Hbase : 0 < 1 - L * t / inject_Z (Z.of_nat (S K0))).
  { assert (Hq : L * t / inject_Z (Z.of_nat (S K0)) < 1)
      by (apply Qlt_shift_div_r; [ exact Hd0 | lra ]).
    set (q := L * t / inject_Z (Z.of_nat (S K0))) in *. lra. }
  pose proof (qpow_pos _ (S K0) Hbase) as HP.
  exists (eps * qpow (1 - L * t / inject_Z (Z.of_nat (S K0))) (S K0)). split.
  - apply Qmult_lt_0_compat; assumption.
  - intros k y0 z0 Hd.
    eapply Qle_lt_trans;
      [ apply (euler_divergence_uniform f L HL Hlip t Ht K0 Hk0 k y0 z0) | ].
    set (P := qpow (1 - L * t / inject_Z (Z.of_nat (S K0))) (S K0)) in *.
    assert (HiP : 0 < 1 / P).
    { apply Qlt_shift_div_l; [ exact HP | ].
      assert (E : 0 * P == 0) by ring. rewrite E. exact H01. }
    assert (H1 : 1 / P * Qabs (y0 - z0) < 1 / P * (eps * P)).
    { apply Qmult_lt_l; [ exact HiP | exact Hd ]. }
    assert (H2 : 1 / P * (eps * P) == eps) by (field; lra).
    rewrite H2 in H1. exact H1.
Qed.

(** The ladder of growth factors (1 + L t/n)^n is a Cauchy process. *)
Corollary growth_factor_is_Cauchy : forall L t, 0 <= L -> 0 <= t ->
  is_Cauchy (expt_process (L * t)).
Proof.
  intros L t HL Ht. apply expt_process_is_Cauchy. apply Qmult_le_0_compat; assumption.
Qed.

(* ===================================================================== *)
(*  6. Decay                                                              *)
(* ===================================================================== *)

(** Without the condition 0 <= u0 the decay formula is false. *)
Lemma decay_factor_needs_u0_nonneg :
  ~ (forall r u0 n, 0 <= r -> r <= 1 -> u0 * Qpow r n <= u0).
Proof.
  intro H. specialize (H (1 # 2) (-1) 1%nat).
  assert (H1 : 0 <= 1 # 2) by (unfold Qle; simpl; lia).
  assert (H2 : (1 # 2) <= 1) by (unfold Qle; simpl; lia).
  specialize (H H1 H2). revert H. cbn [Qpow]. unfold Qle. simpl. lia.
Qed.

(** Decay of the iteration itself: the factor 1 + alpha h within [0, 1]. *)
Lemma gronwall_iterate_decay : forall alpha h u0 n,
  0 <= 1 + alpha * h -> 1 + alpha * h <= 1 -> 0 <= u0 ->
  gronwall_iterate alpha 0 h u0 n <= u0.
Proof.
  intros alpha h u0 n H0 H1 Hu. rewrite gronwall_beta_zero.
  apply gronwall_decay_factor; assumption.
Qed.

Lemma gronwall_iterate_hom_nonneg : forall alpha h u0 n,
  0 <= 1 + alpha * h -> 0 <= u0 -> 0 <= gronwall_iterate alpha 0 h u0 n.
Proof.
  intros alpha h u0 n H0 Hu. induction n as [|n IH]; cbn [gronwall_iterate].
  - exact Hu.
  - unfold gronwall_step.
    assert (Hm : 0 <= (1 + alpha * h) * gronwall_iterate alpha 0 h u0 n)
      by (apply Qmult_le_0_compat; assumption).
    lra.
Qed.

(** The iteration does not increase from step to step (stronger than
    u_n <= u_0). *)
Lemma gronwall_iterate_decay_monotone : forall alpha h u0 n,
  0 <= 1 + alpha * h -> 1 + alpha * h <= 1 -> 0 <= u0 ->
  gronwall_iterate alpha 0 h u0 (S n) <= gronwall_iterate alpha 0 h u0 n.
Proof.
  intros alpha h u0 n H0 H1 Hu.
  pose proof (gronwall_iterate_hom_nonneg alpha h u0 n H0 Hu) as Hn.
  cbn [gronwall_iterate]. unfold gronwall_step.
  set (I := gronwall_iterate alpha 0 h u0 n) in *.
  assert (Hm : (1 + alpha * h) * I <= 1 * I)
    by (apply Qmult_le_compat_r; assumption).
  lra.
Qed.

(** The absolute value of the homogeneous iteration, for every start. *)
Lemma gronwall_iterate_abs : forall alpha h u0 n,
  Qabs (gronwall_iterate alpha 0 h u0 n) == Qabs u0 * Qpow (Qabs (1 + alpha * h)) n.
Proof.
  intros alpha h u0 n. induction n as [|n IH].
  - cbn [gronwall_iterate Qpow]. ring.
  - cbn [gronwall_iterate Qpow]. unfold gronwall_step.
    assert (E : (1 + alpha * h) * gronwall_iterate alpha 0 h u0 n + 0 * h
                == (1 + alpha * h) * gronwall_iterate alpha 0 h u0 n) by ring.
    rewrite E, Qabs_Qmult, IH. ring.
Qed.

(** Decay of the absolute value: no condition on the sign of the start. *)
Lemma gronwall_iterate_abs_decay : forall alpha h u0 n,
  Qabs (1 + alpha * h) <= 1 ->
  Qabs (gronwall_iterate alpha 0 h u0 n) <= Qabs u0.
Proof.
  intros alpha h u0 n Hr. rewrite gronwall_iterate_abs.
  apply gronwall_decay_factor; [ apply Qabs_nonneg | exact Hr | apply Qabs_nonneg ].
Qed.

Lemma gronwall_iterate_abs_monotone : forall alpha h u0 n,
  Qabs (1 + alpha * h) <= 1 ->
  Qabs (gronwall_iterate alpha 0 h u0 (S n)) <= Qabs (gronwall_iterate alpha 0 h u0 n).
Proof.
  intros alpha h u0 n Hr.
  cbn [gronwall_iterate]. unfold gronwall_step.
  assert (E : (1 + alpha * h) * gronwall_iterate alpha 0 h u0 n + 0 * h
              == (1 + alpha * h) * gronwall_iterate alpha 0 h u0 n) by ring.
  rewrite E, Qabs_Qmult.
  assert (Hm : Qabs (1 + alpha * h) * Qabs (gronwall_iterate alpha 0 h u0 n)
               <= 1 * Qabs (gronwall_iterate alpha 0 h u0 n))
    by (apply Qmult_le_compat_r; [ exact Hr | apply Qabs_nonneg ]).
  assert (E1 : 1 * Qabs (gronwall_iterate alpha 0 h u0 n)
               == Qabs (gronwall_iterate alpha 0 h u0 n)) by ring.
  rewrite E1 in Hm. exact Hm.
Qed.

(** With the factor strictly inside (-1, 1) the iteration vanishes. *)
Theorem gronwall_iterate_vanishes : forall alpha h u0,
  Qabs (1 + alpha * h) < 1 ->
  forall eps, 0 < eps -> exists N : nat, forall n, (N <= n)%nat ->
    Qabs (gronwall_iterate alpha 0 h u0 n) < eps.
Proof.
  intros alpha h u0 Hr eps Heps.
  pose proof (Qabs_nonneg u0) as Ha.
  assert (He : 0 < eps / (Qabs u0 + 1)).
  { apply Qlt_shift_div_l; [ lra | ].
    assert (E : 0 * (Qabs u0 + 1) == 0) by ring. rewrite E. exact Heps. }
  destruct (Qpow_limit_zero (Qabs (1 + alpha * h)) (Qabs_nonneg _) Hr _ He) as [N HN].
  exists N. intros n Hn. rewrite gronwall_iterate_abs.
  pose proof (HN n Hn) as Hp.
  assert (H1 : Qabs u0 * Qpow (Qabs (1 + alpha * h)) n
               <= Qabs u0 * (eps / (Qabs u0 + 1))).
  { apply ProcessExpLadder.qmul_le_l; [ exact Ha | apply Qlt_le_weak; exact Hp ]. }
  assert (E : Qabs u0 * (eps / (Qabs u0 + 1)) + eps / (Qabs u0 + 1) == eps)
    by (field; lra).
  set (e := eps / (Qabs u0 + 1)) in *.
  set (X := Qabs u0 * Qpow (Qabs (1 + alpha * h)) n) in *.
  set (Y := Qabs u0 * e) in *.
  lra.
Qed.
