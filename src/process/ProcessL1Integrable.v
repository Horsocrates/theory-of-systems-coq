(** * ProcessL1Integrable.v -- Step functions as functions of the point; integrable functions on a segment, as a ToS System

    Elements: steps (value, left end, right end) and finite lists of steps
              ([StepIntegral.StepFun]); the value of a list at a rational
              point ([step_eval f x]); stage members [on_seq F n] of a
              process of step functions on a segment [a, b].
    Roles:    [step_eval f]        -- the function of the point written by
                                      the list f (sum of value * indicator);
              [inside a b f]       -- all steps of f lie in [a, b];
              [l1_close a b f g e] -- the difference f - g, as a function of
                                      the point, has a record by a list of
                                      steps in [a, b] with sum |v_i| * w_i
                                      below e (L1-closeness that does not
                                      depend on how f and g are partitioned);
              [L1On a b]           -- an integrable function on [a, b]: a
                                      process of step functions that is
                                      Cauchy in the sense of [l1_close];
              [on_integral F]      -- its integral: the process of the
                                      integrals of the stages;
              [l1_on_equiv F G]    -- "equal almost everywhere" in the L1
                                      sense: the stages become l1_close.
    Rules:    grid rule: the Riemann process of a step function differs from
              its step integral by at most (sum |v_i|) * (grid step);
              the integral depends on the function of the point, not on the
              list that records it; monotonicity and homogeneity for lists;
              |I(h)| <= ||h|| for every list h; L1-closeness is reflexive,
              symmetric and additive in the bound (triangle rule).

    Proved (no axioms):
      - [step_riemann_equiv], [step_riemann_cauchy]: the Riemann process of
        a step function tends to its step integral; [lebesgue_step_agrees]:
        the "Lebesgue process" of the process layer and the L1 integral of
        the embedded step function name the same point;
      - [step_fun_integral_scale], [step_integral_monotone],
        [step_integral_depends_on_function], [step_fun_integral_nonneg];
      - [l1_close_integral]: L1-closeness bounds the difference of integrals;
      - [l1_on_integral_is_Cauchy]: the integral of an integrable function
        is a Cauchy process;
      - [l1_on_equiv_equivalence], [l1_on_equiv_integral]: the relation is an
        equivalence and equivalent functions have the same integral;
      - examples: [shrinking] (a non-stationary process), [shrinking_equiv_zero],
        [one_not_equiv_zero], [point_differs_but_equivalent];
      - [series_l1]: a series of steps with summable norms is an integrable
        function; [staircase]: infinitely many steps accumulating at 0;
        [staircase_beyond_every_stage]: it is equivalent to none of its
        stages;
      - the earlier type [L1Space.L1Process]: on a common partition its
        integral is Cauchy and its relation is an equivalence
        ([l1_integral_cauchy_aligned], [l1_equiv_al_equivalence]); without
        that premise neither holds ([l1_process_integral_unbounded],
        [l1_equiv_not_transitive]).

    P4 diagnostic: an integrable function is a process of finite lists of
      steps; every stage is a finite rational computation. The limit function
      and the completed space are not elements. The closeness of two stages
      is witnessed by a finite list (the record of the difference), so no
      supremum over partitions is taken.

    NOT claimed:
      - that the staircase is equivalent to no step function at all (proved:
        to none of its own stages); a function such as x on [0, 1] is not
        exhibited here;
      - completeness as a theorem about a quotient space (Riesz-Fischer for
        L1): the type holds representatives, the quotient is not built;
      - "functions that differ on a null set are equivalent" in general
        (only the one-point example is proved);
      - linearity of [on_integral] and a norm of an integrable function;
      - anything about the earlier type [L1Space.L1Process] beyond the
        common-partition case.

    STATUS: 83 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs Qminmax List Lqa Lia ZArith.
Import ListNotations.
From ToS Require analysis.StepIntegral analysis.L1Space.
From ToS Require Import MeanValueTheorem RiemannIntegration.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import process.ProcessSimple.
From ToS Require process.ProcessLebesgue.
From ToS Require Import process.ProcessRationalsNull.
From ToS Require Import process.ProcessNullCovers.
From ToS Require Import process.ProcessMeasureIntervals.

Open Scope Q_scope.

Module SI := ToS.analysis.StepIntegral.
Module L1 := ToS.analysis.L1Space.
Module PL := ToS.process.ProcessLebesgue.

(* ===================================================================== *)
(*  1. A step function as a function of the point                         *)
(* ===================================================================== *)

(** The value at x of the function recorded by the list f: every step
    contributes its value on its closed segment. *)
Fixpoint step_eval (f : SI.StepFun) (x : Q) : Q :=
  match f with
  | [] => 0
  | s :: r => SI.step_val s * indicator (SI.step_left s) (SI.step_right s) x
              + step_eval r x
  end.

(** Sum of the absolute values of the steps. *)
Fixpoint total_abs (f : SI.StepFun) : Q :=
  match f with
  | [] => 0
  | s :: r => Qabs (SI.step_val s) + total_abs r
  end.

Lemma total_abs_nonneg : forall f, 0 <= total_abs f.
Proof.
  induction f as [| s r IH]; simpl.
  - apply Qle_refl.
  - pose proof (Qabs_nonneg (SI.step_val s)). lra.
Qed.

(** All steps of f lie in [a, b]. *)
Definition inside (a b : Q) (f : SI.StepFun) : Prop :=
  Forall (fun s => a <= SI.step_left s /\ SI.step_right s <= b) f.

Lemma inside_nil : forall a b, inside a b [].
Proof. intros a b. constructor. Qed.

Lemma step_eval_single_inside : forall s x,
  SI.step_left s <= x -> x <= SI.step_right s ->
  step_eval [s] x == SI.step_val s.
Proof.
  intros s x Hl Hr. simpl. rewrite (indicator_inside _ _ x Hl Hr). ring.
Qed.

Lemma step_eval_single_outside : forall s x,
  x < SI.step_left s \/ SI.step_right s < x -> step_eval [s] x == 0.
Proof.
  intros s x [H | H]; simpl.
  - rewrite (indicator_outside_left _ _ x H). ring.
  - rewrite (indicator_outside_right _ _ x H). ring.
Qed.

(** Concatenation of lists is the pointwise sum of the functions. *)
Lemma step_eval_app : forall f g x,
  step_eval (f ++ g) x == step_eval f x + step_eval g x.
Proof.
  intros f g x. induction f as [| s r IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Scaling the values of the steps is the pointwise product. *)
Lemma step_eval_scale : forall c f x,
  step_eval (SI.step_fun_scale c f) x == c * step_eval f x.
Proof.
  intros c f x. induction f as [| s r IH]; simpl.
  - ring.
  - unfold SI.step_fun_scale in IH. rewrite IH. ring.
Qed.

Lemma inside_app : forall a b f g,
  inside a b f -> inside a b g -> inside a b (f ++ g).
Proof.
  intros a b f g Hf Hg. unfold inside in *. apply Forall_app. split; assumption.
Qed.

Lemma inside_scale : forall a b c f,
  inside a b f -> inside a b (SI.step_fun_scale c f).
Proof.
  intros a b c f H. unfold inside, SI.step_fun_scale in *.
  induction H as [| s r Hs _ IH]; simpl; constructor.
  - simpl. exact Hs.
  - exact IH.
Qed.

Lemma inside_weaken : forall a b a' b' f,
  a' <= a -> b <= b' -> inside a b f -> inside a' b' f.
Proof.
  intros a b a' b' f Ha Hb H. unfold inside in *.
  induction H as [| s r [Hl Hr] _ IH]; constructor.
  - split; lra.
  - exact IH.
Qed.

(** Every finite list of steps lies in some segment. *)
Lemma inside_exists : forall f : SI.StepFun,
  exists a b : Q, a < b /\ inside a b f.
Proof.
  induction f as [| s r [a [b [Hab Hin]]]].
  - exists 0, 1. split; [lra | constructor].
  - exists (Qmin a (SI.step_left s)), (Qmax b (SI.step_right s)).
    pose proof (Q.le_min_l a (SI.step_left s)) as H1.
    pose proof (Q.le_min_r a (SI.step_left s)) as H2.
    pose proof (Q.le_max_l b (SI.step_right s)) as H3.
    pose proof (Q.le_max_r b (SI.step_right s)) as H4.
    split; [lra |]. constructor.
    + split; assumption.
    + apply (inside_weaken a b); assumption.
Qed.

(* ===================================================================== *)
(*  2. The Riemann process of a step function tends to its step integral  *)
(* ===================================================================== *)

(** One step: the stage sum of the indicator of [c, d] differs from d - c
    by at most one grid step (the rate bound of ProcessMeasureIntervals). *)
Lemma indicator_riemann_close : forall c d a b n,
  a < b -> a <= c -> c <= d -> d <= b ->
  Qabs (riemann_process (indicator c d) a b n - (d - c)) <= integral_step a b n.
Proof.
  intros c d a b n Hab Hac Hcd Hdb.
  exact (measure_process_rate a b c d n Hab Hac Hcd Hdb).
Qed.

Lemma riemann_sum_zero : forall a h j, riemann_sum (fun _ => 0) a h j == 0.
Proof.
  intros a h j. induction j as [| j IH]; simpl; [reflexivity | rewrite IH; ring].
Qed.

(** Stage bound: the deviation is at most (sum |v_i|) * (grid step). *)
Lemma step_eval_riemann_close : forall f a b n, a < b -> inside a b f ->
  Qabs (riemann_process (step_eval f) a b n - SI.step_fun_integral f)
  <= total_abs f * integral_step a b n.
Proof.
  intros f a b n Hab Hin. induction Hin as [| s r [Hl Hr] _ IH].
  - assert (E : riemann_process (step_eval []) a b n - SI.step_fun_integral [] == 0).
    { unfold riemann_process, integral_process.
      change (step_eval []) with (fun _ : Q => 0).
      rewrite riemann_sum_zero. simpl. ring. }
    rewrite E. simpl. lra.
  - pose proof (riemann_process_add
                  (fun y => SI.step_val s * indicator (SI.step_left s) (SI.step_right s) y)
                  (step_eval r) a b n) as Hadd.
    pose proof (riemann_process_scale (SI.step_val s)
                  (indicator (SI.step_left s) (SI.step_right s)) a b n) as Hsc.
    assert (E0 : riemann_process (step_eval (s :: r)) a b n ==
                 SI.step_val s * riemann_process (indicator (SI.step_left s) (SI.step_right s)) a b n
                 + riemann_process (step_eval r) a b n).
    { rewrite <- Hsc. exact Hadd. }
    assert (E : riemann_process (step_eval (s :: r)) a b n - SI.step_fun_integral (s :: r) ==
                SI.step_val s *
                  (riemann_process (indicator (SI.step_left s) (SI.step_right s)) a b n
                   - (SI.step_right s - SI.step_left s))
                + (riemann_process (step_eval r) a b n - SI.step_fun_integral r)).
    { rewrite E0. cbn [SI.step_fun_integral]. unfold SI.step_integral. ring. }
    rewrite E.
    eapply Qle_trans; [apply Qabs_triangle |].
    rewrite Qabs_Qmult.
    pose proof (indicator_riemann_close (SI.step_left s) (SI.step_right s) a b n
                  Hab Hl (SI.step_valid s) Hr) as Hc.
    assert (Hv : 0 <= Qabs (SI.step_val s)) by apply Qabs_nonneg.
    assert (Hm : Qabs (SI.step_val s) *
                 Qabs (riemann_process (indicator (SI.step_left s) (SI.step_right s)) a b n
                       - (SI.step_right s - SI.step_left s))
                 <= Qabs (SI.step_val s) * integral_step a b n).
    { rewrite (Qmult_comm (Qabs (SI.step_val s)) (Qabs _)).
      rewrite (Qmult_comm (Qabs (SI.step_val s)) (integral_step a b n)).
      apply Qmult_le_compat_r; assumption. }
    cbn [total_abs].
    assert (Hexp : (Qabs (SI.step_val s) + total_abs r) * integral_step a b n ==
                   Qabs (SI.step_val s) * integral_step a b n
                   + total_abs r * integral_step a b n) by ring.
    rewrite Hexp. lra.
Qed.

(** The Riemann process of a step function tends to its step integral. *)
Theorem step_riemann_equiv : forall f a b, a < b -> inside a b f ->
  riemann_process (step_eval f) a b ~~ const_process (SI.step_fun_integral f).
Proof.
  intros f a b Hab Hin eps Heps.
  pose proof (total_abs_nonneg f) as HT.
  assert (HT1 : 0 < total_abs f + 1) by lra.
  assert (Hdelta : 0 < eps / (total_abs f + 1)) by (apply Qlt_shift_div_l; lra).
  destruct (integral_step_eventually_small a b (eps / (total_abs f + 1)) Hab Hdelta)
    as [N HN].
  exists N. intros n Hn. unfold const_process.
  apply Qle_lt_trans with (total_abs f * integral_step a b n).
  - apply step_eval_riemann_close; assumption.
  - specialize (HN n Hn).
    pose proof (integral_step_pos a b n Hab) as Hpos.
    assert (H1 : (total_abs f + 1) * integral_step a b n <
                 (total_abs f + 1) * (eps / (total_abs f + 1))).
    { apply Qmult_lt_l; assumption. }
    assert (H2 : (total_abs f + 1) * (eps / (total_abs f + 1)) == eps) by (field; lra).
    assert (H3 : (total_abs f + 1) * integral_step a b n ==
                 total_abs f * integral_step a b n + integral_step a b n) by ring.
    lra.
Qed.

Corollary step_riemann_cauchy : forall f a b, a < b -> inside a b f ->
  is_Cauchy (riemann_process (step_eval f) a b).
Proof.
  intros f a b Hab Hin.
  apply (equiv_cauchy_l (const_process (SI.step_fun_integral f))).
  - apply process_equiv_sym. apply step_riemann_equiv; assumption.
  - apply const_is_Cauchy.
Qed.

(** The same for the "Lebesgue process" of the process layer, which is
    the Riemann process by definition. *)
Corollary lebesgue_step_equiv : forall f a b, a < b -> inside a b f ->
  PL.lebesgue_process (step_eval f) a b ~~ const_process (SI.step_fun_integral f).
Proof.
  intros f a b Hab Hin. unfold PL.lebesgue_process.
  apply step_riemann_equiv; assumption.
Qed.

(* ===================================================================== *)
(*  3. Properties of the step integral for lists of steps                 *)
(* ===================================================================== *)

(** Homogeneity for a list of steps. *)
Lemma step_fun_integral_scale : forall c f,
  SI.step_fun_integral (SI.step_fun_scale c f) == c * SI.step_fun_integral f.
Proof.
  intros c f. induction f as [| s rest IH].
  - simpl. ring.
  - simpl. unfold SI.step_integral at 1 2. simpl.
    unfold SI.step_fun_scale in IH. rewrite IH. ring.
Qed.

(** Monotonicity inside a segment: the pointwise comparison of the functions
    carries over to the integrals (through the Riemann processes). *)
Lemma step_integral_monotone_inside : forall f g a b, a < b ->
  inside a b f -> inside a b g ->
  (forall x, step_eval f x <= step_eval g x) ->
  SI.step_fun_integral f <= SI.step_fun_integral g.
Proof.
  intros f g a b Hab Hf Hg Hle.
  destruct (Qlt_le_dec (SI.step_fun_integral g) (SI.step_fun_integral f)) as [Hlt | Hok];
    [| exact Hok].
  exfalso.
  assert (Heps : 0 < (SI.step_fun_integral f - SI.step_fun_integral g) / 2).
  { apply Qlt_shift_div_l; lra. }
  destruct (step_riemann_equiv f a b Hab Hf _ Heps) as [N1 H1].
  destruct (step_riemann_equiv g a b Hab Hg _ Heps) as [N2 H2].
  specialize (H1 (Nat.max N1 N2) (Nat.le_max_l _ _)).
  specialize (H2 (Nat.max N1 N2) (Nat.le_max_r _ _)).
  unfold const_process in H1, H2.
  pose proof (riemann_process_monotone (step_eval f) (step_eval g) a b
                (Nat.max N1 N2) Hab Hle) as Hm.
  apply Qabs_Qlt_condition in H1. apply Qabs_Qlt_condition in H2.
  assert (He : (SI.step_fun_integral f - SI.step_fun_integral g) / 2 * 2 ==
               SI.step_fun_integral f - SI.step_fun_integral g) by field.
  set (e := (SI.step_fun_integral f - SI.step_fun_integral g) / 2) in *.
  lra.
Qed.

(** Monotonicity: if one step function is nowhere greater than another,
    its integral is not greater. No condition on the partitions. *)
Theorem step_integral_monotone : forall f g : SI.StepFun,
  (forall x, step_eval f x <= step_eval g x) ->
  SI.step_fun_integral f <= SI.step_fun_integral g.
Proof.
  intros f g Hle.
  destruct (inside_exists (f ++ g)) as [a [b [Hab Hin]]].
  unfold inside in Hin. apply Forall_app in Hin. destruct Hin as [Hf Hg].
  exact (step_integral_monotone_inside f g a b Hab Hf Hg Hle).
Qed.

(** The integral depends on the function of the point only, not on the list
    of steps that records it. *)
Theorem step_integral_depends_on_function : forall f g : SI.StepFun,
  (forall x, step_eval f x == step_eval g x) ->
  SI.step_fun_integral f == SI.step_fun_integral g.
Proof.
  intros f g Heq. apply Qle_antisym; apply step_integral_monotone; intro x;
    rewrite (Heq x); apply Qle_refl.
Qed.

Corollary step_fun_integral_nonneg : forall f : SI.StepFun,
  (forall x, 0 <= step_eval f x) -> 0 <= SI.step_fun_integral f.
Proof.
  intros f H.
  change 0 with (SI.step_fun_integral []) at 1.
  apply step_integral_monotone. intro x. simpl. apply H.
Qed.

(** Comparing the values of two steps says nothing about their integrals
    when the segments differ: the comparison must be of the functions. *)
Lemma le_0_2 : 0 <= 2. Proof. lra. Qed.
Lemma le_0_0 : (0:Q) <= 0. Proof. apply Qle_refl. Qed.

Example step_values_do_not_compare_integrals :
  let s1 := SI.mkStep 1 0 2 le_0_2 in
  let s2 := SI.mkStep 2 0 0 le_0_0 in
  SI.step_val s1 <= SI.step_val s2 /\ ~ SI.step_integral s1 <= SI.step_integral s2.
Proof.
  cbv zeta. split.
  - simpl. lra.
  - unfold SI.step_integral. simpl. intro H. lra.
Qed.

(* ===================================================================== *)
(*  4. The norm of a list of steps                                        *)
(* ===================================================================== *)

Lemma SI_norm_cons : forall s r,
  SI.step_fun_norm (s :: r) ==
  Qabs (SI.step_val s) * (SI.step_right s - SI.step_left s) + SI.step_fun_norm r.
Proof.
  intros. unfold SI.step_fun_norm. simpl. unfold SI.step_integral at 1. simpl.
  reflexivity.
Qed.

Lemma SI_norm_nil : SI.step_fun_norm [] == 0.
Proof. reflexivity. Qed.

Lemma SI_norm_app : forall f g,
  SI.step_fun_norm (f ++ g) == SI.step_fun_norm f + SI.step_fun_norm g.
Proof.
  intros f g. induction f as [| s r IH].
  - simpl app. rewrite SI_norm_nil. ring.
  - change ((s :: r) ++ g) with (s :: (r ++ g)). rewrite !SI_norm_cons, IH. ring.
Qed.

Lemma SI_norm_scale_opp : forall h,
  SI.step_fun_norm (SI.step_fun_scale (-(1)) h) == SI.step_fun_norm h.
Proof.
  induction h as [| s r IH].
  - reflexivity.
  - change (SI.step_fun_scale (-(1)) (s :: r)) with
      (SI.mkStep (-(1) * SI.step_val s) (SI.step_left s) (SI.step_right s)
                 (SI.step_valid s) :: SI.step_fun_scale (-(1)) r).
    rewrite !SI_norm_cons, IH. cbn [SI.step_val SI.step_left SI.step_right].
    rewrite Qabs_Qmult.
    assert (E1 : Qabs (-(1)) == 1) by reflexivity.
    rewrite E1. ring.
Qed.

(** |I(h)| <= ||h|| for every list of steps. *)
Lemma integral_abs_le_norm : forall h,
  Qabs (SI.step_fun_integral h) <= SI.step_fun_norm h.
Proof.
  induction h as [| s r IH].
  - rewrite SI_norm_nil. simpl. apply Qle_refl.
  - rewrite SI_norm_cons. cbn [SI.step_fun_integral]. unfold SI.step_integral.
    eapply Qle_trans; [apply Qabs_triangle |].
    rewrite Qabs_Qmult.
    assert (Hw : 0 <= SI.step_right s - SI.step_left s)
      by (pose proof (SI.step_valid s); lra).
    rewrite (Qabs_pos _ Hw). lra.
Qed.

(* ===================================================================== *)
(*  5. L1-closeness that does not depend on the partitions                *)
(* ===================================================================== *)

(** ||f - g||_1 < eps: the difference f - g, as a function of the point,
    has a record by a list of steps in [a, b] whose norm is below eps. *)
Definition l1_close (a b : Q) (f g : SI.StepFun) (eps : Q) : Prop :=
  exists h : SI.StepFun,
    inside a b h /\
    (forall x, step_eval h x == step_eval f x - step_eval g x) /\
    SI.step_fun_norm h < eps.

(** L1-closeness bounds the difference of the integrals; no condition on
    how f and g are partitioned. *)
Theorem l1_close_integral : forall a b f g eps, a < b ->
  inside a b f -> inside a b g -> l1_close a b f g eps ->
  Qabs (SI.step_fun_integral f - SI.step_fun_integral g) < eps.
Proof.
  intros a b f g eps Hab Hf Hg [h [Hh [Hev Hn]]].
  assert (HD : SI.step_fun_integral (f ++ SI.step_fun_scale (-(1)) g)
               == SI.step_fun_integral h).
  { apply step_integral_depends_on_function.
    intro x. rewrite step_eval_app, step_eval_scale, Hev. ring. }
  rewrite SI.integral_app, step_fun_integral_scale in HD.
  assert (E : SI.step_fun_integral f - SI.step_fun_integral g == SI.step_fun_integral h).
  { rewrite <- HD. ring. }
  rewrite E.
  apply Qle_lt_trans with (SI.step_fun_norm h); [apply integral_abs_le_norm | exact Hn].
Qed.

Lemma l1_close_refl : forall a b f eps, 0 < eps -> l1_close a b f f eps.
Proof.
  intros a b f eps Heps. exists []. split; [constructor |]. split.
  - intro x. simpl. ring.
  - rewrite SI_norm_nil. exact Heps.
Qed.

Lemma l1_close_sym : forall a b f g eps,
  l1_close a b f g eps -> l1_close a b g f eps.
Proof.
  intros a b f g eps [h [Hh [Hev Hn]]]. exists (SI.step_fun_scale (-(1)) h).
  split; [apply inside_scale; exact Hh |]. split.
  - intro x. rewrite step_eval_scale, Hev. ring.
  - rewrite SI_norm_scale_opp. exact Hn.
Qed.

Lemma l1_close_trans : forall a b f g k e1 e2,
  l1_close a b f g e1 -> l1_close a b g k e2 -> l1_close a b f k (e1 + e2).
Proof.
  intros a b f g k e1 e2 [h1 [Hh1 [Hev1 Hn1]]] [h2 [Hh2 [Hev2 Hn2]]].
  exists (h1 ++ h2). split; [apply inside_app; assumption |]. split.
  - intro x. rewrite step_eval_app, Hev1, Hev2. ring.
  - rewrite SI_norm_app. lra.
Qed.

Lemma l1_close_le : forall a b f g e e',
  l1_close a b f g e -> e <= e' -> l1_close a b f g e'.
Proof.
  intros a b f g e e' [h [Hh [Hev Hn]]] Hle. exists h.
  split; [exact Hh |]. split; [exact Hev | lra].
Qed.

(** Two lists that record the same function are L1-close with any bound. *)
Lemma l1_close_same_function : forall a b f g eps, 0 < eps ->
  (forall x, step_eval f x == step_eval g x) -> l1_close a b f g eps.
Proof.
  intros a b f g eps Heps Heq. exists []. split; [constructor |]. split.
  - intro x. simpl. rewrite (Heq x). ring.
  - rewrite SI_norm_nil. exact Heps.
Qed.

(* ===================================================================== *)
(*  6. Integrable functions on a segment                                  *)
(* ===================================================================== *)

(** An integrable function on [a, b]: a process of step functions in
    [a, b] that is Cauchy in the sense of L1-closeness. *)
Record L1On (a b : Q) := mkL1On {
  on_seq : nat -> SI.StepFun;
  on_inside : forall n, inside a b (on_seq n);
  on_cauchy : forall eps : Q, 0 < eps -> exists N : nat, forall m n : nat,
    (N <= m)%nat -> (N <= n)%nat -> l1_close a b (on_seq m) (on_seq n) eps
}.

Arguments on_seq {a b} _ _.
Arguments on_inside {a b} _ _.
Arguments on_cauchy {a b} _ _ _.

(** The integral of an integrable function: the process of the integrals
    of its stages. *)
Definition on_integral {a b : Q} (F : L1On a b) : RealProcess :=
  fun n => SI.step_fun_integral (on_seq F n).

(** The integral of an integrable function is a Cauchy process. *)
Theorem l1_on_integral_is_Cauchy : forall a b (F : L1On a b), a < b ->
  is_Cauchy (on_integral F).
Proof.
  intros a b F Hab. unfold is_Cauchy. intros eps Heps.
  destruct (on_cauchy F eps Heps) as [N HN].
  exists N. intros m n Hm Hn. unfold on_integral.
  apply (l1_close_integral a b); [exact Hab | apply on_inside | apply on_inside |].
  apply HN; assumption.
Qed.

(** "Equal almost everywhere" in the L1 sense: ||F_n - G_n||_1 -> 0. *)
Definition l1_on_equiv {a b : Q} (F G : L1On a b) : Prop :=
  forall eps : Q, 0 < eps -> exists N : nat, forall n : nat, (N <= n)%nat ->
    l1_close a b (on_seq F n) (on_seq G n) eps.

(** It is an equivalence relation. *)
Theorem l1_on_equiv_equivalence : forall a b,
  (forall F : L1On a b, l1_on_equiv F F) /\
  (forall F G : L1On a b, l1_on_equiv F G -> l1_on_equiv G F) /\
  (forall F G K : L1On a b, l1_on_equiv F G -> l1_on_equiv G K -> l1_on_equiv F K).
Proof.
  intros a b. split; [| split].
  - intros F eps Heps. exists 0%nat. intros n _. apply l1_close_refl. exact Heps.
  - intros F G H eps Heps. destruct (H eps Heps) as [N HN].
    exists N. intros n Hn. apply l1_close_sym. apply HN. exact Hn.
  - intros F G K H1 H2 eps Heps.
    assert (He2 : 0 < eps / 2) by (apply Qlt_shift_div_l; lra).
    destruct (H1 (eps / 2) He2) as [N1 HN1]. destruct (H2 (eps / 2) He2) as [N2 HN2].
    exists (Nat.max N1 N2). intros n Hn.
    apply l1_close_le with (eps / 2 + eps / 2).
    + apply l1_close_trans with (on_seq G n).
      * apply HN1. lia.
      * apply HN2. lia.
    + assert (Hs : eps / 2 + eps / 2 == eps) by field. lra.
Qed.

(** Equivalent integrable functions have the same integral: their integral
    processes name one point. *)
Theorem l1_on_equiv_integral : forall a b (F G : L1On a b), a < b ->
  l1_on_equiv F G -> on_integral F ~~ on_integral G.
Proof.
  intros a b F G Hab H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. unfold on_integral.
  apply (l1_close_integral a b); [exact Hab | apply on_inside | apply on_inside |].
  apply HN. exact Hn.
Qed.

(** Embedding of a step function: the constant process. *)
Definition step_to_l1_on (a b : Q) (f : SI.StepFun) (Hf : inside a b f) : L1On a b.
Proof.
  refine (mkL1On a b (fun _ => f) (fun _ => Hf) _).
  intros eps Heps. exists 0%nat. intros m n _ _. apply l1_close_refl. exact Heps.
Defined.

Lemma step_to_l1_on_integral : forall a b f Hf n,
  on_integral (step_to_l1_on a b f Hf) n = SI.step_fun_integral f.
Proof. reflexivity. Qed.

(** Two lists that record the same function are embedded into one class. *)
Lemma step_to_l1_on_ext : forall a b f g Hf Hg,
  (forall x, step_eval f x == step_eval g x) ->
  l1_on_equiv (step_to_l1_on a b f Hf) (step_to_l1_on a b g Hg).
Proof.
  intros a b f g Hf Hg Heq eps Heps. exists 0%nat. intros n _.
  change (l1_close a b f g eps). apply l1_close_same_function; assumption.
Qed.

(** Lebesgue agrees with Riemann on step functions: the process of the
    process layer and the L1 integral of the embedded step function name
    the same point. *)
Theorem lebesgue_step_agrees : forall a b f (Hf : inside a b f), a < b ->
  PL.lebesgue_process (step_eval f) a b ~~ on_integral (step_to_l1_on a b f Hf).
Proof.
  intros a b f Hf Hab eps Heps.
  destruct (lebesgue_step_equiv f a b Hab Hf eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold const_process in HN.
  rewrite step_to_l1_on_integral. exact HN.
Qed.

(* ===================================================================== *)
(*  7. Examples                                                           *)
(* ===================================================================== *)

(** The constant v on [0, 1]. *)
Definition const_step (v : Q) : SI.StepFun := [SI.mkStep v 0 1 SI.le_0_1].

Lemma inside_const_step : forall v, inside 0 1 (const_step v).
Proof.
  intro v. constructor; [| constructor]. simpl. split; apply Qle_refl.
Qed.

Lemma norm_const_step : forall v, SI.step_fun_norm (const_step v) == Qabs v.
Proof. intro v. exact (SI.norm_constant v). Qed.

Lemma step_eval_const_step : forall v x,
  step_eval (const_step v) x == v * indicator 0 1 x.
Proof. intros v x. unfold const_step. cbn [step_eval SI.step_val SI.step_left SI.step_right]. ring. Qed.

Lemma half_pow_small : forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat -> half_pow n < eps.
Proof.
  intros eps Heps. destruct (rationals_cover_to_zero eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold const_process in HN.
  apply Qabs_Qlt_condition in HN. lra.
Qed.

(** A non-stationary integrable function: the constants (1/2)^n on [0, 1]. *)
Definition shrinking : L1On 0 1.
Proof.
  refine (mkL1On 0 1 (fun n => const_step (half_pow n))
                     (fun n => inside_const_step (half_pow n)) _).
  intros eps Heps. destruct (half_pow_small eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  exists (const_step (half_pow m - half_pow n)).
  split; [apply inside_const_step |]. split.
  - intro x. rewrite !step_eval_const_step. ring.
  - rewrite norm_const_step.
    pose proof (HN m Hm). pose proof (HN n Hn).
    pose proof (half_pow_pos m). pose proof (half_pow_pos n).
    apply Qabs_Qlt_condition. split; lra.
Defined.

(** The zero function on [a, b]. *)
Definition zero_on (a b : Q) : L1On a b := step_to_l1_on a b [] (inside_nil a b).

(** It is equivalent to zero: a non-stationary process and a stationary
    one in the same class. *)
Example shrinking_equiv_zero : l1_on_equiv shrinking (zero_on 0 1).
Proof.
  intros eps Heps. destruct (half_pow_small eps Heps) as [N HN].
  exists N. intros n Hn.
  change (l1_close 0 1 (const_step (half_pow n)) [] eps).
  exists (const_step (half_pow n)). split; [apply inside_const_step |]. split.
  - intro x. cbn [step_eval]. ring.
  - rewrite norm_const_step.
    rewrite Qabs_pos; [apply HN; exact Hn | apply Qlt_le_weak, half_pow_pos].
Qed.

(** The relation is not trivial: the constant 1 is not equivalent to zero. *)
Example one_not_equiv_zero :
  ~ l1_on_equiv (step_to_l1_on 0 1 (const_step 1) (inside_const_step 1)) (zero_on 0 1).
Proof.
  intro H.
  assert (H01 : 0 < 1) by lra.
  destruct (l1_on_equiv_integral 0 1 _ _ H01 H 1 H01) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  unfold zero_on in HN. rewrite !step_to_l1_on_integral in HN.
  assert (E : SI.step_fun_integral (const_step 1) - SI.step_fun_integral [] == 1).
  { unfold const_step. cbn [SI.step_fun_integral]. unfold SI.step_integral.
    cbn [SI.step_val SI.step_left SI.step_right]. ring. }
  rewrite E in HN. exact (Qlt_irrefl 1 HN).
Qed.

Lemma inside_point : forall a b c (Hcc : c <= c), a <= c -> c <= b ->
  inside a b [SI.mkStep 1 c c Hcc].
Proof.
  intros a b c Hcc Ha Hb. constructor; [| constructor]. simpl. split; assumption.
Qed.

(** "Almost everywhere" at work: a function that equals 1 at one point and
    0 elsewhere differs from zero at that point, and is equivalent to zero. *)
Example point_differs_but_equivalent :
  forall a b c (Hcc : c <= c) (Ha : a <= c) (Hb : c <= b),
  l1_on_equiv (step_to_l1_on a b [SI.mkStep 1 c c Hcc] (inside_point a b c Hcc Ha Hb))
              (zero_on a b)
  /\ step_eval [SI.mkStep 1 c c Hcc] c == 1
  /\ step_eval [] c == 0.
Proof.
  intros a b c Hcc Ha Hb. split; [| split].
  - intros eps Heps. exists 0%nat. intros n _.
    change (l1_close a b [SI.mkStep 1 c c Hcc] [] eps).
    exists [SI.mkStep 1 c c Hcc]. split; [apply inside_point; assumption |]. split.
    + intro x. cbn [step_eval]. ring.
    + rewrite SI_norm_cons, SI_norm_nil. cbn [SI.step_val SI.step_left SI.step_right].
      assert (E : Qabs 1 * (c - c) + 0 == 0) by (change (Qabs 1) with 1; ring).
      rewrite E. exact Heps.
  - apply (step_eval_single_inside (SI.mkStep 1 c c Hcc) c); simpl; apply Qle_refl.
  - reflexivity.
Qed.

(* ===================================================================== *)
(*  8. Series of steps: integrable functions beyond the stages            *)
(* ===================================================================== *)

(** The first n steps of a sequence of steps. *)
Fixpoint prefix (s : nat -> SI.Step) (n : nat) : SI.StepFun :=
  match n with
  | O => []
  | S k => prefix s k ++ [s k]
  end.

(** The d steps that follow the first n. *)
Fixpoint tail (s : nat -> SI.Step) (n d : nat) : SI.StepFun :=
  match d with
  | O => []
  | S k => tail s n k ++ [s (n + k)%nat]
  end.

Lemma prefix_split : forall s n d,
  prefix s (n + d)%nat = prefix s n ++ tail s n d.
Proof.
  intros s n d. induction d as [| d IH].
  - rewrite Nat.add_0_r. cbn [tail]. rewrite app_nil_r. reflexivity.
  - rewrite Nat.add_succ_r. cbn [prefix tail]. rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma inside_prefix : forall a b s,
  (forall k, a <= SI.step_left (s k) /\ SI.step_right (s k) <= b) ->
  forall n, inside a b (prefix s n).
Proof.
  intros a b s H n. induction n as [| n IH]; cbn [prefix].
  - constructor.
  - apply inside_app; [exact IH | constructor; [apply H | constructor]].
Qed.

Lemma inside_tail : forall a b s,
  (forall k, a <= SI.step_left (s k) /\ SI.step_right (s k) <= b) ->
  forall n d, inside a b (tail s n d).
Proof.
  intros a b s H n d. induction d as [| d IH]; cbn [tail].
  - constructor.
  - apply inside_app; [exact IH | constructor; [apply H | constructor]].
Qed.

(** The norms of the steps are summable: the tails become small. *)
Definition summable (s : nat -> SI.Step) : Prop :=
  forall eps, 0 < eps -> exists N, forall n d, (N <= n)%nat ->
    SI.step_fun_norm (tail s n d) < eps.

(** A series of steps in [a, b] with summable norms is an integrable
    function: its stages are the partial sums. *)
Definition series_l1 (a b : Q) (s : nat -> SI.Step)
  (Hin : forall k, a <= SI.step_left (s k) /\ SI.step_right (s k) <= b)
  (Hsum : summable s) : L1On a b.
Proof.
  refine (mkL1On a b (prefix s) (inside_prefix a b s Hin) _).
  intros eps Heps. destruct (Hsum eps Heps) as [N HN]. exists N.
  assert (Hle : forall m n, (N <= n)%nat -> (n <= m)%nat ->
                l1_close a b (prefix s m) (prefix s n) eps).
  { intros m n Hn Hnm.
    assert (Em : m = (n + (m - n))%nat) by lia.
    exists (tail s n (m - n)). split; [apply inside_tail; exact Hin |]. split.
    - intro x. rewrite Em at 2. rewrite prefix_split, step_eval_app. ring.
    - apply HN. exact Hn. }
  intros m n Hm Hn. destruct (Nat.le_ge_cases n m) as [H | H].
  - apply Hle; assumption.
  - apply l1_close_sym. apply Hle; assumption.
Defined.

Lemma prefix_integral_S : forall s n,
  SI.step_fun_integral (prefix s (S n)) ==
  SI.step_fun_integral (prefix s n) + SI.step_integral (s n).
Proof.
  intros s n. cbn [prefix]. rewrite SI.integral_app, SI.integral_singleton. reflexivity.
Qed.

(** The staircase: the step of height (1/2)^k on [0, (1/2)^k], k = 0, 1, ...
    Infinitely many steps accumulating at 0. *)
Definition stair_step (k : nat) : SI.Step :=
  SI.mkStep (half_pow k) 0 (half_pow k) (half_pow_nonneg k).

Lemma stair_inside : forall k,
  0 <= SI.step_left (stair_step k) /\ SI.step_right (stair_step k) <= 1.
Proof.
  intro k. cbn [stair_step SI.step_left SI.step_right].
  split; [apply Qle_refl | apply half_pow_le_one].
Qed.

Lemma stair_step_norm : forall k,
  SI.step_fun_norm [stair_step k] == half_pow k * half_pow k.
Proof.
  intro k. rewrite SI_norm_cons, SI_norm_nil.
  cbn [stair_step SI.step_val SI.step_left SI.step_right].
  rewrite (Qabs_pos (half_pow k) (half_pow_nonneg k)). ring.
Qed.

Lemma stair_tail_bound : forall n d,
  SI.step_fun_norm (tail stair_step n d) <= 2 * half_pow n - 2 * half_pow (n + d).
Proof.
  intros n d. induction d as [| d IH].
  - cbn [tail]. rewrite SI_norm_nil, Nat.add_0_r. lra.
  - cbn [tail]. rewrite SI_norm_app, stair_step_norm, Nat.add_succ_r.
    cbn [half_pow].
    pose proof (half_pow_nonneg (n + d)) as H0.
    pose proof (half_pow_le_one (n + d)) as H1.
    assert (Hsq : half_pow (n + d) * half_pow (n + d) <= 1 * half_pow (n + d))
      by (apply Qmult_le_compat_r; assumption).
    set (h := half_pow (n + d)) in *.
    set (hh := h * h) in *.
    lra.
Qed.

Lemma stair_summable : summable stair_step.
Proof.
  intros eps Heps.
  assert (He2 : 0 < eps / 2) by (apply Qlt_shift_div_l; lra).
  destruct (half_pow_small (eps / 2) He2) as [N HN]. exists N. intros n d Hn.
  pose proof (stair_tail_bound n d) as Hb. pose proof (HN n Hn) as Hs.
  pose proof (half_pow_pos (n + d)) as Hp.
  assert (E : eps / 2 * 2 == eps) by field.
  set (e2 := eps / 2) in *.
  lra.
Qed.

Definition staircase : L1On 0 1 := series_l1 0 1 stair_step stair_inside stair_summable.

Lemma staircase_integral : forall n,
  on_integral staircase n = SI.step_fun_integral (prefix stair_step n).
Proof. reflexivity. Qed.

Lemma stair_integral_S : forall n,
  SI.step_fun_integral (prefix stair_step (S n)) ==
  SI.step_fun_integral (prefix stair_step n) + half_pow n * half_pow n.
Proof.
  intro n. rewrite prefix_integral_S. unfold SI.step_integral.
  cbn [stair_step SI.step_val SI.step_left SI.step_right]. ring.
Qed.

Lemma stair_integral_mono : forall n d,
  SI.step_fun_integral (prefix stair_step n) <=
  SI.step_fun_integral (prefix stair_step (n + d)).
Proof.
  intros n d. induction d as [| d IH].
  - rewrite Nat.add_0_r. apply Qle_refl.
  - rewrite Nat.add_succ_r, stair_integral_S.
    pose proof (half_pow_nonneg (n + d)) as H0.
    assert (Hsq : 0 <= half_pow (n + d) * half_pow (n + d))
      by (apply Qmult_le_0_compat; assumption).
    set (hh := half_pow (n + d) * half_pow (n + d)) in *.
    lra.
Qed.

(** The staircase is not equivalent to any of its own stages: the limit
    lies beyond every finite partial sum. *)
Example staircase_beyond_every_stage : forall n,
  ~ l1_on_equiv staircase
      (step_to_l1_on 0 1 (prefix stair_step n) (inside_prefix 0 1 stair_step stair_inside n)).
Proof.
  intros n H.
  assert (H01 : 0 < 1) by lra.
  pose proof (half_pow_pos n) as Hp.
  assert (Heps : 0 < half_pow n * half_pow n)
    by (apply Qmult_lt_0_compat; assumption).
  destruct (l1_on_equiv_integral 0 1 _ _ H01 H _ Heps) as [N HN].
  assert (Hm : (N <= S n + N)%nat) by lia.
  specialize (HN (S n + N)%nat Hm).
  rewrite staircase_integral, step_to_l1_on_integral in HN.
  pose proof (stair_integral_mono (S n) N) as Hmono.
  pose proof (stair_integral_S n) as HS.
  apply Qabs_Qlt_condition in HN.
  set (hh := half_pow n * half_pow n) in *.
  lra.
Qed.

(* ===================================================================== *)
(*  9. The positional difference of StepIntegral.v as a special case      *)
(* ===================================================================== *)

(** Two lists on a common partition: the same segments in the same order. *)
Definition SI_aligned (f g : SI.StepFun) : Prop :=
  Forall2 (fun s t => SI.step_left s == SI.step_left t /\
                      SI.step_right s == SI.step_right t) f g.

Lemma indicator_wd : forall c d c' d' x,
  c == c' -> d == d' -> indicator c d x == indicator c' d' x.
Proof.
  intros c d c' d' x Hc Hd. unfold indicator.
  assert (H1 : Qle_bool c x = Qle_bool c' x).
  { apply Bool.eq_true_iff_eq. rewrite !Qle_bool_iff. rewrite Hc. reflexivity. }
  assert (H2 : Qle_bool x d = Qle_bool x d').
  { apply Bool.eq_true_iff_eq. rewrite !Qle_bool_iff. rewrite Hd. reflexivity. }
  rewrite H1, H2. reflexivity.
Qed.

Lemma step_eval_diff_aligned : forall f g, SI_aligned f g ->
  forall x, step_eval (SI.step_fun_diff f g) x == step_eval f x - step_eval g x.
Proof.
  intros f g H x. induction H as [| s t f' g' [Hl Hr] _ IH].
  - simpl. ring.
  - simpl. rewrite IH.
    rewrite (indicator_wd (SI.step_left t) (SI.step_right t)
                          (SI.step_left s) (SI.step_right s) x);
      [ring | symmetry; exact Hl | symmetry; exact Hr].
Qed.

Lemma inside_diff : forall a b f g,
  inside a b f -> inside a b (SI.step_fun_diff f g).
Proof.
  intros a b f g H. revert g. unfold inside in *.
  induction H as [| s r Hs _ IH]; intros [| t g']; simpl; constructor.
  - simpl. exact Hs.
  - apply IH.
Qed.

(** On a common partition the positional difference of StepIntegral.v
    witnesses L1-closeness. *)
Lemma aligned_close : forall a b f g eps,
  SI_aligned f g -> inside a b f ->
  SI.step_fun_norm (SI.step_fun_diff f g) < eps -> l1_close a b f g eps.
Proof.
  intros a b f g eps Hal Hf Hn. exists (SI.step_fun_diff f g).
  split; [apply inside_diff; exact Hf |]. split.
  - apply step_eval_diff_aligned. exact Hal.
  - exact Hn.
Qed.

(* ===================================================================== *)
(*  10. The earlier type L1Space.L1Process                                *)
(* ===================================================================== *)

(** L1Space.v keeps its own copy of the record of a step; the bridge. *)
Definition to_l1_step (s : SI.Step) : L1.Step :=
  L1.mkStep (SI.step_val s) (SI.step_left s) (SI.step_right s) (SI.step_valid s).

Definition to_l1 (f : SI.StepFun) : L1.StepFun := map to_l1_step f.

Lemma to_l1_integral : forall f : SI.StepFun,
  L1.step_fun_integral (to_l1 f) = SI.step_fun_integral f.
Proof.
  induction f as [| s r IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** The same agreement for the embedding [step_to_l1] of L1Space.v. *)
Corollary lebesgue_step_agrees_l1space : forall f a b, a < b -> inside a b f ->
  PL.lebesgue_process (step_eval f) a b
    ~~ L1.l1_integral_approx (L1.step_to_l1 (to_l1 f)).
Proof.
  intros f a b Hab Hin eps Heps.
  destruct (lebesgue_step_equiv f a b Hab Hin eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold const_process in HN.
  rewrite L1.step_to_l1_integral. rewrite to_l1_integral. exact HN.
Qed.

(** --- 10.1 What holds on a common partition --------------------------- *)

Definition L1_aligned (f g : L1.StepFun) : Prop :=
  Forall2 (fun s t => L1.step_left s == L1.step_left t /\
                      L1.step_right s == L1.step_right t) f g.

Lemma L1_diff_norm_cons : forall s t f g,
  L1.step_fun_norm (L1.step_fun_diff (s :: f) (t :: g)) ==
  Qabs (L1.step_val s - L1.step_val t) * (L1.step_right s - L1.step_left s)
  + L1.step_fun_norm (L1.step_fun_diff f g).
Proof.
  intros. unfold L1.step_fun_norm. simpl. unfold L1.step_integral at 1. simpl.
  reflexivity.
Qed.

Lemma L1_integral_diff_le_norm : forall f g, L1_aligned f g ->
  Qabs (L1.step_fun_integral f - L1.step_fun_integral g)
  <= L1.step_fun_norm (L1.step_fun_diff f g).
Proof.
  intros f g H. induction H as [| s t f' g' [Hl Hr] Hrest IH].
  - unfold L1.step_fun_norm. simpl. apply Qle_refl.
  - pose proof (L1.integral_diff_le_norm_single s t Hl Hr) as Hs.
    rewrite L1_diff_norm_cons.
    apply Qabs_Qle_condition in Hs. apply Qabs_Qle_condition in IH.
    apply Qabs_Qle_condition. cbn [L1.step_fun_integral].
    set (A := Qabs (L1.step_val s - L1.step_val t) * (L1.step_right s - L1.step_left s)) in *.
    set (N := L1.step_fun_norm (L1.step_fun_diff f' g')) in *.
    split; lra.
Qed.

(** All stages of the process are written on one partition. *)
Definition l1_aligned (f : L1.L1Process) : Prop :=
  forall m n, L1_aligned (L1.l1_seq f m) (L1.l1_seq f n).

(** On a common partition the integral of an L1Process is a Cauchy process. *)
Theorem l1_integral_cauchy_aligned : forall f : L1.L1Process,
  l1_aligned f -> is_Cauchy (L1.l1_integral_approx f).
Proof.
  intros f Hal. unfold is_Cauchy. intros eps Heps.
  destruct (L1.l1_cauchy f eps Heps) as [N HN]. exists N. intros m n Hm Hn.
  unfold L1.l1_integral_approx.
  apply Qle_lt_trans with (L1.step_fun_norm (L1.step_fun_diff (L1.l1_seq f m) (L1.l1_seq f n))).
  - apply L1_integral_diff_le_norm. apply Hal.
  - apply HN; assumption.
Qed.

Lemma L1_aligned_refl : forall f, L1_aligned f f.
Proof.
  induction f as [| s r IH]; constructor.
  - split; reflexivity.
  - exact IH.
Qed.

Lemma L1_aligned_sym : forall f g, L1_aligned f g -> L1_aligned g f.
Proof.
  intros f g H. induction H as [| s t f' g' [Hl Hr] _ IH]; constructor.
  - split; symmetry; assumption.
  - exact IH.
Qed.

Lemma L1_aligned_trans : forall f g h, L1_aligned f g -> L1_aligned g h -> L1_aligned f h.
Proof.
  intros f g h H. revert h. induction H as [| s t f' g' [Hl Hr] _ IH]; intros h Hgh.
  - inversion Hgh. constructor.
  - inversion Hgh as [| t' u g'' h' [Hl' Hr'] Hrest]; subst. constructor.
    + split; [rewrite Hl; exact Hl' | rewrite Hr; exact Hr'].
    + apply IH. exact Hrest.
Qed.

Lemma L1_diff_norm_sym : forall f g, L1_aligned f g ->
  L1.step_fun_norm (L1.step_fun_diff f g) == L1.step_fun_norm (L1.step_fun_diff g f).
Proof.
  intros f g H. induction H as [| s t f' g' [Hl Hr] _ IH].
  - reflexivity.
  - rewrite !L1_diff_norm_cons. rewrite IH.
    assert (Ha : Qabs (L1.step_val s - L1.step_val t) == Qabs (L1.step_val t - L1.step_val s)).
    { rewrite (Qabs_Qminus (L1.step_val s) (L1.step_val t)). reflexivity. }
    rewrite Ha, Hl, Hr. reflexivity.
Qed.

Lemma L1_diff_norm_triangle : forall f g h, L1_aligned f g -> L1_aligned g h ->
  L1.step_fun_norm (L1.step_fun_diff f h) <=
  L1.step_fun_norm (L1.step_fun_diff f g) + L1.step_fun_norm (L1.step_fun_diff g h).
Proof.
  intros f g h H. revert h. induction H as [| s t f' g' [Hl Hr] _ IH]; intros h Hgh.
  - inversion Hgh. unfold L1.step_fun_norm. simpl. lra.
  - inversion Hgh as [| t' u g'' h' [Hl' Hr'] Hrest]; subst.
    rewrite !L1_diff_norm_cons. specialize (IH h' Hrest).
    assert (Hw : 0 <= L1.step_right s - L1.step_left s)
      by (pose proof (L1.step_valid s); lra).
    assert (Hwt : L1.step_right t - L1.step_left t == L1.step_right s - L1.step_left s)
      by (rewrite Hl, Hr; reflexivity).
    rewrite Hwt.
    assert (Htri : Qabs (L1.step_val s - L1.step_val u) <=
                   Qabs (L1.step_val s - L1.step_val t) + Qabs (L1.step_val t - L1.step_val u)).
    { assert (Hd : L1.step_val s - L1.step_val u ==
                   (L1.step_val s - L1.step_val t) + (L1.step_val t - L1.step_val u)) by ring.
      rewrite Hd. apply Qabs_triangle. }
    assert (Hm : Qabs (L1.step_val s - L1.step_val u) * (L1.step_right s - L1.step_left s) <=
                 (Qabs (L1.step_val s - L1.step_val t) + Qabs (L1.step_val t - L1.step_val u))
                 * (L1.step_right s - L1.step_left s)).
    { apply Qmult_le_compat_r; assumption. }
    set (W := L1.step_right s - L1.step_left s) in *.
    set (A := Qabs (L1.step_val s - L1.step_val u)) in *.
    set (B := Qabs (L1.step_val s - L1.step_val t)) in *.
    set (C := Qabs (L1.step_val t - L1.step_val u)) in *.
    assert (Hexp : (B + C) * W == B * W + C * W) by ring.
    rewrite Hexp in Hm. lra.
Qed.

(** Two processes written stage by stage on one partition. *)
Definition aligned_pair (f g : L1.L1Process) : Prop :=
  forall n, L1_aligned (L1.l1_seq f n) (L1.l1_seq g n).

(** The relation of L1Space.v together with the common partition. *)
Definition l1_equiv_al (f g : L1.L1Process) : Prop :=
  aligned_pair f g /\ L1.l1_equiv f g.

(** On a common partition it is an equivalence relation. *)
Theorem l1_equiv_al_equivalence :
  (forall f, l1_equiv_al f f) /\
  (forall f g, l1_equiv_al f g -> l1_equiv_al g f) /\
  (forall f g h, l1_equiv_al f g -> l1_equiv_al g h -> l1_equiv_al f h).
Proof.
  split; [| split].
  - intro f. split; [intro n; apply L1_aligned_refl | apply L1.l1_equiv_refl].
  - intros f g [Hal H]. split.
    + intro n. apply L1_aligned_sym. apply Hal.
    + intros eps Heps. destruct (H eps Heps) as [N HN].
      exists N. intros n Hn. rewrite <- (L1_diff_norm_sym _ _ (Hal n)). apply HN. exact Hn.
  - intros f g h [Hfg H1] [Hgh H2]. split.
    + intro n. apply L1_aligned_trans with (L1.l1_seq g n); [apply Hfg | apply Hgh].
    + intros eps Heps.
      assert (He2 : 0 < eps / 2) by (apply Qlt_shift_div_l; lra).
      destruct (H1 (eps / 2) He2) as [N1 HN1]. destruct (H2 (eps / 2) He2) as [N2 HN2].
      exists (Nat.max N1 N2). intros n Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia. assert (Hn2 : (N2 <= n)%nat) by lia.
      pose proof (HN1 n Hn1) as A1. pose proof (HN2 n Hn2) as A2.
      pose proof (L1_diff_norm_triangle _ _ _ (Hfg n) (Hgh n)) as T.
      assert (Hs : eps / 2 + eps / 2 == eps) by field.
      lra.
Qed.

(** ... and it keeps the integral. *)
Theorem l1_equiv_al_integral : forall f g, l1_equiv_al f g ->
  L1.l1_integral_approx f ~~ L1.l1_integral_approx g.
Proof.
  intros f g [Hal H] eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. unfold L1.l1_integral_approx.
  apply Qle_lt_trans with (L1.step_fun_norm (L1.step_fun_diff (L1.l1_seq f n) (L1.l1_seq g n))).
  - apply L1_integral_diff_le_norm. apply Hal.
  - apply HN. exact Hn.
Qed.

(** --- 10.2 Why the premise is needed ---------------------------------- *)

Lemma nat_Q_nonneg : forall n : nat, 0 <= inject_Z (Z.of_nat n).
Proof. intro n. unfold Qle. simpl. lia. Qed.

(** The value 1 on [0, n]: the positional difference of two stages has
    norm 0, the integrals are 0, 1, 2, ... *)
Definition wide_seq (n : nat) : L1.StepFun :=
  [L1.mkStep 1 0 (inject_Z (Z.of_nat n)) (nat_Q_nonneg n)].

Lemma wide_seq_diff_norm : forall m n,
  L1.step_fun_norm (L1.step_fun_diff (wide_seq m) (wide_seq n)) == 0.
Proof.
  intros m n. unfold L1.step_fun_norm, wide_seq. simpl.
  unfold L1.step_integral. simpl.
  assert (E : Qabs (1 - 1) == 0) by reflexivity.
  rewrite E. ring.
Qed.

Definition wide : L1.L1Process.
Proof.
  refine (L1.mkL1 wide_seq _).
  intros eps Heps. exists 0%nat. intros m n _ _.
  rewrite wide_seq_diff_norm. exact Heps.
Defined.

Lemma wide_integral : forall n,
  L1.l1_integral_approx wide n == inject_Z (Z.of_nat n).
Proof.
  intro n. unfold L1.l1_integral_approx, wide, wide_seq. simpl.
  unfold L1.step_integral. simpl. ring.
Qed.

(** Without the common partition the integral of an L1Process need not be
    a Cauchy process: its stages can be unbounded. *)
Example l1_process_integral_unbounded :
  exists f : L1.L1Process,
    (forall M : nat, inject_Z (Z.of_nat M) <= L1.l1_integral_approx f M) /\
    ~ is_Cauchy (L1.l1_integral_approx f).
Proof.
  exists wide. split.
  - intro M. rewrite wide_integral. apply Qle_refl.
  - intro H. assert (H01 : 0 < 1) by lra.
    destruct (H 1 H01) as [N HN].
    assert (HSN : (N <= S N)%nat) by lia.
    specialize (HN (S N) N HSN (Nat.le_refl N)).
    rewrite !wide_integral in HN.
    assert (E : inject_Z (Z.of_nat (S N)) - inject_Z (Z.of_nat N) == 1).
    { rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. ring. }
    rewrite E in HN. exact (Qlt_irrefl 1 HN).
Qed.

Lemma L1_diff_nil_r : forall f : L1.StepFun, L1.step_fun_diff f [] = [].
Proof. intros [| s r]; reflexivity. Qed.

(** Without the common partition the relation of L1Space.v is not
    transitive: every process is related to the empty list. *)
Example l1_equiv_not_transitive :
  exists f g h : L1.L1Process,
    L1.l1_equiv f g /\ L1.l1_equiv g h /\ ~ L1.l1_equiv f h.
Proof.
  exists (L1.step_to_l1 [L1.mkStep 1 0 1 L1.le_0_1]),
         (L1.step_to_l1 []),
         (L1.step_to_l1 [L1.mkStep 0 0 1 L1.le_0_1]).
  split; [| split].
  - intros eps Heps. exists 0%nat. intros n _. simpl.
    unfold L1.step_fun_norm. simpl. exact Heps.
  - intros eps Heps. exists 0%nat. intros n _. simpl.
    unfold L1.step_fun_norm. simpl. exact Heps.
  - intro H. assert (H01 : 0 < 1) by lra.
    destruct (H 1 H01) as [N HN]. specialize (HN N (le_n N)).
    simpl in HN. unfold L1.step_fun_norm in HN. simpl in HN.
    unfold L1.step_integral in HN. simpl in HN.
    revert HN. unfold Qlt. simpl. lia.
Qed.
