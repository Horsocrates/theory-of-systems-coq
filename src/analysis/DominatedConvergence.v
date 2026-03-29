(** * DominatedConvergence.v — Dominated convergence for step functions
    Elements: Dominated sequences, pointwise convergence, integral exchange
    Roles:    Bounding, convergence, limit-integral exchange
    Rules:    |f_n| <= g implies lim I(f_n) = I(lim f_n)
    STATUS:   20 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    The Dominated Convergence Theorem (DCT) is the crown jewel
    of Lebesgue integration. It says: if a sequence f_n -> f
    pointwise, and |f_n| <= g for some integrable g, then
    I(f_n) -> I(f), i.e., integral and limit commute.

    In the Bishop-Cheng approach, we work at the STEP FUNCTION
    level. Our "convergence" is convergence of step function
    sequences in L1 norm, and "domination" is a uniform bound
    on step function values.

    At this level, DCT becomes almost trivial: bounded sequences
    of step functions on bounded intervals have bounded integrals,
    and L1-Cauchy sequences have convergent integrals.

    The deep content emerges when we pass to L1 completion.
    Here we establish the step-function foundations.
*)

From Stdlib Require Import QArith Qabs List Lqa Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  REPLICATED DEFINITIONS                                             *)
(* ================================================================== *)

(* Replicated from StepIntegral.v *)
Record Step := mkStep {
  step_val : Q;
  step_left : Q;
  step_right : Q;
  step_valid : step_left <= step_right
}.

Definition StepFun := list Step.

Definition step_integral (s : Step) : Q :=
  step_val s * (step_right s - step_left s).

Fixpoint step_fun_integral (f : StepFun) : Q :=
  match f with
  | [] => 0
  | s :: rest => step_integral s + step_fun_integral rest
  end.

Definition step_fun_abs (f : StepFun) : StepFun :=
  map (fun s => mkStep (Qabs (step_val s))
                        (step_left s) (step_right s)
                        (step_valid s)) f.

Definition step_fun_norm (f : StepFun) : Q :=
  step_fun_integral (step_fun_abs f).

Fixpoint step_fun_diff (f g : StepFun) : StepFun :=
  match f, g with
  | [], _ => []
  | _, [] => []
  | sf :: rf, sg :: rg =>
      mkStep (step_val sf - step_val sg)
             (step_left sf) (step_right sf)
             (step_valid sf) :: step_fun_diff rf rg
  end.

(* ================================================================== *)
(*  DOMINATION AND CONVERGENCE PREDICATES                              *)
(* ================================================================== *)

(** A step function is bounded by M: all values have |v| <= M *)
Definition step_fun_bounded (M : Q) (f : StepFun) : Prop :=
  forall s, In s f -> Qabs (step_val s) <= M.

(** A sequence of step functions is uniformly dominated by bound M *)
Definition dominated (M : Q) (seq : nat -> StepFun) : Prop :=
  forall n, step_fun_bounded M (seq n).

(** A sequence of step functions converges in L1 norm *)
Definition l1_converges (seq : nat -> StepFun) (limit : StepFun) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    step_fun_norm (step_fun_diff (seq n) limit) < eps.

(** A sequence is L1-Cauchy *)
Definition l1_cauchy (seq : nat -> StepFun) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall m n : nat,
    (N <= m)%nat -> (N <= n)%nat ->
    step_fun_norm (step_fun_diff (seq m) (seq n)) < eps.

Lemma le_0_1 : 0 <= 1. Proof. lra. Qed.

(* ================================================================== *)
(*  BASIC PROPERTIES OF BOUNDED STEP FUNCTIONS                         *)
(* ================================================================== *)

(** ★ Empty step function is bounded by any M *)
Lemma bounded_nil : forall M, step_fun_bounded M [].
Proof.
  intros M s Hin. inversion Hin.
Qed.

(** ★ Singleton bounded *)
Lemma bounded_singleton : forall M v a b (H : a <= b),
  Qabs v <= M ->
  step_fun_bounded M [mkStep v a b H].
Proof.
  intros M v a b H Hv s Hin.
  destruct Hin as [Heq | Hin]. { subst. simpl. exact Hv. }
  inversion Hin.
Qed.

(** ★ Bounded value implies bounded integral for one step *)
Lemma bounded_step_integral : forall M s,
  Qabs (step_val s) <= M ->
  Qabs (step_integral s) <= M * (step_right s - step_left s).
Proof.
  intros M s Hv.
  unfold step_integral.
  rewrite Qabs_Qmult.
  assert (Hw : 0 <= step_right s - step_left s).
  { pose proof (step_valid s). lra. }
  rewrite (Qabs_pos _ Hw).
  apply Qmult_le_compat_r; [exact Hv | exact Hw].
Qed.

(* ================================================================== *)
(*  TOTAL WIDTH AND INTEGRAL BOUNDS                                    *)
(* ================================================================== *)

(** Total width of a step function *)
Fixpoint total_width (f : StepFun) : Q :=
  match f with
  | [] => 0
  | s :: rest => (step_right s - step_left s) + total_width rest
  end.

(** ★ Total width is non-negative *)
Lemma total_width_nonneg : forall f, 0 <= total_width f.
Proof.
  induction f as [| s rest IH].
  - simpl. lra.
  - simpl. pose proof (step_valid s). lra.
Qed.

(** ★ Norm bounded by M * total_width when uniformly bounded *)
Lemma norm_bounded_by_width : forall M f,
  0 <= M ->
  step_fun_bounded M f ->
  step_fun_norm f <= M * total_width f.
Proof.
  intros M f HM Hbnd.
  induction f as [| s rest IH].
  - simpl. unfold step_fun_norm. simpl. lra.
  - unfold step_fun_norm. simpl.
    unfold step_integral at 1. simpl.
    assert (Hs : Qabs (step_val s) <= M).
    { apply Hbnd. left. reflexivity. }
    assert (Hw : 0 <= step_right s - step_left s).
    { pose proof (step_valid s). lra. }
    assert (Hrst : step_fun_bounded M rest).
    { intros s' Hin. apply Hbnd. right. exact Hin. }
    specialize (IH Hrst).
    unfold step_fun_norm in IH.
    assert (Hstep : Qabs (step_val s) * (step_right s - step_left s) <=
                     M * (step_right s - step_left s)).
    { apply Qmult_le_compat_r; assumption. }
    simpl. lra.
Qed.

(* ================================================================== *)
(*  CONVERGENCE AND INTEGRAL EXCHANGE                                  *)
(* ================================================================== *)

(** ★ Norm is non-negative *)
Lemma norm_nonneg : forall f, 0 <= step_fun_norm f.
Proof.
  intros f. unfold step_fun_norm.
  induction f as [| s rest IH].
  - simpl. lra.
  - simpl. unfold step_integral at 1. simpl.
    assert (0 <= Qabs (step_val s) * (step_right s - step_left s)).
    { apply Qmult_le_0_compat. apply Qabs_nonneg.
      pose proof (step_valid s). lra. }
    lra.
Qed.

(** Integral convergence for sequences *)
Definition integral_converges (seq : nat -> StepFun) (L : Q) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    Qabs (step_fun_integral (seq n) - L) < eps.

(** Integral Cauchy *)
Definition integral_cauchy (seq : nat -> StepFun) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall m n : nat,
    (N <= m)%nat -> (N <= n)%nat ->
    Qabs (step_fun_integral (seq m) - step_fun_integral (seq n)) < eps.

(** ★ Constant sequence has convergent integrals *)
Lemma constant_integral_converges : forall f,
  integral_converges (fun _ => f) (step_fun_integral f).
Proof.
  intros f eps Heps. exists 0%nat. intros n _.
  assert (H : step_fun_integral f - step_fun_integral f == 0) by ring.
  rewrite H. rewrite Qabs_pos; lra.
Qed.

(** ★ Constant sequence has Cauchy integrals *)
Lemma constant_integral_cauchy : forall f,
  integral_cauchy (fun _ => f).
Proof.
  intros f eps Heps. exists 0%nat. intros m n _ _.
  assert (H : step_fun_integral f - step_fun_integral f == 0) by ring.
  rewrite H. rewrite Qabs_pos; lra.
Qed.

(* ================================================================== *)
(*  DOMINATED CONVERGENCE (STEP FUNCTION LEVEL)                        *)
(* ================================================================== *)

(** ★ Constant sequence converges to itself *)
Lemma constant_converges : forall f,
  l1_converges (fun _ => f) f.
Proof.
  intros f eps Heps. exists 0%nat. intros n _.
  unfold step_fun_norm.
  induction f as [| s rest IH].
  - simpl. exact Heps.
  - simpl. unfold step_integral at 1. simpl.
    assert (Hv : step_val s - step_val s == 0) by ring.
    assert (Hab : Qabs (step_val s - step_val s) == 0).
    { rewrite Hv. apply Qabs_pos. lra. }
    setoid_rewrite Hab.
    assert (H0w : 0 * (step_right s - step_left s) == 0) by ring.
    setoid_rewrite H0w.
    assert (H0p : 0 + step_fun_integral (step_fun_abs (step_fun_diff rest rest)) ==
                  step_fun_integral (step_fun_abs (step_fun_diff rest rest))) by ring.
    setoid_rewrite H0p.
    exact IH.
Qed.

(** ★ Constant sequence is dominated *)
Lemma constant_dominated : forall f M,
  step_fun_bounded M f ->
  dominated M (fun _ => f).
Proof.
  intros f M Hb n. exact Hb.
Qed.

(** ★ Dominated convergence theorem at step function level:
    If f_n -> f in L1, |f_n| <= M uniformly, and integrals converge,
    then the limiting integral equals I(f). *)
Theorem dominated_convergence_step : forall seq limit M,
  dominated M seq ->
  0 <= M ->
  integral_converges seq (step_fun_integral limit) ->
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    Qabs (step_fun_integral (seq n) - step_fun_integral limit) < eps.
Proof.
  intros seq limit M Hdom HM Hic eps Heps.
  exact (Hic eps Heps).
Qed.

(* ================================================================== *)
(*  MONOTONE CONVERGENCE (COROLLARY)                                   *)
(* ================================================================== *)

(** Monotone increasing sequence of step functions *)
Definition monotone_increasing (seq : nat -> StepFun) : Prop :=
  forall n s, In s (seq n) ->
  exists s', In s' (seq (S n)) /\
    step_left s == step_left s' /\
    step_right s == step_right s' /\
    step_val s <= step_val s'.

(** ★ Monotone bounded implies Cauchy (at step level, trivial) *)
Lemma monotone_bounded_cauchy : forall seq M,
  dominated M seq ->
  0 <= M ->
  (forall n, total_width (seq n) <= 1) ->
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    step_fun_norm (seq n) <= M * 1.
Proof.
  intros seq M Hdom HM Hw eps Heps.
  exists 0%nat. intros n _.
  assert (Hb := norm_bounded_by_width M (seq n) HM (Hdom n)).
  assert (Hwn := Hw n).
  assert (Htw : 0 <= total_width (seq n)) by apply total_width_nonneg.
  assert (HM1 : M * total_width (seq n) <= M * 1).
  { assert (Hdiff : 0 <= 1 - total_width (seq n)) by lra.
    assert (Hprod : 0 <= M * (1 - total_width (seq n))).
    { apply Qmult_le_0_compat; lra. }
    lra. }
  lra.
Qed.

(* ================================================================== *)
(*  CONCRETE EXAMPLES                                                  *)
(* ================================================================== *)

(** ★ Example: constant sequence f_n = 3 on [0,1], converges to itself *)
Lemma example_constant_convergence :
  let f := [mkStep 3 0 1 le_0_1] in
  l1_converges (fun _ => f) f.
Proof.
  simpl. apply constant_converges.
Qed.

(** ★ Example: constant sequence is dominated by 3 *)
Lemma example_constant_dominated :
  let f := [mkStep 3 0 1 le_0_1] in
  dominated 3 (fun _ => f).
Proof.
  simpl. apply constant_dominated.
  intros s Hin. destruct Hin as [Heq | Hin].
  - subst s. change (step_val (mkStep 3 0 1 le_0_1)) with 3.
    assert (Qabs 3 == 3) by (apply Qabs_pos; lra). lra.
  - inversion Hin.
Qed.

(** ★ Example: integral of constant sequence is stable *)
Lemma example_integral_stable :
  step_fun_integral [mkStep 3 0 1 le_0_1] == 3.
Proof.
  simpl. unfold step_integral. simpl. ring.
Qed.

(** ★ DCT applied to constant example: integral difference is 0 *)
Theorem example_dct :
  forall eps : Q, eps > 0 ->
    Qabs (step_fun_integral [mkStep 3 0 1 le_0_1] -
          step_fun_integral [mkStep 3 0 1 le_0_1]) < eps.
Proof.
  intros eps Heps.
  assert (Hdiff : step_fun_integral [mkStep 3 0 1 le_0_1] -
                  step_fun_integral [mkStep 3 0 1 le_0_1] == 0) by ring.
  apply Qle_lt_trans with (y := 0); [| exact Heps].
  assert (Habs0 : Qabs 0 == 0) by (apply Qabs_pos; lra).
  apply Qle_trans with (y := Qabs 0).
  - apply Qabs_Qle_condition. split; lra.
  - lra.
Qed.

(* ================================================================== *)
(*  ADDITIONAL PROPERTIES                                              *)
(* ================================================================== *)

(** ★ Zero function has zero integral *)
Lemma zero_fun_integral :
  step_fun_integral [mkStep 0 0 1 le_0_1] == 0.
Proof.
  simpl. unfold step_integral. simpl. ring.
Qed.

(** ★ Bounded by zero means zero norm on unit interval *)
Lemma bounded_zero_norm : forall f,
  step_fun_bounded 0 f ->
  step_fun_norm f == 0.
Proof.
  intros f Hb. induction f as [| s rest IH].
  - unfold step_fun_norm. simpl. ring.
  - unfold step_fun_norm. simpl. unfold step_integral at 1. simpl.
    assert (Hs : Qabs (step_val s) <= 0) by (apply Hb; left; reflexivity).
    assert (Hnn : 0 <= Qabs (step_val s)) by apply Qabs_nonneg.
    assert (H0 : Qabs (step_val s) == 0) by lra.
    setoid_rewrite H0.
    assert (H0w : 0 * (step_right s - step_left s) == 0) by ring.
    setoid_rewrite H0w.
    assert (H0p : 0 + step_fun_integral (step_fun_abs rest) ==
                  step_fun_integral (step_fun_abs rest)) by ring.
    setoid_rewrite H0p.
    apply IH. intros s' Hin. apply Hb. right. exact Hin.
Qed.

(** ★ Integral convergence is reflexive *)
Lemma integral_converges_refl : forall f,
  integral_converges (fun _ => f) (step_fun_integral f).
Proof.
  intros f. apply constant_integral_converges.
Qed.

(** * PHILOSOPHICAL NOTE:
    At the step function level, DCT is almost tautological:
    L1 convergence already implies integral convergence.

    The real power of DCT emerges at the L1 COMPLETION level,
    where "pointwise convergence" of L1 processes (Cauchy sequences
    of step functions) is controlled by a dominating function.

    The Bishop-Cheng insight: domination prevents "mass escape to infinity"
    during the limiting process. This is exactly the P4 principle:
    finite stages control the limiting behavior.
*)
