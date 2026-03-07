(** * Hessian.v — Second-Order Derivatives and Optimization

    Theory of Systems — Verified Standard Library (Tier 2b)

    Elements: function f, derivative f', second derivative f'', step size α
    Roles:    derivative → Direction, second derivative → Curvature,
              step → Update, Hessian matrix → MultiCurvature
    Rules:    positive second derivative (constitution for minimum),
              positive definiteness (constitution for multi-dim minimum)
    Status:   minimum | saddle_point | maximum

    Connection: Differentiation.v (has_derivative — same definition redefined locally)
    Connection: TaylorSeries.v (convexity, second derivative test)
    Connection: FixedPoint.v (contraction mapping for Newton convergence)
    Connection: LinearAlgebra.v (QVec, QMat, dot_product)

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Close Scope Z_scope.
Open Scope Q_scope.

(* ========================================================================= *)
(* HELPER TACTIC                                                              *)
(* ========================================================================= *)

(** Rewrite Qabs under Qeq (local copy from CauchyReal.v to avoid dep chain) *)
Ltac qabs_rw H :=
  let Habs := fresh "Habs" in
  assert (Habs := Qabs_wd _ _ H); rewrite Habs; clear Habs.

(* ========================================================================= *)
(* SECTION 1: LOCAL DERIVATIVE DEFINITION                                     *)
(* ========================================================================= *)

(** Division-free derivative: |f(x+h) - f(x) - L*h| < eps * |h|.
    This is identical to Differentiation.v's has_derivative, redefined
    locally to avoid importing the heavy CauchyReal → RealField chain. *)
Definition has_deriv (f : Q -> Q) (x L : Q) : Prop :=
  forall eps : Q, 0 < eps ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x - L * h) < eps * Qabs h.

(** Second derivative: f has derivative f'(x) at x, and f' has derivative L2 at x. *)
Definition has_second_deriv (f f' : Q -> Q) (x L2 : Q) : Prop :=
  has_deriv f x (f' x) /\ has_deriv f' x L2.

(** Strongly convex derivative: f' is mu-monotone on [a,b].
    This captures strong convexity via the gradient characterization:
    (f'(y) - f'(x)) * (y - x) >= mu * (y - x)^2. *)
Definition is_strongly_convex_deriv (f' : Q -> Q) (a b mu : Q) : Prop :=
  0 < mu /\
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
    mu * (y - x) * (y - x) <= (f' y - f' x) * (y - x).

(** Newton's method step: x_{n+1} = x_n - f'(x_n) / f''(x_n). *)
Definition newton_step (f' f'' : Q -> Q) (x : Q) : Q :=
  x - f' x / f'' x.

(** Positive definite 2x2 matrix [[a,b],[c,d]]:
    Sylvester criterion: a > 0 and det > 0. *)
Definition pd_2x2 (a b c d : Q) : Prop :=
  0 < a /\ 0 < a * d - b * c.

(** Critical point: f'(x) = 0. *)
Definition is_critical_point (f' : Q -> Q) (x : Q) : Prop :=
  f' x == 0.

(** Second derivative test classification. *)
Inductive critical_type : Set :=
  | LocalMin
  | LocalMax
  | Inconclusive.

Definition classify_critical (L2 : Q) : critical_type :=
  if Qlt_le_dec 0 L2 then LocalMin
  else if Qlt_le_dec L2 0 then LocalMax
  else Inconclusive.

(* ========================================================================= *)
(* SECTION 2: BASIC DERIVATIVE PROPERTIES (5 Qed)                            *)
(* ========================================================================= *)

(** L1: Derivative of constant function is 0. *)
Lemma has_deriv_const : forall (c x : Q), has_deriv (fun _ => c) x 0.
Proof.
  intros c x eps Heps.
  exists 1. split; [lra |].
  intros h Hh_pos Hh_lt.
  assert (Heq : c - c - 0 * h == 0) by ring.
  qabs_rw Heq. rewrite Qabs_pos; [| lra].
  apply Qmult_lt_0_compat; lra.
Qed.

(** L2: Derivative of identity function is 1. *)
Lemma has_deriv_id : forall (x : Q), has_deriv (fun t => t) x 1.
Proof.
  intros x eps Heps.
  exists 1. split; [lra |].
  intros h Hh_pos Hh_lt.
  assert (Heq : (x + h) - x - 1 * h == 0) by ring.
  qabs_rw Heq. rewrite Qabs_pos; [| lra].
  apply Qmult_lt_0_compat; lra.
Qed.

(** L3: Derivative of negation. *)
Lemma has_deriv_neg : forall (f : Q -> Q) (x L : Q),
  has_deriv f x L -> has_deriv (fun t => - f t) x (- L).
Proof.
  intros f x L Hf eps Heps.
  destruct (Hf eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  assert (Heq : - f (x + h) - - f x - - L * h ==
                 - (f (x + h) - f x - L * h)) by ring.
  qabs_rw Heq. rewrite Qabs_opp. exact (Hbound h Hh_pos Hh_lt).
Qed.

(** L4: Derivative of sum. *)
Lemma has_deriv_sum : forall (f g : Q -> Q) (x Lf Lg : Q),
  has_deriv f x Lf -> has_deriv g x Lg ->
  has_deriv (fun t => f t + g t) x (Lf + Lg).
Proof.
  intros f g x Lf Lg Hf Hg eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hf (eps * (1#2)) Heps2) as [df [Hdf Hbf]].
  destruct (Hg (eps * (1#2)) Heps2) as [dg [Hdg Hbg]].
  exists (Qmin df dg). split.
  - destruct (Q.min_spec df dg) as [[_ ->] | [_ ->]]; lra.
  - intros h Hh_pos Hh_lt.
    assert (Hh_df : Qabs h < df).
    { assert (Hmin := Q.le_min_l df dg). lra. }
    assert (Hh_dg : Qabs h < dg).
    { assert (Hmin := Q.le_min_r df dg). lra. }
    assert (Heq : (f (x + h) + g (x + h)) - (f x + g x) - (Lf + Lg) * h ==
                   (f (x + h) - f x - Lf * h) + (g (x + h) - g x - Lg * h)) by ring.
    qabs_rw Heq.
    assert (Htri := Qabs_triangle (f (x + h) - f x - Lf * h)
                                   (g (x + h) - g x - Lg * h)).
    specialize (Hbf h Hh_pos Hh_df).
    specialize (Hbg h Hh_pos Hh_dg).
    lra.
Qed.

(** L5: Derivative of x^2 is 2*x. *)
Lemma has_deriv_square : forall (x : Q),
  has_deriv (fun w => w * w) x (2 * x).
Proof.
  intros x eps Heps.
  exists eps. split; [exact Heps |].
  intros h Hh_pos Hh_lt.
  assert (Heq : (x + h) * (x + h) - x * x - 2 * x * h == h * h) by ring.
  qabs_rw Heq.
  rewrite Qabs_Qmult.
  apply Qmult_lt_compat_r; [exact Hh_pos | exact Hh_lt].
Qed.

(* ========================================================================= *)
(* SECTION 3: SECOND DERIVATIVE AND CONVEXITY (5 Qed)                        *)
(* ========================================================================= *)

(** L6: Extracting the second derivative from has_second_deriv. *)
Lemma second_deriv_is_deriv_of_first :
  forall (f f' : Q -> Q) (x L2 : Q),
  has_second_deriv f f' x L2 -> has_deriv f' x L2.
Proof.
  intros f f' x L2 [_ H]. exact H.
Qed.

(** L7: Constructing second_deriv from two derivative facts. *)
Lemma second_deriv_from_parts :
  forall (f f' : Q -> Q) (x L2 : Q),
  has_deriv f x (f' x) -> has_deriv f' x L2 ->
  has_second_deriv f f' x L2.
Proof.
  intros f f' x L2 H1 H2. unfold has_second_deriv. split; assumption.
Qed.

(** L8: Critical point has small function variation.
    At a critical point (f'(x) = 0), f(x+h) - f(x) is o(h). *)
Lemma critical_point_small_variation :
  forall (f : Q -> Q) (x : Q),
  has_deriv f x 0 ->
  forall eps, 0 < eps ->
    exists delta, 0 < delta /\
    forall h, 0 < Qabs h -> Qabs h < delta ->
      Qabs (f (x + h) - f x) < eps * Qabs h.
Proof.
  intros f x Hf eps Heps.
  destruct (Hf eps Heps) as [delta [Hdelta Hbound]].
  exists delta. split; [exact Hdelta |].
  intros h Hh_pos Hh_lt.
  specialize (Hbound h Hh_pos Hh_lt).
  (* Hbound : Qabs (f (x+h) - f x - 0*h) < eps * Qabs h *)
  (* Goal : Qabs (f (x+h) - f x) < eps * Qabs h *)
  assert (Heq : f (x + h) - f x == f (x + h) - f x - 0 * h) by ring.
  qabs_rw Heq. exact Hbound.
Qed.

(** L9: Strong convexity implies positive parameter. *)
Lemma strongly_convex_positive_mu :
  forall (f' : Q -> Q) (a b mu : Q),
  is_strongly_convex_deriv f' a b mu -> 0 < mu.
Proof.
  intros f' a b mu [Hmu _]. exact Hmu.
Qed.

(** L10: Strongly convex derivative implies monotonicity of f'.
    If f' is mu-monotone and x < y, then f'(x) < f'(y). *)
Lemma strongly_convex_monotone :
  forall (f' : Q -> Q) (a b mu : Q),
  is_strongly_convex_deriv f' a b mu ->
  forall x y, a <= x -> x <= b -> a <= y -> y <= b ->
    x < y -> f' x < f' y.
Proof.
  intros f' a b mu [Hmu Hsc] x y Hax Hxb Hay Hyb Hxy.
  specialize (Hsc x y Hax Hxb Hay Hyb).
  (* We have: mu * (y - x) * (y - x) <= (f' y - f' x) * (y - x) *)
  (* Since y - x > 0, we can divide both sides *)
  assert (Hpos : 0 < y - x) by lra.
  assert (Hpos2 : 0 < (y - x) * (y - x)).
  { apply Qmult_lt_0_compat; lra. }
  (* mu * (y-x)^2 > 0 *)
  assert (Hmupos : 0 < mu * (y - x) * (y - x)).
  { apply Qmult_lt_0_compat; [| lra].
    apply Qmult_lt_0_compat; lra. }
  (* So (f' y - f' x) * (y - x) > 0 *)
  assert (Hdiff_pos : 0 < (f' y - f' x) * (y - x)) by lra.
  (* Since y - x > 0, we need f' y - f' x > 0 *)
  destruct (Qlt_le_dec 0 (f' y - f' x)) as [H | H].
  - lra.
  - (* If f' y - f' x <= 0, then (f'y - f'x)*(y-x) <= 0, contradiction *)
    exfalso.
    assert (Hle : 0 <= (f' x - f' y) * (y - x)).
    { apply Qmult_le_0_compat; lra. }
    assert (Hrew : (f' x - f' y) * (y - x) == - ((f' y - f' x) * (y - x))) by ring.
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: NEWTON'S METHOD (5 Qed)                                        *)
(* ========================================================================= *)

(** L11: Newton step unfolding. *)
Lemma newton_step_eq :
  forall (f' f'' : Q -> Q) (x : Q),
  newton_step f' f'' x == x - f' x / f'' x.
Proof.
  intros. unfold newton_step. reflexivity.
Qed.

(** L12: Newton step at a root of f' is a fixed point.
    If f'(x_star) = 0, then N(x_star) = x_star. *)
Lemma newton_fixed_point :
  forall (f' f'' : Q -> Q) (xstar : Q),
  f' xstar == 0 -> ~ f'' xstar == 0 ->
  newton_step f' f'' xstar == xstar.
Proof.
  intros f' f'' xstar Hfp Hfpp.
  unfold newton_step.
  assert (Hq : f' xstar / f'' xstar == 0).
  { rewrite Hfp. unfold Qdiv. ring. }
  lra.
Qed.

(** L13: Newton step is well-defined when f'' is nonzero. *)
Lemma newton_step_well_defined :
  forall (f' f'' : Q -> Q) (x : Q),
  ~ f'' x == 0 ->
  exists y, y == newton_step f' f'' x.
Proof.
  intros f' f'' x Hne.
  exists (newton_step f' f'' x). reflexivity.
Qed.

(** L14: Newton step moves left when f' > 0 and f'' > 0.
    Under these conditions, the correction f'/f'' > 0, so x_{n+1} < x_n. *)
Lemma newton_step_decreases :
  forall (f' f'' : Q -> Q) (x : Q),
  0 < f' x -> 0 < f'' x ->
  newton_step f' f'' x < x.
Proof.
  intros f' f'' x Hfp Hfpp.
  unfold newton_step.
  assert (Hq : 0 < f' x / f'' x).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - exact Hfp.
    - apply Qinv_lt_0_compat. exact Hfpp. }
  lra.
Qed.

(** L15: Newton step moves right when f' < 0 and f'' > 0. *)
Lemma newton_step_increases :
  forall (f' f'' : Q -> Q) (x : Q),
  f' x < 0 -> 0 < f'' x ->
  x < newton_step f' f'' x.
Proof.
  intros f' f'' x Hfp Hfpp.
  unfold newton_step.
  assert (Hq : f' x / f'' x < 0).
  { unfold Qdiv.
    assert (H0 : 0 < / f'' x) by (apply Qinv_lt_0_compat; exact Hfpp).
    assert (H1 : f' x * / f'' x < 0 * / f'' x).
    { apply Qmult_lt_compat_r; [exact H0 | exact Hfp]. }
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: POSITIVE DEFINITE 2x2 MATRICES (5 Qed)                        *)
(* ========================================================================= *)

(** L16: Positive definite matrix has positive leading entry. *)
Lemma pd_2x2_positive_diag :
  forall (a b c d : Q), pd_2x2 a b c d -> 0 < a.
Proof.
  intros a b c d [Ha _]. exact Ha.
Qed.

(** L17: Positive definite matrix has positive determinant. *)
Lemma pd_2x2_positive_det :
  forall (a b c d : Q), pd_2x2 a b c d -> 0 < a * d - b * c.
Proof.
  intros a b c d [_ Hdet]. exact Hdet.
Qed.

(** L18: Diagonal matrix with positive entries is positive definite. *)
Lemma pd_diagonal :
  forall (a d : Q), 0 < a -> 0 < d -> pd_2x2 a 0 0 d.
Proof.
  intros a d Ha Hd.
  unfold pd_2x2. split.
  - exact Ha.
  - assert (Heq : a * d - 0 * 0 == a * d) by ring.
    rewrite Heq. apply Qmult_lt_0_compat; assumption.
Qed.

(** L19: Positive definite matrix with positive d has positive trace. *)
Lemma pd_2x2_trace_positive :
  forall (a b c d : Q), pd_2x2 a b c d -> 0 < d -> 0 < a + d.
Proof.
  intros a b c d [Ha _] Hd. lra.
Qed.

(** L20: The 2x2 identity matrix is positive definite. *)
Lemma pd_identity : pd_2x2 1 0 0 1.
Proof.
  unfold pd_2x2. split; [lra |].
  assert (Heq : 1 * 1 - 0 * 0 == 1) by ring.
  rewrite Heq. lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: CLASSIFICATION AND CONNECTIONS (2 Qed)                         *)
(* ========================================================================= *)

(** L21: Classification of critical points by second derivative.
    If L2 > 0, the classifier returns LocalMin. *)
Lemma classify_critical_min :
  forall (L2 : Q), 0 < L2 -> classify_critical L2 = LocalMin.
Proof.
  intros L2 HL2. unfold classify_critical.
  destruct (Qlt_le_dec 0 L2) as [H | H].
  - reflexivity.
  - lra.
Qed.

(** L22: If L2 < 0, the classifier returns LocalMax. *)
Lemma classify_critical_max :
  forall (L2 : Q), L2 < 0 -> classify_critical L2 = LocalMax.
Proof.
  intros L2 HL2. unfold classify_critical.
  destruct (Qlt_le_dec 0 L2) as [H | H].
  - lra.
  - destruct (Qlt_le_dec L2 0) as [H2 | H2].
    + reflexivity.
    + lra.
Qed.
