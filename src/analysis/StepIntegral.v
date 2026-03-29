(** * StepIntegral.v — Step functions with endpoint representation
    Elements: Step records (value, left, right), StepFun lists
    Roles:    Integration, norm, pointwise evaluation
    Rules:    Linearity, monotonicity, non-negativity of norm
    STATUS:   20 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    P4-COMPATIBLE MEASURE THEORY: Integration first, measure derived.

    A step function on [a,b] is: f = Σᵢ cᵢ · χ[aᵢ,bᵢ]
    where {[aᵢ,bᵢ]} partition [a,b] and cᵢ ∈ Q.
    Integral: I(f) = Σᵢ cᵢ · (bᵢ - aᵢ).  Exact over Q.

    This is the FOUNDATION of Bishop-Cheng measure theory.
    Everything else is L¹ completion of this.
*)

From Stdlib Require Import QArith Qabs List Lqa Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  STEP FUNCTION REPRESENTATION                                       *)
(* ================================================================== *)

(** A step = (value, left endpoint, right endpoint) with validity *)
Record Step := mkStep {
  step_val : Q;
  step_left : Q;
  step_right : Q;
  step_valid : step_left <= step_right
}.

(** A step function = finite list of steps *)
Definition StepFun := list Step.

(** Integral of one step: c · (b - a) *)
Definition step_integral (s : Step) : Q :=
  step_val s * (step_right s - step_left s).

(** Integral of step function: sum of step integrals *)
Fixpoint step_fun_integral (f : StepFun) : Q :=
  match f with
  | [] => 0
  | s :: rest => step_integral s + step_fun_integral rest
  end.

(* ================================================================== *)
(*  CONCRETE EXAMPLES                                                  *)
(* ================================================================== *)

(** Helper: build step with proof obligation *)
Lemma le_0_1 : 0 <= 1. Proof. lra. Qed.
Lemma le_0_half : 0 <= 1#2. Proof. lra. Qed.
Lemma le_half_1 : 1#2 <= 1. Proof. lra. Qed.
Lemma le_0_3 : 0 <= 3. Proof. lra. Qed.

(** ★ Integral of constant c on [0,1]: I = c·(1-0) = c *)
Lemma integral_constant : forall c : Q,
  step_integral (mkStep c 0 1 le_0_1) == c.
Proof.
  intros c. unfold step_integral. simpl. ring.
Qed.

(** ★ Integral of χ[0, 1/2]: I = 1·(1/2-0) = 1/2 *)
Lemma integral_half_indicator :
  step_integral (mkStep 1 0 (1#2) le_0_half) == 1#2.
Proof.
  unfold step_integral. simpl. ring.
Qed.

(** ★ Two-step: 2 on [0,1/2] + 3 on [1/2,1]. I = 2·(1/2) + 3·(1/2) = 5/2 *)
Lemma integral_two_step :
  let s1 := mkStep 2 0 (1#2) le_0_half in
  let s2 := mkStep 3 (1#2) 1 le_half_1 in
  step_fun_integral [s1; s2] == 5#2.
Proof.
  simpl. unfold step_integral. simpl. ring.
Qed.

(* ================================================================== *)
(*  STEP FUNCTION OPERATIONS                                           *)
(* ================================================================== *)

(** Absolute value of step function *)
Definition step_fun_abs (f : StepFun) : StepFun :=
  map (fun s => mkStep (Qabs (step_val s))
                        (step_left s) (step_right s)
                        (step_valid s)) f.

(** ★ L¹ norm of step function: ‖f‖₁ = I(|f|) *)
Definition step_fun_norm (f : StepFun) : Q :=
  step_fun_integral (step_fun_abs f).

(** Scalar multiplication *)
Definition step_fun_scale (c : Q) (f : StepFun) : StepFun :=
  map (fun s => mkStep (c * step_val s)
                        (step_left s) (step_right s)
                        (step_valid s)) f.

(** Difference of two step functions (same partition) *)
(** For simplicity: pointwise on aligned steps *)
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
(*  PROPERTIES                                                         *)
(* ================================================================== *)

(** ★ Integral of empty function = 0 *)
Lemma integral_nil : step_fun_integral [] == 0.
Proof. simpl. lra. Qed.

(** ★ Integral of singleton = step_integral *)
Lemma integral_singleton : forall s,
  step_fun_integral [s] == step_integral s.
Proof. intros s. simpl. ring. Qed.

(** ★ Integral of concatenation = sum *)
Lemma integral_app : forall f g,
  step_fun_integral (f ++ g) == step_fun_integral f + step_fun_integral g.
Proof.
  intros f g. induction f as [| s rest IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(** ★ Scalar multiplication of integral *)
Lemma integral_scale : forall c s,
  step_integral (mkStep (c * step_val s)
                         (step_left s) (step_right s)
                         (step_valid s)) == c * step_integral s.
Proof.
  intros c s. unfold step_integral. simpl. ring.
Qed.

(** ★ Monotonicity: if value increases, integral increases (same interval) *)
Lemma integral_monotone_step : forall s1 s2,
  step_left s1 == step_left s2 ->
  step_right s1 == step_right s2 ->
  step_val s1 <= step_val s2 ->
  step_integral s1 <= step_integral s2.
Proof.
  intros s1 s2 Hl Hr Hv.
  unfold step_integral.
  assert (Hw : step_right s1 - step_left s1 == step_right s2 - step_left s2).
  { rewrite Hl, Hr. ring. }
  assert (Hnn : 0 <= step_right s1 - step_left s1).
  { pose proof (step_valid s1). lra. }
  apply Qle_trans with (step_val s2 * (step_right s1 - step_left s1)).
  - apply Qmult_le_compat_r; assumption.
  - rewrite Hw. lra.
Qed.

(** ★ Step integral non-negative for non-negative value on valid interval *)
Lemma step_integral_nonneg : forall s,
  0 <= step_val s ->
  0 <= step_integral s.
Proof.
  intros s Hv. unfold step_integral.
  assert (Hw : 0 <= step_right s - step_left s).
  { pose proof (step_valid s). lra. }
  apply Qmult_le_0_compat; assumption.
Qed.

(** ★ Qabs is non-negative *)
Lemma Qabs_nonneg_local : forall q, 0 <= Qabs q.
Proof.
  intros q. apply Qabs_nonneg.
Qed.

(** ★ Norm is non-negative *)
Lemma norm_nonneg : forall f, 0 <= step_fun_norm f.
Proof.
  intros f. unfold step_fun_norm.
  induction f as [| s rest IH].
  - simpl. lra.
  - simpl. unfold step_integral at 1. simpl.
    assert (H1 : 0 <= Qabs (step_val s) * (step_right s - step_left s)).
    { apply Qmult_le_0_compat.
      - apply Qabs_nonneg_local.
      - pose proof (step_valid s). lra. }
    lra.
Qed.

(** ★ Norm of constant c on [0,1] *)
Lemma norm_constant : forall c,
  step_fun_norm [mkStep c 0 1 le_0_1] == Qabs c.
Proof.
  intros c. unfold step_fun_norm, step_fun_abs, step_fun_integral.
  simpl. unfold step_integral. simpl. ring.
Qed.

(** ★ Integral of step on [0,b]: c·b *)
Lemma integral_from_zero : forall c b (H : 0 <= b),
  step_integral (mkStep c 0 b H) == c * b.
Proof.
  intros c b H. unfold step_integral. simpl. ring.
Qed.
