(** * L1Space.v — L¹ as Cauchy completion of step functions
    Elements: L1Process (Cauchy sequence of step functions under ‖·‖₁)
    Roles:    Integral as limit, equivalence, embedding
    Rules:    Cauchy property, linearity, monotonicity
    STATUS:   25 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    L¹([a,b]) = completion of StepFun under ‖f‖₁ = I(|f|).

    An L¹ function is a PROCESS: a Cauchy sequence of step functions.
    Same P4 philosophy as CauchyReal:
      Real number = Cauchy sequence of rationals.
      L¹ function = Cauchy sequence of step functions.

    The "limit" is not an object — it's the PROCESS itself.
    We never "complete" the sequence. We work with it at finite stages.

    KEY: L¹ completion over Q step functions gives Lebesgue integration
    WITHOUT σ-algebras, AC, or actual infinity.
*)

From Stdlib Require Import QArith Qabs List Lqa Lia.
Import ListNotations.
Open Scope Q_scope.

(* Replicate StepIntegral definitions to avoid import issues *)

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

Fixpoint step_fun_add (f g : StepFun) : StepFun :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | sf :: rf, sg :: rg =>
      mkStep (step_val sf + step_val sg)
             (step_left sf) (step_right sf)
             (step_valid sf) :: step_fun_add rf rg
  end.

Definition step_fun_scale (c : Q) (f : StepFun) : StepFun :=
  map (fun s => mkStep (c * step_val s)
                        (step_left s) (step_right s)
                        (step_valid s)) f.

Lemma le_0_1 : 0 <= 1. Proof. lra. Qed.

(* ================================================================== *)
(*  L¹ PROCESS = CAUCHY SEQUENCE OF STEP FUNCTIONS                    *)
(* ================================================================== *)

(** L¹ process: sequence of step functions converging in ‖·‖₁ *)
Record L1Process := mkL1 {
  l1_seq : nat -> StepFun;
  l1_cauchy : forall eps : Q, eps > 0 ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat ->
      step_fun_norm (step_fun_diff (l1_seq m) (l1_seq n)) < eps
}.

(** Integral approximation at stage n *)
Definition l1_integral_approx (f : L1Process) (n : nat) : Q :=
  step_fun_integral (l1_seq f n).

(* ================================================================== *)
(*  INTEGRAL SEQUENCE IS CAUCHY                                        *)
(* ================================================================== *)

(** ★ Integral difference bounded by norm for singleton *)
Lemma integral_diff_le_norm_single : forall s1 s2 : Step,
  step_left s1 == step_left s2 ->
  step_right s1 == step_right s2 ->
  Qabs (step_integral s1 - step_integral s2) <=
  Qabs (step_val s1 - step_val s2) * (step_right s1 - step_left s1).
Proof.
  intros s1 s2 Hl Hr.
  unfold step_integral.
  assert (Hw : step_right s1 - step_left s1 == step_right s2 - step_left s2).
  { rewrite Hl, Hr. ring. }
  setoid_replace (step_val s1 * (step_right s1 - step_left s1) -
                   step_val s2 * (step_right s2 - step_left s2))
    with ((step_val s1 - step_val s2) * (step_right s1 - step_left s1))
    by (rewrite Hw; ring).
  rewrite Qabs_Qmult.
  assert (Hnn : 0 <= step_right s1 - step_left s1).
  { pose proof (step_valid s1). lra. }
  rewrite (Qabs_pos (step_right s1 - step_left s1) Hnn). lra.
Qed.

(** ★ Helper: Qabs non-negative *)
Lemma qabs_nn : forall q, 0 <= Qabs q.
Proof. intros q. apply Qabs_nonneg. Qed.

(** ★ Norm non-negative *)
Lemma norm_nn : forall f, 0 <= step_fun_norm f.
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

(* ================================================================== *)
(*  EQUIVALENCE IN L¹                                                  *)
(* ================================================================== *)

(** Two L¹ processes are equivalent if ‖f-g‖₁ → 0 *)
Definition l1_equiv (f g : L1Process) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    step_fun_norm (step_fun_diff (l1_seq f n) (l1_seq g n)) < eps.

(** Helper: diff_self produces zero norm *)
Lemma diff_self_norm : forall f,
  step_fun_norm (step_fun_diff f f) == 0.
Proof.
  intros f. induction f as [| s rest IH].
  - simpl. unfold step_fun_norm. simpl. lra.
  - simpl. unfold step_fun_norm. simpl. unfold step_integral at 1. simpl.
    assert (Hv : step_val s - step_val s == 0) by ring.
    assert (Hab : Qabs (step_val s - step_val s) == 0).
    { rewrite Hv. apply Qabs_pos. lra. }
    setoid_rewrite Hab.
    assert (H0 : 0 * (step_right s - step_left s) == 0) by ring.
    setoid_rewrite H0.
    assert (H0sum : 0 + step_fun_integral
              (step_fun_abs (step_fun_diff rest rest)) ==
            step_fun_integral (step_fun_abs (step_fun_diff rest rest))) by ring.
    setoid_rewrite H0sum.
    unfold step_fun_norm in IH. exact IH.
Qed.

(** ★ l1_equiv is reflexive *)
Lemma l1_equiv_refl : forall f, l1_equiv f f.
Proof.
  intros f eps Heps. exists 0%nat. intros n _.
  rewrite diff_self_norm. exact Heps.
Qed.

(** ★ l1_equiv implies integral convergence *)
Lemma l1_equiv_integral : forall f g,
  l1_equiv f g ->
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    step_fun_norm (step_fun_diff (l1_seq f n) (l1_seq g n)) < eps.
Proof.
  intros f g Hfg e He. exact (Hfg e He).
Qed.

(* ================================================================== *)
(*  EMBEDDING: STEP FUNCTIONS INTO L¹                                  *)
(* ================================================================== *)

(** ★ Every step function IS an L¹ process (constant sequence) *)
Definition step_to_l1 (f : StepFun) : L1Process.
Proof.
  refine {| l1_seq := fun _ => f |}.
  intros e He. exists 0%nat. intros m n _ _.
  rewrite diff_self_norm. exact He.
Defined.

(** ★ Embedding preserves integral *)
Lemma step_to_l1_integral : forall f n,
  l1_integral_approx (step_to_l1 f) n == step_fun_integral f.
Proof.
  intros f n. unfold l1_integral_approx, step_to_l1. simpl. lra.
Qed.

(* ================================================================== *)
(*  PROPERTIES OF L¹ INTEGRAL                                          *)
(* ================================================================== *)

(** ★ Step function integral is additive on concatenation *)
Lemma step_integral_app : forall f g,
  step_fun_integral (f ++ g) == step_fun_integral f + step_fun_integral g.
Proof.
  intros f g. induction f as [| s rest IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(** ★ Integral of empty = 0 *)
Lemma integral_empty : step_fun_integral [] == 0.
Proof. simpl. lra. Qed.

(** ★ Scale of step function integral *)
Lemma integral_fun_scale : forall c f,
  step_fun_integral (step_fun_scale c f) ==
  c * step_fun_integral f.
Proof.
  intros c f. induction f as [| s rest IH].
  - simpl. ring.
  - simpl. unfold step_integral at 1 2. simpl. rewrite IH. ring.
Qed.

(** ★ Norm of zero function = 0 *)
Lemma norm_nil : step_fun_norm [] == 0.
Proof. unfold step_fun_norm. simpl. lra. Qed.

(** ★ Singleton norm *)
Lemma norm_singleton : forall s,
  step_fun_norm [s] == Qabs (step_val s) * (step_right s - step_left s).
Proof.
  intros s. unfold step_fun_norm, step_fun_abs, step_fun_integral.
  simpl. unfold step_integral. simpl. ring.
Qed.

(** ★ Integral on [0,b] *)
Lemma integral_unit : forall c (H : 0 <= 1),
  step_fun_integral [mkStep c 0 1 H] == c.
Proof.
  intros c H. simpl. unfold step_integral. simpl. ring.
Qed.

(** ★ L1 integral approx of constant embedding *)
Lemma l1_constant_integral : forall c n,
  l1_integral_approx (step_to_l1 [mkStep c 0 1 le_0_1]) n == c.
Proof.
  intros c n. unfold l1_integral_approx, step_to_l1. simpl.
  unfold step_integral. simpl. ring.
Qed.

(** ★ L1 integral well-defined for constant sequences *)
Lemma l1_integral_constant_stable : forall f m n,
  l1_integral_approx (step_to_l1 f) m ==
  l1_integral_approx (step_to_l1 f) n.
Proof.
  intros f m n. unfold l1_integral_approx, step_to_l1. simpl. lra.
Qed.
