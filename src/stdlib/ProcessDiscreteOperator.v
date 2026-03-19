(* ProcessDiscreteOperator.v — Finite difference operators *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessOperatorF.
Open Scope Q_scope.

Definition forward_diff : ProcessOp := fun f => fun K => f (S K) - f K.

Definition backward_diff : ProcessOp :=
  fun f => fun K => match K with 0%nat => f 0%nat | S k => f (S k) - f k end.

Definition second_diff : ProcessOp := fun f => forward_diff (forward_diff f).

Lemma second_diff_formula : forall f K,
  second_diff f K == f (S (S K)) - 2 * f (S K) + f K.
Proof. intros f K. unfold second_diff, forward_diff. ring. Qed.

Lemma forward_diff_const : forall c K,
  forward_diff (const_process c) K == 0.
Proof. intros. unfold forward_diff, const_process. ring. Qed.

Lemma forward_diff_linear : forall K,
  forward_diff (fun n => inject_Z (Z.of_nat n)) K == 1.
Proof.
  intros K. unfold forward_diff.
  rewrite Nat2Z.inj_succ. unfold inject_Z. unfold Qeq; simpl; lia.
Qed.

Lemma forward_diff_add : forall f g K,
  forward_diff (process_add f g) K ==
  process_add (forward_diff f) (forward_diff g) K.
Proof. intros. unfold forward_diff, process_add. ring. Qed.

Lemma forward_diff_scale : forall c f K,
  forward_diff (fun n => c * f n) K == c * forward_diff f K.
Proof. intros. unfold forward_diff. ring. Qed.

Lemma forward_diff_is_linear : is_linear forward_diff.
Proof.
  split.
  - intros f g K. exact (forward_diff_add f g K).
  - intros c f K. exact (forward_diff_scale c f K).
Qed.

Lemma discrete_leibniz : forall f g K,
  forward_diff (process_mul f g) K ==
  f K * forward_diff g K + g (S K) * forward_diff f K.
Proof. intros. unfold forward_diff, process_mul. ring. Qed.

Definition discrete_schrodinger (V : RealProcess) : ProcessOp :=
  fun f => fun K => - second_diff f K + V K * f K.

Lemma schrodinger_free_particle : forall f K,
  discrete_schrodinger (const_process 0) f K ==
  -(f (S (S K)) - 2 * f (S K) + f K).
Proof. intros. unfold discrete_schrodinger, const_process. rewrite second_diff_formula. ring. Qed.

Theorem discrete_operator_foundation :
  is_linear forward_diff /\
  (forall c K, forward_diff (const_process c) K == 0) /\
  (forall f K, second_diff f K == f (S (S K)) - 2 * f (S K) + f K).
Proof.
  split; [|split].
  - exact forward_diff_is_linear.
  - exact forward_diff_const.
  - exact second_diff_formula.
Qed.

Definition discrete_op_count := 12%nat.
