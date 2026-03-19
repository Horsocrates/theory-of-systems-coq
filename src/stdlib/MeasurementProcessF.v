(* MeasurementProcessF.v — Measurement = projection *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import stdlib.ProcessBornRuleUnified.
Open Scope Q_scope.

Definition projection_onto (n : nat) : ProcessOp :=
  fun f => fun k => if Nat.eqb k n then f n else 0.

Lemma projection_idempotent_0 : forall f K,
  projection_onto 0 (projection_onto 0 f) K == projection_onto 0 f K.
Proof.
  intros f K. unfold projection_onto.
  destruct K; simpl; ring.
Qed.

Lemma projection_idempotent_1 : forall f K,
  projection_onto 1 (projection_onto 1 f) K == projection_onto 1 f K.
Proof.
  intros f K. unfold projection_onto.
  destruct K; [simpl; ring | destruct K; simpl; ring].
Qed.

Lemma projections_orthogonal_01 : forall f K,
  projection_onto 0 (projection_onto 1 f) K == 0.
Proof.
  intros f K. unfold projection_onto.
  destruct K; simpl; ring.
Qed.

Lemma projections_orthogonal_10 : forall f K,
  projection_onto 1 (projection_onto 0 f) K == 0.
Proof.
  intros f K. unfold projection_onto.
  destruct K; [simpl; ring | destruct K; simpl; ring].
Qed.

Lemma projection_linear_0 : is_linear_add (projection_onto 0).
Proof.
  intros f g K. unfold projection_onto, process_add.
  destruct K; simpl; ring.
Qed.

Lemma projection_eigenprocess_0 :
  is_eigenprocess (projection_onto 0)
    (fun k => if Nat.eqb k 0 then 1 else 0) 1.
Proof. intros K. unfold projection_onto. destruct K; simpl; ring. Qed.

Lemma projection_kills_0_on_1 :
  is_eigenprocess (projection_onto 0)
    (fun k => if Nat.eqb k 1 then 1 else 0) 0.
Proof. intros K. unfold projection_onto. destruct K; simpl; ring.
Qed.

Theorem measurement_foundation :
  (forall f K, projection_onto 0 (projection_onto 0 f) K == projection_onto 0 f K) /\
  (forall f K, projection_onto 0 (projection_onto 1 f) K == 0).
Proof.
  split.
  - exact projection_idempotent_0.
  - exact projections_orthogonal_01.
Qed.

Definition measurement_f_count := 8%nat.
