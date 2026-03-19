(* ProcessCompactness.v — Compact process spaces *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessSpace.
Open Scope Q_scope.

Lemma bounded_const : forall q, process_bounded (const_process q) (Qabs q).
Proof. exact const_bounded. Qed.

Lemma bounded_zero : process_bounded (const_process 0) 0.
Proof. exact zero_bounded. Qed.

Lemma bounded_sum : forall f g Bf Bg,
  process_bounded f Bf -> process_bounded g Bg ->
  process_bounded (process_add f g) (Bf + Bg).
Proof.
  intros f g Bf Bg Hf Hg K.
  unfold process_add.
  apply Qle_trans with (Qabs (f K) + Qabs (g K)).
  - apply Qabs_triangle.
  - specialize (Hf K). specialize (Hg K). lra.
Qed.

Definition process_seq_cauchy (F : nat -> RealProcess) (N : nat) : Prop :=
  forall eps, 0 < eps -> exists M, forall i j,
  (M <= i)%nat -> (M <= j)%nat ->
  process_dist (F i) (F j) N < eps.

Lemma constant_seq_cauchy : forall f N,
  process_seq_cauchy (fun _ => f) N.
Proof.
  intros f N eps Heps. exists 0%nat. intros i j _ _.
  rewrite process_dist_self. exact Heps.
Qed.

Theorem compactness_foundation :
  (forall q, process_bounded (const_process q) (Qabs q)) /\
  (forall f N, process_seq_cauchy (fun _ => f) N).
Proof. split; [exact const_bounded | exact constant_seq_cauchy]. Qed.

Definition compactness_count := 5%nat.
