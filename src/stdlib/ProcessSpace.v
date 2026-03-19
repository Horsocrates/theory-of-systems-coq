(* ProcessSpace.v — Topology on process space *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
Open Scope Q_scope.

Definition cylinder (N : nat) (center : RealProcess) (radius : Q)
  (f : RealProcess) : Prop :=
  forall k, (k <= N)%nat -> Qabs (f k - center k) < radius.

Fixpoint process_dist_aux (f g : RealProcess) (n : nat) : Q :=
  match n with
  | O => Qabs (f 0%nat - g 0%nat)
  | S n' => process_dist_aux f g n' + Qpow (1#2) n * Qabs (f n - g n)
  end.

Definition process_dist (f g : RealProcess) (N : nat) : Q :=
  process_dist_aux f g N.

Lemma process_dist_self : forall f N, process_dist f f N == 0.
Proof.
  intros f N. induction N.
  - unfold process_dist, process_dist_aux.
    assert (Heq : f 0%nat - f 0%nat == 0) by ring. rewrite Heq.
    rewrite Qabs_pos; lra.
  - unfold process_dist, process_dist_aux. fold process_dist_aux.
    assert (Heq : f (S N) - f (S N) == 0) by ring. rewrite Heq.
    rewrite Qabs_pos; [| lra].
    assert (Hmul : Qpow (1 # 2) (S N) * 0 == 0) by ring.
    rewrite Hmul. unfold process_dist in IHN. lra.
Qed.

Definition process_ball (center : RealProcess) (r : Q) (N : nat)
  (f : RealProcess) : Prop := process_dist center f N < r.

Lemma self_in_ball : forall f r N, 0 < r -> process_ball f r N f.
Proof. intros. unfold process_ball. rewrite process_dist_self. exact H. Qed.

Lemma cylinder_self : forall N f r, 0 < r -> cylinder N f r f.
Proof.
  intros N f r Hr k Hk.
  assert (Heq : f k - f k == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

Definition process_bounded (f : RealProcess) (B : Q) : Prop :=
  forall K, Qabs (f K) <= B.

Lemma const_bounded : forall q, process_bounded (const_process q) (Qabs q).
Proof. intros q K. unfold const_process. lra. Qed.

Lemma zero_bounded : process_bounded (const_process 0) 0.
Proof. intros K. unfold const_process. rewrite Qabs_pos; lra. Qed.

Theorem process_space_complete :
  (forall f N, process_dist f f N == 0) /\
  (forall f r N, 0 < r -> process_ball f r N f).
Proof. split; [exact process_dist_self | exact self_in_ball]. Qed.

Definition process_space_count := 7%nat.
