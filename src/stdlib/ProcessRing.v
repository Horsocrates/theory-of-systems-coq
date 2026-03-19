(* ProcessRing.v — Algebraic structure on RealProcess *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Pointwise Operations                                       *)
(* ================================================================== *)

Definition process_add (f g : RealProcess) : RealProcess :=
  fun K => f K + g K.

Definition process_mul (f g : RealProcess) : RealProcess :=
  fun K => f K * g K.

Definition process_neg (f : RealProcess) : RealProcess :=
  fun K => - (f K).

Definition process_zero : RealProcess := const_process 0.
Definition process_one : RealProcess := const_process 1.

Definition process_sub (f g : RealProcess) : RealProcess :=
  process_add f (process_neg g).

Definition process_scale (c : Q) (f : RealProcess) : RealProcess :=
  fun K => c * f K.

(* ================================================================== *)
(*  Part II: Ring Axioms                                                *)
(* ================================================================== *)

Lemma process_add_comm : forall f g K,
  process_add f g K == process_add g f K.
Proof. intros. unfold process_add. ring. Qed.

Lemma process_add_assoc : forall f g h K,
  process_add (process_add f g) h K ==
  process_add f (process_add g h) K.
Proof. intros. unfold process_add. ring. Qed.

Lemma process_add_zero_l : forall f K,
  process_add process_zero f K == f K.
Proof. intros. unfold process_add, process_zero, const_process. ring. Qed.

Lemma process_add_zero_r : forall f K,
  process_add f process_zero K == f K.
Proof. intros. unfold process_add, process_zero, const_process. ring. Qed.

Lemma process_add_neg : forall f K,
  process_add f (process_neg f) K == 0.
Proof. intros. unfold process_add, process_neg. ring. Qed.

Lemma process_mul_comm : forall f g K,
  process_mul f g K == process_mul g f K.
Proof. intros. unfold process_mul. ring. Qed.

Lemma process_mul_assoc : forall f g h K,
  process_mul (process_mul f g) h K ==
  process_mul f (process_mul g h) K.
Proof. intros. unfold process_mul. ring. Qed.

Lemma process_mul_one_l : forall f K,
  process_mul process_one f K == f K.
Proof. intros. unfold process_mul, process_one, const_process. ring. Qed.

Lemma process_mul_one_r : forall f K,
  process_mul f process_one K == f K.
Proof. intros. unfold process_mul, process_one, const_process. ring. Qed.

Lemma process_distrib_l : forall f g h K,
  process_mul f (process_add g h) K ==
  process_add (process_mul f g) (process_mul f h) K.
Proof. intros. unfold process_mul, process_add. ring. Qed.

Lemma process_distrib_r : forall f g h K,
  process_mul (process_add f g) h K ==
  process_add (process_mul f h) (process_mul g h) K.
Proof. intros. unfold process_mul, process_add. ring. Qed.

Lemma process_mul_zero_l : forall f K,
  process_mul process_zero f K == 0.
Proof. intros. unfold process_mul, process_zero, const_process. ring. Qed.

Lemma process_neg_neg : forall f K,
  process_neg (process_neg f) K == f K.
Proof. intros. unfold process_neg. ring. Qed.

Lemma process_scale_distrib : forall c f g K,
  process_scale c (process_add f g) K ==
  process_add (process_scale c f) (process_scale c g) K.
Proof. intros. unfold process_scale, process_add. ring. Qed.

Lemma process_scale_assoc : forall c d f K,
  process_scale c (process_scale d f) K ==
  process_scale (c * d) f K.
Proof. intros. unfold process_scale. ring. Qed.

Lemma process_scale_one : forall f K,
  process_scale 1 f K == f K.
Proof. intros. unfold process_scale. ring. Qed.

(** ★ Summary: RealProcess is a commutative ring *)
Theorem process_is_comm_ring :
  forall f g K,
  process_add f g K == process_add g f K /\
  process_mul f g K == process_mul g f K /\
  process_add f process_zero K == f K /\
  process_mul f process_one K == f K.
Proof.
  intros f g K. split; [|split; [|split]].
  - apply process_add_comm.
  - apply process_mul_comm.
  - apply process_add_zero_r.
  - apply process_mul_one_r.
Qed.

(** Concrete: const embeds Q into ProcessRing *)
Lemma const_add : forall p q K,
  process_add (const_process p) (const_process q) K == p + q.
Proof. intros. unfold process_add, const_process. ring. Qed.

Lemma const_mul : forall p q K,
  process_mul (const_process p) (const_process q) K == p * q.
Proof. intros. unfold process_mul, const_process. ring. Qed.

Definition process_ring_count := 22%nat.
