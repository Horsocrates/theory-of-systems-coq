(* ProcessModule.v — Modules of processes *)
From Stdlib Require Import QArith QArith_base Lia PeanoNat.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
Open Scope Q_scope.

(** Process-valued vector: n components, each a RealProcess *)
Definition ProcessVec (n : nat) := nat -> RealProcess.

Definition pvec_zero (n : nat) : ProcessVec n :=
  fun _ => process_zero.

Definition pvec_add {n} (v w : ProcessVec n) : ProcessVec n :=
  fun i => process_add (v i) (w i).

Definition pvec_scale (c : RealProcess) {n} (v : ProcessVec n) : ProcessVec n :=
  fun i => process_mul c (v i).

Definition pvec_neg {n} (v : ProcessVec n) : ProcessVec n :=
  fun i => process_neg (v i).

(** Module axioms *)
Lemma pvec_add_comm : forall n (v w : ProcessVec n) i K,
  pvec_add v w i K == pvec_add w v i K.
Proof. intros. unfold pvec_add. apply process_add_comm. Qed.

Lemma pvec_add_assoc : forall n (v w u : ProcessVec n) i K,
  pvec_add (pvec_add v w) u i K == pvec_add v (pvec_add w u) i K.
Proof. intros. unfold pvec_add. apply process_add_assoc. Qed.

Lemma pvec_add_zero : forall n (v : ProcessVec n) i K,
  pvec_add v (pvec_zero n) i K == v i K.
Proof. intros. unfold pvec_add, pvec_zero. apply process_add_zero_r. Qed.

Lemma pvec_scale_one : forall n (v : ProcessVec n) i K,
  pvec_scale process_one v i K == v i K.
Proof. intros. unfold pvec_scale. apply process_mul_one_l. Qed.

Lemma pvec_scale_distrib : forall n c (v w : ProcessVec n) i K,
  pvec_scale c (pvec_add v w) i K ==
  process_add (pvec_scale c v i) (pvec_scale c w i) K.
Proof. intros. unfold pvec_scale, pvec_add. apply process_distrib_l. Qed.

Lemma pvec_scale_zero : forall n (v : ProcessVec n) i K,
  pvec_scale process_zero v i K == 0.
Proof. intros. unfold pvec_scale. apply process_mul_zero_l. Qed.

(** Inner product at resolution K *)
Fixpoint pvec_inner_aux {n} (v w : ProcessVec n) (K : nat) (k : nat) : Q :=
  match k with
  | O => v 0%nat K * w 0%nat K
  | S k' => pvec_inner_aux v w K k' + v k K * w k K
  end.

Definition pvec_inner_at {n} (v w : ProcessVec n) (dim : nat) (K : nat) : Q :=
  match dim with
  | O => 0
  | S d => pvec_inner_aux v w K d
  end.

(** Norm²: ⟨v,v⟩ ≥ 0 for 1D *)
Lemma q_square_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intros q. destruct (Qlt_le_dec q 0).
  - assert (Hle : 0 <= -q) by lra.
    assert (Heq : q * q == (-q) * (-q)) by ring.
    rewrite Heq. apply Qmult_le_0_compat; exact Hle.
  - apply Qmult_le_0_compat; exact q0.
Qed.

Lemma pvec_inner_1d_nonneg : forall (v : ProcessVec 1) K,
  0 <= v 0%nat K * v 0%nat K.
Proof. intros. apply q_square_nonneg. Qed.

(** Process-valued matrix *)
Definition ProcessMat (n m : nat) := nat -> nat -> RealProcess.

Definition pmat_zero (n m : nat) : ProcessMat n m :=
  fun _ _ => process_zero.

Definition pmat_id (n : nat) : ProcessMat n n :=
  fun i j => if Nat.eqb i j then process_one else process_zero.

Lemma pmat_id_diag : forall n i K,
  pmat_id n i i K == 1.
Proof.
  intros. unfold pmat_id. rewrite Nat.eqb_refl.
  unfold process_one, const_process. reflexivity.
Qed.

Lemma pmat_id_offdiag : forall n i j K,
  (i <> j)%nat -> pmat_id n i j K == 0.
Proof.
  intros n i j K Hne. unfold pmat_id.
  rewrite <- Nat.eqb_neq in Hne. rewrite Hne.
  unfold process_zero, const_process. reflexivity.
Qed.

Theorem process_module_axioms :
  forall n (v w : ProcessVec n) i K,
  pvec_add v w i K == pvec_add w v i K /\
  pvec_add v (pvec_zero n) i K == v i K /\
  pvec_scale process_one v i K == v i K.
Proof.
  intros. split; [|split].
  - apply pvec_add_comm.
  - apply pvec_add_zero.
  - apply pvec_scale_one.
Qed.

Definition process_module_count := 14%nat.
