(* ProcessOperatorF.v — Linear operators on process space *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessSpace.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Linear Operator on Processes                                *)
(* ================================================================== *)

Definition ProcessOp := RealProcess -> RealProcess.

Definition is_linear_add (A : ProcessOp) : Prop :=
  forall f g K, A (process_add f g) K == process_add (A f) (A g) K.

Definition is_linear_scale (A : ProcessOp) : Prop :=
  forall c f K, A (fun n => c * f n) K == c * (A f K).

Definition is_linear (A : ProcessOp) : Prop :=
  is_linear_add A /\ is_linear_scale A.

(* ================================================================== *)
(*  Part II: Eigenvalue Problem                                         *)
(* ================================================================== *)

Definition is_eigenprocess (A : ProcessOp) (f : RealProcess) (lambda : Q) : Prop :=
  forall K, A f K == lambda * f K.

Definition has_discrete_spectrum (A : ProcessOp) : Prop :=
  exists (lambdas : nat -> Q) (eigenvecs : nat -> RealProcess),
  forall n, is_eigenprocess A (eigenvecs n) (lambdas n).

(** Diagonal operator: D(f)(K) = d(K) * f(K) *)
Definition diagonal_op (d : RealProcess) : ProcessOp :=
  fun f => fun K => d K * f K.

Lemma diagonal_is_linear_add : forall d,
  is_linear_add (diagonal_op d).
Proof. intros d f g K. unfold diagonal_op, process_add. ring. Qed.

Lemma diagonal_is_linear_scale : forall d,
  is_linear_scale (diagonal_op d).
Proof. intros d c f K. unfold diagonal_op. ring. Qed.

Lemma diagonal_is_linear : forall d, is_linear (diagonal_op d).
Proof. intros. split; [apply diagonal_is_linear_add | apply diagonal_is_linear_scale]. Qed.

Lemma diagonal_eigenprocess : forall d n,
  is_eigenprocess (diagonal_op d)
    (fun k => if Nat.eqb k n then 1 else 0) (d n).
Proof.
  intros d n K. unfold diagonal_op.
  destruct (Nat.eqb K n) eqn:E.
  - apply Nat.eqb_eq in E. subst. ring.
  - ring.
Qed.

Lemma diagonal_has_spectrum : forall d,
  has_discrete_spectrum (diagonal_op d).
Proof.
  intros d. exists d. exists (fun n k => if Nat.eqb k n then 1 else 0).
  intros n. exact (diagonal_eigenprocess d n).
Qed.

(* ================================================================== *)
(*  Part III: Inner Product and Self-Adjointness                        *)
(* ================================================================== *)

Fixpoint process_inner_aux (f g : RealProcess) (n : nat) : Q :=
  match n with
  | O => f 0%nat * g 0%nat
  | S n' => process_inner_aux f g n' + f n * g n
  end.

Definition process_inner (f g : RealProcess) (N : nat) : Q :=
  process_inner_aux f g N.

Lemma inner_self_nonneg_0 : forall f, 0 <= process_inner f f 0.
Proof.
  intros f. unfold process_inner, process_inner_aux.
  destruct (Qlt_le_dec (f 0%nat) 0).
  - assert (H : 0 <= -(f 0%nat)) by lra.
    assert (Heq : f 0%nat * f 0%nat == (-(f 0%nat)) * (-(f 0%nat))) by ring.
    rewrite Heq. apply Qmult_le_0_compat; exact H.
  - apply Qmult_le_0_compat; exact q.
Qed.

Definition is_self_adjoint (A : ProcessOp) (N : nat) : Prop :=
  forall f g, process_inner (A f) g N == process_inner f (A g) N.

Lemma diagonal_self_adjoint_0 : forall d,
  is_self_adjoint (diagonal_op d) 0.
Proof.
  intros d f g. unfold process_inner, process_inner_aux, diagonal_op. ring.
Qed.

Lemma diagonal_self_adjoint_1 : forall d,
  is_self_adjoint (diagonal_op d) 1.
Proof.
  intros d f g. unfold process_inner, process_inner_aux, diagonal_op. ring.
Qed.

(** Self-adjoint over Q -> eigenvalues already real (trivial!) *)
Theorem self_adjoint_real_eigenvalues :
  forall A N lambda f,
  is_self_adjoint A N -> is_eigenprocess A f lambda ->
  exists (num : Z) (den : BinNums.positive), lambda = num # den.
Proof. intros. destruct lambda as [num den]. exists num, den. reflexivity. Qed.

(** Zero operator *)
Definition zero_op : ProcessOp := fun _ => const_process 0.

Lemma zero_op_linear : is_linear zero_op.
Proof.
  split.
  - intros f g K. unfold zero_op, const_process, process_add. ring.
  - intros c f K. unfold zero_op, const_process. ring.
Qed.

(** Identity operator *)
Definition id_op : ProcessOp := fun f => f.

Lemma id_op_linear : is_linear id_op.
Proof.
  split.
  - intros f g K. unfold id_op, process_add. reflexivity.
  - intros c f K. unfold id_op. reflexivity.
Qed.

Lemma id_eigenprocess : forall f, is_eigenprocess id_op f 1.
Proof. intros f K. unfold id_op. ring. Qed.

Theorem process_operator_foundation :
  is_linear (diagonal_op (const_process 1)) /\
  has_discrete_spectrum (diagonal_op (const_process 1)) /\
  is_linear zero_op /\ is_linear id_op.
Proof.
  split; [|split; [|split]].
  - apply diagonal_is_linear.
  - apply diagonal_has_spectrum.
  - exact zero_op_linear.
  - exact id_op_linear.
Qed.

Definition process_op_count := 18%nat.
