(** * ControlTheory.v --- Linear Control Systems

    Theory of Systems --- Verified Standard Library (Batch 5)

    Elements: states (QVec n), inputs (QVec m), outputs (QVec p)
    Roles:    A -> Dynamics, B -> Control, C -> Observation, K -> Feedback
    Rules:    LTI equation (constitution), Lyapunov stability condition
    Status:   stable | unstable | controllable | observable

    Connection: FixedPoint.v --- stability = contraction to origin
    Connection: LinearAlgebra.v --- matrix operations
    Connection: ProcessGeneral.v --- evolution as GenProcess (P4)

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import LinearAlgebra.
From ToS Require Import ProcessGeneral.

Record ScalarLTI := mkScalarLTI {
  slti_a : Q;
  slti_b : Q;
}.

Fixpoint scalar_evolve (sys : ScalarLTI) (x0 : Q) (u : nat -> Q)
    (t : nat) : Q :=
  match t with
  | O => x0
  | S t' => slti_a sys * scalar_evolve sys x0 u t' + slti_b sys * u t'
  end.

Definition scalar_zero_input (sys : ScalarLTI) (x0 : Q) (t : nat) : Q :=
  scalar_evolve sys x0 (fun _ => 0) t.

Definition scalar_stable (sys : ScalarLTI) : Prop :=
  Qabs (slti_a sys) < 1.

Definition scalar_lyapunov_decrease (sys : ScalarLTI) : Prop :=
  forall x : Q, ~ (x == 0) ->
    (slti_a sys * x) * (slti_a sys * x) < x * x.

Lemma scalar_evolve_zero :
  forall sys x0 u, scalar_evolve sys x0 u 0 = x0.
Proof. reflexivity. Qed.

Lemma scalar_evolve_step :
  forall sys x0 u t,
    scalar_evolve sys x0 u (S t) =
    slti_a sys * scalar_evolve sys x0 u t + slti_b sys * u t.
Proof. reflexivity. Qed.

Lemma scalar_zero_input_0 :
  forall sys x0, scalar_zero_input sys x0 0 = x0.
Proof. reflexivity. Qed.

Lemma scalar_zero_input_step :
  forall sys x0 t,
    scalar_zero_input sys x0 (S t) ==
    slti_a sys * scalar_zero_input sys x0 t.
Proof.
  intros sys x0 t. unfold scalar_zero_input. simpl. ring.
Qed.

Lemma scalar_zero_input_1 :
  forall sys x0, scalar_zero_input sys x0 1 == slti_a sys * x0.
Proof.
  intros sys x0. unfold scalar_zero_input. simpl. ring.
Qed.

Lemma scalar_zero_input_2 :
  forall sys x0, scalar_zero_input sys x0 2 == slti_a sys * (slti_a sys * x0).
Proof.
  intros sys x0. unfold scalar_zero_input. simpl. ring.
Qed.

Lemma scalar_evolve_zero_input :
  forall sys x0 t,
    scalar_evolve sys x0 (fun _ => 0) t == scalar_zero_input sys x0 t.
Proof.
  intros sys x0 t. unfold scalar_zero_input. lra.
Qed.

Lemma scalar_zero_input_linear :
  forall sys c x0 t,
    scalar_zero_input sys (c * x0) t ==
    c * scalar_zero_input sys x0 t.
Proof.
  intros sys c x0 t. induction t as [| t' IH].
  - unfold scalar_zero_input. simpl. lra.
  - unfold scalar_zero_input in *. simpl.
    rewrite IH. ring.
Qed.

Lemma scalar_zero_input_additive :
  forall sys x0 y0 t,
    scalar_zero_input sys (x0 + y0) t ==
    scalar_zero_input sys x0 t + scalar_zero_input sys y0 t.
Proof.
  intros sys x0 y0 t. induction t as [| t' IH].
  - unfold scalar_zero_input. simpl. lra.
  - unfold scalar_zero_input in *. simpl.
    rewrite IH. ring.
Qed.

Lemma abs_lt_1_sq_lt_1 :
  forall a : Q, Qabs a < 1 -> a * a < 1.
Proof.
  intros a Ha.
  assert (Ha2 : -(1) < a < 1).
  { apply Qabs_Qlt_condition. exact Ha. }
  destruct Ha2 as [Hlo Hhi].
  (* Key: (1-a)*(1+a) > 0 and (1-a)*(1+a) == 1 - a*a *)
  assert (H1 : 0 < 1 - a) by lra.
  assert (H2 : 0 < 1 + a) by lra.
  assert (H3 : 0 < (1 - a) * (1 + a)).
  { apply Qmult_lt_0_compat; assumption. }
  assert (H4 : (1 - a) * (1 + a) == 1 - a * a) by ring.
  lra.
Qed.

Theorem scalar_stable_lyapunov :
  forall sys, scalar_stable sys -> scalar_lyapunov_decrease sys.
Proof.
  intros sys Hstab x Hx.
  unfold scalar_stable in Hstab.
  set (a := slti_a sys) in *.
  assert (Haa : a * a < 1) by (apply abs_lt_1_sq_lt_1; exact Hstab).
  assert (Hxx : 0 < x * x).
  { destruct (Qlt_le_dec 0 x) as [Hp | Hn].
    - apply Qmult_lt_0_compat; lra.
    - destruct (Qeq_dec x 0) as [Hz | Hnz].
      + exfalso. apply Hx. exact Hz.
      + assert (Hpp : x  < 0) by lra.
        assert (Hnx : 0 < -x) by lra.
        assert (Heq : x * x == (-x)*(-x)) by ring.
        rewrite Heq. apply Qmult_lt_0_compat; lra. }
  assert (Heq : a * x * (a * x) == a * a * (x * x)) by ring.
  rewrite Heq.
  assert (Hdiff : 0 < (1 - a * a) * (x * x)).
  { apply Qmult_lt_0_compat; lra. }
  lra.
Qed.

Lemma constant_input_evolve_1 :
  forall sys x0 c,
    scalar_evolve sys x0 (fun _ => c) 1 ==
    slti_a sys * x0 + slti_b sys * c.
Proof.
  intros sys x0 c. simpl. lra.
Qed.

Lemma constant_input_evolve_2 :
  forall sys x0 c,
    scalar_evolve sys x0 (fun _ => c) 2 ==
    slti_a sys * (slti_a sys * x0 + slti_b sys * c) + slti_b sys * c.
Proof.
  intros sys x0 c. simpl. lra.
Qed.

Definition sys_half : ScalarLTI := mkScalarLTI (1#2) 0.

Lemma scalar_half_stable : scalar_stable sys_half.
Proof.
  unfold scalar_stable, sys_half. simpl.
  unfold Qabs. simpl. lra.
Qed.

Lemma scalar_half_zero_input_1 :
  forall x0, scalar_zero_input sys_half x0 1 == (1#2) * x0.
Proof.
  intros x0. unfold scalar_zero_input, sys_half. simpl. ring.
Qed.

Lemma scalar_half_zero_input_2 :
  forall x0, scalar_zero_input sys_half x0 2 == (1#4) * x0.
Proof.
  intros x0. unfold scalar_zero_input, sys_half. simpl. ring.
Qed.

Record LTI (n m p : nat) := mkLTI {
  lti_A : QMat n n;
  lti_B : QMat n m;
  lti_C : QMat p n;
}.

Arguments mkLTI {n m p} _ _ _.
Arguments lti_A {n m p} _.
Arguments lti_B {n m p} _.
Arguments lti_C {n m p} _.

Fixpoint lti_evolve {n m p : nat} (sys : LTI n m p)
    (x0 : QVec n) (u : nat -> QVec m) (t : nat) : QVec n :=
  match t with
  | O => x0
  | S t' => qv_add (mat_vec_mul (lti_A sys) (lti_evolve sys x0 u t'))
                    (mat_vec_mul (lti_B sys) (u t'))
  end.

Definition lti_output {n m p : nat} (sys : LTI n m p)
    (x : QVec n) : QVec p :=
  mat_vec_mul (lti_C sys) x.

Definition lti_process {n m p : nat} (sys : LTI n m p)
    (x0 : QVec n) (u : nat -> QVec m) : GenProcess (QVec n) :=
  fun t => lti_evolve sys x0 u t.

Lemma lti_evolve_zero :
  forall {n m p} (sys : LTI n m p) x0 u,
    lti_evolve sys x0 u 0 = x0.
Proof. reflexivity. Qed.

Lemma lti_evolve_step :
  forall {n m p} (sys : LTI n m p) x0 u t,
    lti_evolve sys x0 u (S t) =
    qv_add (mat_vec_mul (lti_A sys) (lti_evolve sys x0 u t))
           (mat_vec_mul (lti_B sys) (u t)).
Proof. reflexivity. Qed.

Lemma lti_process_at :
  forall {n m p} (sys : LTI n m p) x0 u t,
    lti_process sys x0 u t = lti_evolve sys x0 u t.
Proof. reflexivity. Qed.

Definition scalar_process (sys : ScalarLTI) (x0 : Q)
    (u : nat -> Q) : GenProcess Q :=
  fun t => scalar_evolve sys x0 u t.

Lemma scalar_process_at :
  forall sys x0 u t,
    scalar_process sys x0 u t = scalar_evolve sys x0 u t.
Proof. reflexivity. Qed.

Lemma scalar_zero_process_init :
  forall sys x0,
    scalar_process sys x0 (fun _ => 0) 0%nat = x0.
Proof. reflexivity. Qed.
