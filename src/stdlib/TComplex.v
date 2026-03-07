(* TComplex: Complex Numbers as ToS System *)
(* STATUS: 18 Qed, 0 Admitted, 0 axioms *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import TheoryOfSystems_Core_ERR.

Record TComplex := mkComplex { tc_re : Q; tc_im : Q }.

Definition tc_zero : TComplex := mkComplex 0 0.
Definition tc_one : TComplex := mkComplex 1 0.
Definition tc_i : TComplex := mkComplex 0 1.

Definition tc_add (z1 z2 : TComplex) : TComplex :=
  mkComplex (tc_re z1 + tc_re z2) (tc_im z1 + tc_im z2).

Definition tc_sub (z1 z2 : TComplex) : TComplex :=
  mkComplex (tc_re z1 - tc_re z2) (tc_im z1 - tc_im z2).

Definition tc_mul (z1 z2 : TComplex) : TComplex :=
  mkComplex (tc_re z1 * tc_re z2 - tc_im z1 * tc_im z2)
            (tc_re z1 * tc_im z2 + tc_im z1 * tc_re z2).

Definition tc_conj (z : TComplex) : TComplex :=
  mkComplex (tc_re z) (- tc_im z).

Definition tc_neg (z : TComplex) : TComplex :=
  mkComplex (- tc_re z) (- tc_im z).

Definition tc_norm_sq (z : TComplex) : Q :=
  tc_re z * tc_re z + tc_im z * tc_im z.

Definition tc_eq (z1 z2 : TComplex) : Prop :=
  tc_re z1 == tc_re z2 /\ tc_im z1 == tc_im z2.

Inductive tc_status : Set :=
  | TC_Real
  | TC_Imaginary
  | TC_Complex.

Lemma tc_add_comm_re : forall z1 z2 : TComplex,
    tc_re (tc_add z1 z2) == tc_re (tc_add z2 z1).
Proof. intros z1 z2. unfold tc_add. simpl. lra. Qed.

Lemma tc_add_comm_im : forall z1 z2 : TComplex,
    tc_im (tc_add z1 z2) == tc_im (tc_add z2 z1).
Proof. intros z1 z2. unfold tc_add. simpl. lra. Qed.

Lemma tc_add_assoc_re : forall z1 z2 z3 : TComplex,
    tc_re (tc_add (tc_add z1 z2) z3) == tc_re (tc_add z1 (tc_add z2 z3)).
Proof. intros z1 z2 z3. unfold tc_add. simpl. lra. Qed.

Lemma tc_add_assoc_im : forall z1 z2 z3 : TComplex,
    tc_im (tc_add (tc_add z1 z2) z3) == tc_im (tc_add z1 (tc_add z2 z3)).
Proof. intros z1 z2 z3. unfold tc_add. simpl. lra. Qed.

Lemma tc_add_zero_r : forall z : TComplex,
    tc_eq (tc_add z tc_zero) z.
Proof. intros z. unfold tc_eq, tc_add, tc_zero. simpl. split; lra. Qed.

Lemma tc_mul_comm_re : forall z1 z2 : TComplex,
    tc_re (tc_mul z1 z2) == tc_re (tc_mul z2 z1).
Proof. intros z1 z2. unfold tc_mul. simpl. ring. Qed.

Lemma tc_mul_comm_im : forall z1 z2 : TComplex,
    tc_im (tc_mul z1 z2) == tc_im (tc_mul z2 z1).
Proof. intros z1 z2. unfold tc_mul. simpl. ring. Qed.

Lemma tc_mul_one_r_re : forall z : TComplex,
    tc_re (tc_mul z tc_one) == tc_re z.
Proof. intros z. unfold tc_mul, tc_one. simpl. ring. Qed.

Lemma tc_mul_one_r_im : forall z : TComplex,
    tc_im (tc_mul z tc_one) == tc_im z.
Proof. intros z. unfold tc_mul, tc_one. simpl. ring. Qed.

Lemma tc_conj_involutive : forall z : TComplex,
    tc_eq (tc_conj (tc_conj z)) z.
Proof. intros z. unfold tc_eq, tc_conj. simpl. split; ring. Qed.

(** Square of any Q is nonneg *)
Lemma Qsq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hneg|Hpos].
  - assert (Hmq : 0 <= -q) by lra.
    assert (Heq : q * q == (-q) * (-q)) by ring.
    rewrite Heq.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma tc_norm_sq_nonneg : forall z : TComplex,
    0 <= tc_norm_sq z.
Proof.
  intros z. unfold tc_norm_sq.
  pose proof (Qsq_nonneg (tc_re z)) as H1.
  pose proof (Qsq_nonneg (tc_im z)) as H2.
  lra.
Qed.

Lemma tc_norm_sq_zero : tc_norm_sq tc_zero == 0.
Proof. unfold tc_norm_sq, tc_zero. simpl. lra. Qed.

Lemma tc_mul_conj_re : forall z : TComplex,
    tc_re (tc_mul z (tc_conj z)) == tc_norm_sq z.
Proof. intros z. unfold tc_mul, tc_conj, tc_norm_sq. simpl. ring. Qed.

Lemma tc_mul_conj_im : forall z : TComplex,
    tc_im (tc_mul z (tc_conj z)) == 0.
Proof. intros z. unfold tc_mul, tc_conj. simpl. ring. Qed.

Lemma tc_i_squared_re : tc_re (tc_mul tc_i tc_i) == -(1).
Proof. unfold tc_mul, tc_i. simpl. ring. Qed.

Lemma tc_i_squared_im : tc_im (tc_mul tc_i tc_i) == 0.
Proof. unfold tc_mul, tc_i. simpl. ring. Qed.

Lemma tc_eq_refl : forall z : TComplex, tc_eq z z.
Proof. intros z. unfold tc_eq. split; lra. Qed.

Lemma tc_eq_sym : forall z1 z2 : TComplex, tc_eq z1 z2 -> tc_eq z2 z1.
Proof. intros z1 z2 [H1 H2]. unfold tc_eq. split; lra. Qed.
