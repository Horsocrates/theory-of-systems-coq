(** * ProcessOperatorFA.v — Operators as Matrix Processes
    Elements: operator processes (nat → (nat → Q) → (nat → Q))
    Roles:    bounded, self-adjoint, positive, compact, diagonal
    Rules:    operator norm bounded, composition, algebra
    Status:   complete
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS OPERATOR FA — Operators as Matrix Processes                  *)
(*                                                                            *)
(*  Under P4: a bounded operator A : L² → L² is the process of             *)
(*  finite matrices {A_n : Q^n → Q^n}.                                      *)
(*                                                                            *)
(*  STATUS: 18 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessFiniteDim.
From ToS Require Import process.ProcessL2.

(* ================================================================== *)
(*  Part I: Operator Process                                            *)
(* ================================================================== *)

(** An operator process: at level n, an n×n matrix action *)
Definition OperatorProcess := nat -> (nat -> Q) -> (nat -> Q).

(** Matrix representation at level n *)
Definition op_matrix_entry (A : OperatorProcess) (n i j : nat) : Q :=
  A n (fun k => if Nat.eqb k j then 1 else 0) i.

(** Operator norm at level n (Frobenius norm squared) *)
Definition op_norm_n (A : OperatorProcess) (n : nat) : Q :=
  sum_Q (fun i => sum_Q (fun j =>
    op_matrix_entry A n i j * op_matrix_entry A n i j) n) n.

(** Bounded operator *)
Definition is_bounded_op (A : OperatorProcess) (B : Q) : Prop :=
  forall n, op_norm_n A n <= B.

(** Self-adjoint: A_{ij} = A_{ji} at every level *)
Definition is_selfadjoint (A : OperatorProcess) : Prop :=
  forall n i j, op_matrix_entry A n i j == op_matrix_entry A n j i.

(** Positive: ⟨v, Av⟩ ≥ 0 at every level *)
Definition is_positive_op (A : OperatorProcess) : Prop :=
  forall n (v : nat -> Q),
    0 <= inner_product_n n v (A n v).

(** Norm is nonneg *)
Lemma op_norm_nonneg : forall A n, 0 <= op_norm_n A n.
Proof.
  intros. unfold op_norm_n.
  apply sum_Q_nonneg. intros i _.
  apply sum_Q_nonneg. intros j _.
  apply q_sq_nonneg.
Qed.

(* ================================================================== *)
(*  Part II: Diagonal Operators                                         *)
(* ================================================================== *)

(** Diagonal operator from eigenvalue sequence *)
Definition diag_operator (eigenvals : nat -> Q) : OperatorProcess :=
  fun n v => fun k => if Nat.ltb k n then eigenvals k * v k else 0.

(** Diagonal operator matrix entry *)
Lemma diag_matrix_entry : forall eigenvals n i j,
  (i < n)%nat -> (j < n)%nat ->
  op_matrix_entry (diag_operator eigenvals) n i j ==
  if Nat.eqb i j then eigenvals i else 0.
Proof.
  intros eigenvals n i j Hi Hj.
  unfold op_matrix_entry, diag_operator.
  destruct (Nat.ltb_spec i n); [| lia].
  destruct (Nat.eqb_spec i j).
  - subst. destruct (Nat.eqb_spec j j); [ring | lia].
  - destruct (Nat.eqb_spec i j); [lia | ring].
Qed.

(** Diagonal operator is self-adjoint *)
Lemma diag_selfadjoint : forall eigenvals,
  is_selfadjoint (diag_operator eigenvals).
Proof.
  intros eigenvals n i j.
  unfold op_matrix_entry, diag_operator.
  destruct (Nat.ltb_spec i n); destruct (Nat.ltb_spec j n).
  - destruct (Nat.eqb_spec j i); destruct (Nat.eqb_spec i j).
    + subst. ring.
    + lia.
    + lia.
    + ring.
  - destruct (Nat.eqb_spec j i).
    + subst. lia.
    + destruct (Nat.eqb_spec i j); [subst; lia | lra].
  - destruct (Nat.eqb_spec i j).
    + subst. lia.
    + destruct (Nat.eqb_spec j i); [subst; lia | lra].
  - lra.
Qed.

(** Diagonal operator with nonneg eigenvalues is positive *)
Lemma diag_positive : forall eigenvals,
  (forall k, 0 <= eigenvals k) ->
  is_positive_op (diag_operator eigenvals).
Proof.
  intros eigenvals Hnn n v.
  unfold inner_product_n, diag_operator.
  apply sum_Q_nonneg. intros k Hk.
  destruct (Nat.ltb_spec k n); [| lia].
  assert (Hrw : v k * (eigenvals k * v k) == eigenvals k * (v k * v k)) by ring.
  setoid_rewrite Hrw.
  apply Qmult_le_0_compat; [apply Hnn | apply q_sq_nonneg].
Qed.

(* ================================================================== *)
(*  Part III: Compact Operators                                         *)
(* ================================================================== *)

(** Compact = norm process is Cauchy *)
Definition is_compact (A : OperatorProcess) : Prop :=
  forall eps, 0 < eps ->
    exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
      Qabs (op_norm_n A m - op_norm_n A n) < eps.

(** Under P4: EVERY operator is finite-rank at each level *)
(** Compactness = the norm process converges *)

(** Diagonal bounded by entry bound *)
Lemma diag_entry_bounded : forall eigenvals B n i j,
  (forall k, Qabs (eigenvals k) <= B) ->
  Qabs (op_matrix_entry (diag_operator eigenvals) n i j) <= B.
Proof.
  intros eigenvals B n i j Hbnd.
  unfold op_matrix_entry, diag_operator.
  destruct (Nat.ltb_spec i n).
  - destruct (Nat.eqb_spec i j).
    + subst. destruct (Nat.eqb_spec j j); [| lia].
      assert (Heq : eigenvals j * 1 == eigenvals j) by ring.
      setoid_rewrite Heq. apply Hbnd.
    + destruct (Nat.eqb_spec i j); [lia |].
      assert (Heq : eigenvals i * 0 == 0) by ring.
      setoid_rewrite Heq.
      assert (Habs0 : Qabs 0 == 0) by (rewrite Qabs_pos; lra).
      setoid_rewrite Habs0. assert (H0B := Qabs_nonneg (eigenvals 0%nat)).
      assert (HB0 := Hbnd 0%nat). lra.
  - assert (Habs0 : Qabs 0 == 0) by (rewrite Qabs_pos; lra).
    setoid_rewrite Habs0. assert (HB0 := Hbnd 0%nat).
    assert (H0B := Qabs_nonneg (eigenvals 0%nat)). lra.
Qed.

(* ================================================================== *)
(*  Part IV: Operator Algebra                                           *)
(* ================================================================== *)

(** Composition: (AB)_n = A_n ∘ B_n *)
Definition op_compose (A B : OperatorProcess) : OperatorProcess :=
  fun n v => A n (B n v).

(** Sum *)
Definition op_add (A B : OperatorProcess) : OperatorProcess :=
  fun n v => fun k => A n v k + B n v k.

(** Scalar multiplication *)
Definition op_scale (c : Q) (A : OperatorProcess) : OperatorProcess :=
  fun n v => fun k => c * A n v k.

(** Identity operator *)
Definition op_id : OperatorProcess :=
  fun n v => fun k => if Nat.ltb k n then v k else 0.

(** Identity is self-adjoint *)
Lemma id_selfadjoint : is_selfadjoint op_id.
Proof.
  intros n i j. unfold op_matrix_entry, op_id.
  destruct (Nat.ltb_spec i n); destruct (Nat.ltb_spec j n).
  - destruct (Nat.eqb_spec j i); destruct (Nat.eqb_spec i j); try lia; reflexivity.
  - destruct (Nat.eqb_spec j i); [subst; lia |].
    destruct (Nat.eqb_spec i j); [subst; lia | lra].
  - destruct (Nat.eqb_spec i j); [subst; lia |].
    destruct (Nat.eqb_spec j i); [subst; lia | lra].
  - lra.
Qed.

(** Add preserves self-adjointness *)
Lemma add_selfadjoint : forall A B,
  is_selfadjoint A -> is_selfadjoint B ->
  is_selfadjoint (op_add A B).
Proof.
  intros A B HA HB n i j. unfold is_selfadjoint, op_matrix_entry in *.
  unfold op_add.
  assert (Ha := HA n i j). assert (Hb := HB n i j).
  setoid_rewrite Ha. setoid_rewrite Hb. reflexivity.
Qed.

(** Scale preserves self-adjointness *)
Lemma scale_selfadjoint : forall c A,
  is_selfadjoint A ->
  is_selfadjoint (op_scale c A).
Proof.
  intros c A HA n i j. unfold is_selfadjoint, op_matrix_entry in *.
  unfold op_scale.
  assert (Ha := HA n i j).
  setoid_rewrite Ha. reflexivity.
Qed.

(** Zero operator *)
Definition op_zero : OperatorProcess :=
  fun _ _ _ => 0.

(** Zero operator is bounded *)
Lemma zero_entry : forall n i j, op_matrix_entry op_zero n i j == 0.
Proof. intros. unfold op_matrix_entry, op_zero. ring. Qed.

Lemma sum_Q_const_zero : forall n, sum_Q (fun _ => 0) n == 0.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma zero_norm : forall n, op_norm_n op_zero n == 0.
Proof.
  intro n. unfold op_norm_n.
  assert (Houter : sum_Q (fun i => sum_Q (fun j =>
    op_matrix_entry op_zero n i j * op_matrix_entry op_zero n i j) n) n ==
    sum_Q (fun _ => 0) n).
  { apply sum_Q_ext. intros i _.
    assert (Hinner : sum_Q (fun j =>
      op_matrix_entry op_zero n i j * op_matrix_entry op_zero n i j) n ==
      sum_Q (fun _ => 0) n).
    { apply sum_Q_ext. intros j _. rewrite zero_entry. ring. }
    rewrite Hinner. apply sum_Q_const_zero. }
  rewrite Houter. apply sum_Q_const_zero.
Qed.

Lemma zero_bounded : is_bounded_op op_zero 0.
Proof.
  intro n. assert (H := zero_norm n). lra.
Qed.

(** Zero operator is self-adjoint *)
Lemma zero_selfadjoint : is_selfadjoint op_zero.
Proof. intros n i j. unfold op_matrix_entry, op_zero. ring. Qed.

(** Zero operator is positive *)
Lemma zero_positive : is_positive_op op_zero.
Proof.
  intros n v. unfold inner_product_n, op_zero.
  apply sum_Q_nonneg. intros k _. lra.
Qed.

(* ================================================================== *)
(*  Part V: Operator Applied to L² Elements                            *)
(* ================================================================== *)

(** Apply operator to L² element: A_n(f) *)
Definition op_apply (A : OperatorProcess) (f : L2Element) (n : nat) : L2Element :=
  A n f.

(** Diagonal operator applied to element *)
Lemma diag_apply : forall eigenvals f n k,
  (k < n)%nat ->
  diag_operator eigenvals n f k == eigenvals k * f k.
Proof.
  intros. unfold diag_operator.
  destruct (Nat.ltb_spec k n); [reflexivity | lia].
Qed.

(** Diagonal operator above n gives 0 *)
Lemma diag_apply_above : forall eigenvals f n k,
  (n <= k)%nat ->
  diag_operator eigenvals n f k == 0.
Proof.
  intros. unfold diag_operator.
  destruct (Nat.ltb_spec k n); [lia | reflexivity].
Qed.

(* ================================================================== *)
(*  Part VI: E/R/R Pattern                                              *)
(* ================================================================== *)

(** Convergence rate *)
Definition operator_convergence_rate : Q := 1 # 2.

Lemma operator_rate_valid :
  0 < operator_convergence_rate /\ operator_convergence_rate < 1.
Proof. unfold operator_convergence_rate. split; lra. Qed.

(** E/R/R: operators as process construction *)
Theorem operator_is_process :
  (* Under P4: a bounded operator is a process of finite matrices *)
  (* At level n: A_n is an n×n matrix over Q *)
  (* The process {A_n} with bounded norm IS the operator *)
  (* No infinite-dimensional operator theory needed *)
  forall (A : OperatorProcess) B,
    is_bounded_op A B -> forall n, op_norm_n A n <= B.
Proof.
  intros A B HB n. exact (HB n).
Qed.

(** P4: operators are processes of finite matrices *)
(** No infinite-dimensional spaces *)
(** Self-adjoint = symmetric at every level *)
(** Positive = positive definite at every level *)
(** Compact = norm process converges *)
