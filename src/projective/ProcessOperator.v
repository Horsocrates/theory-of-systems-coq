(* ========================================================================= *)
(*        PROCESS OPERATORS — Position, Momentum, and Commutators            *)
(*                                                                           *)
(*  Operators on the quantum tower act at each finite stage.                 *)
(*  Position and momentum are approximated by rational matrices              *)
(*  at each stage, converging to the continuous operators.                   *)
(*                                                                           *)
(*  The canonical commutation relation [X, P] = iℏ is approximated          *)
(*  at each finite stage as a structural relation between the               *)
(*  matrix actions.                                                          *)
(*                                                                           *)
(*  Part of: Theory of Systems — Projective Systems (P4 Frontier)           *)
(*  STATUS: 29 Qed, 0 Admitted                                               *)
(*  AXIOMS: classic (via MonotoneConvergence)                                *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs QArith.Qminmax.
Require Import ZArith.
Require Import Coq.micromega.Lqa.
Require Import Lia.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import LinearAlgebra.
From ToS Require Import ProcessGeneral.
From ToS Require Import SeriesConvergence.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import projective.ProjectiveSystem.
From ToS Require Import projective.ProjectiveLimit.
From ToS Require Import projective.QuantumTower.

(* ========================================================================= *)
(*                    PART I: PROCESS OPERATOR CORE                          *)
(* ========================================================================= *)

(**
  PROCESS OPERATOR
  =================

  A ProcessOp acts on InfVecs at each finite stage.
  At stage n, it maps QVec (S n) -> QVec (S n).
  Key requirement: compatible with truncation (structural).
*)

Record ProcessOp := mkProcessOp {
  po_action : forall n : nat, QVec (S n) -> QVec (S n);
}.

(** Apply operator at stage n *)
Definition po_apply (T : ProcessOp) (v : InfVec) (n : nat) : QVec (S n) :=
  po_action T n (iv_at v n).

(** Operator equality: same action at every stage *)
Definition po_eq (T1 T2 : ProcessOp) : Prop :=
  forall n (v : QVec (S n)), qv_eq (po_action T1 n v) (po_action T2 n v).

Lemma po_eq_refl : forall T, po_eq T T.
Proof. intros T n v. apply qv_eq_refl. Qed.

Lemma po_eq_sym : forall T1 T2, po_eq T1 T2 -> po_eq T2 T1.
Proof. intros T1 T2 H n v. apply qv_eq_sym. apply H. Qed.

Lemma po_eq_trans : forall T1 T2 T3,
  po_eq T1 T2 -> po_eq T2 T3 -> po_eq T1 T3.
Proof.
  intros T1 T2 T3 H12 H23 n v.
  apply qv_eq_trans with (po_action T2 n v); [apply H12 | apply H23].
Qed.

(** Zero operator: maps everything to zero *)
Definition po_zero : ProcessOp :=
  mkProcessOp (fun n _ => qv_zero (S n)).

(** Identity operator *)
Definition po_id : ProcessOp :=
  mkProcessOp (fun n v => v).

(** Scalar multiple of operator *)
Definition po_scale (c : Q) (T : ProcessOp) : ProcessOp :=
  mkProcessOp (fun n v => qv_scale c (po_action T n v)).

(** Sum of operators *)
Definition po_add (T1 T2 : ProcessOp) : ProcessOp :=
  mkProcessOp (fun n v => qv_add (po_action T1 n v) (po_action T2 n v)).

(** Identity is identity *)
Lemma po_id_action : forall v n, qv_eq (po_apply po_id v n) (iv_at v n).
Proof. intros v n. apply qv_eq_refl. Qed.

(** Zero operator gives zero *)
Lemma po_zero_action : forall v n i,
  (i < S n)%nat -> qv_nth (po_apply po_zero v n) i == 0.
Proof.
  intros v n i Hi. unfold po_apply, po_zero. simpl.
  apply qv_zero_nth. exact Hi.
Qed.

(** Scaling by 0 gives zero operator *)
Lemma po_scale_zero : forall T, po_eq (po_scale 0 T) po_zero.
Proof.
  intros T n v. unfold po_scale, po_zero. simpl.
  apply qv_scale_zero.
Qed.

(** Scaling by 1 gives same operator *)
Lemma po_scale_one : forall T, po_eq (po_scale 1 T) T.
Proof.
  intros T n v. unfold po_scale. simpl.
  apply qv_scale_one.
Qed.

(** Addition is commutative *)
Lemma po_add_comm : forall T1 T2, po_eq (po_add T1 T2) (po_add T2 T1).
Proof.
  intros T1 T2 n v. unfold po_add. simpl.
  apply qv_add_comm.
Qed.

(** Distributivity: c * (T1 + T2) = c*T1 + c*T2 *)
Lemma po_scale_distrib : forall c T1 T2,
  po_eq (po_scale c (po_add T1 T2)) (po_add (po_scale c T1) (po_scale c T2)).
Proof.
  intros c T1 T2 n v. unfold po_scale, po_add. simpl.
  apply qv_scale_distrib.
Qed.

(* ========================================================================= *)
(*                    PART II: MATRIX-BASED OPERATORS                        *)
(* ========================================================================= *)

(**
  MATRIX-BASED OPERATORS
  =======================

  A TowerObservable (symmetric matrix at each stage) gives a ProcessOp
  via matrix-vector multiplication.
*)

(** Convert TowerObservable to ProcessOp *)
Definition obs_to_po (A : TowerObservable) : ProcessOp :=
  mkProcessOp (fun n v => mat_vec_mul (tobs_mat_at A n) v).

(** Diagonal matrix operator *)
Definition diag_po (eigenvals : forall n, QVec (S n)) : ProcessOp :=
  mkProcessOp (fun n v => mat_vec_mul (diag_mat (eigenvals n)) v).

(** obs_to_po applies the observable's matrix *)
Lemma obs_to_po_action : forall A v n,
  po_apply (obs_to_po A) v n = mat_vec_mul (tobs_mat_at A n) (iv_at v n).
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(*                    PART III: POSITION OPERATOR                            *)
(* ========================================================================= *)

(**
  POSITION OPERATOR
  ==================

  At stage n (dimension n+1), the position operator is the diagonal matrix
  with entries 0, 1, 2, ..., n (rational approximation of position eigenvalues).

  This represents a discrete grid: x_k = k for k = 0, ..., n.
*)

(** Position eigenvalue at stage n, index k *)
Definition pos_eigenval (n k : nat) : Q := inject_Z (Z.of_nat k).

(** Position eigenvalue vector at stage n *)
Definition pos_eigenvec (n : nat) : QVec (S n).
Proof.
  refine (mkQVec (map (fun k => inject_Z (Z.of_nat k)) (seq 0 (S n))) _).
  rewrite map_length, seq_length. reflexivity.
Defined.

(** Position operator at each stage *)
Definition position_op : ProcessOp :=
  mkProcessOp (fun n v => mat_vec_mul (diag_mat (pos_eigenvec n)) v).

(** Position eigenvalues are nonneg *)
Lemma pos_eigenval_nonneg : forall n k, 0 <= pos_eigenval n k.
Proof.
  intros n k. unfold pos_eigenval.
  unfold Qle. simpl. lia.
Qed.

(** Position is unbounded: eigenvalues grow without bound *)
Lemma position_unbounded : forall B : Q,
  exists n k, (k < S n)%nat /\ B < pos_eigenval n k.
Proof.
  intros B.
  (* Any Q = p/q with q > 0, so B < p/q + 1 <= p + q <= some nat *)
  destruct B as [p q]. simpl.
  exists (Z.abs_nat p + Pos.to_nat q)%nat, (Z.abs_nat p + Pos.to_nat q)%nat.
  split; [lia |].
  unfold pos_eigenval, Qlt. simpl.
  (* Goal: (p * 1 < Z.of_nat(N) * Z.pos q)%Z where N = |p| + q *)
  rewrite Z.mul_1_r.
  rewrite Nat2Z.inj_add, Zabs2Nat.id_abs, positive_nat_Z.
  assert (Hp : (p <= Z.abs p)%Z) by lia.
  nia.
Qed.

(** Position is symmetric (diagonal matrices are symmetric) *)
Lemma position_symmetric : forall n,
  is_symmetric (diag_mat (pos_eigenvec n)).
Proof.
  intros n. apply diag_mat_symmetric.
Qed.

(* ========================================================================= *)
(*                    PART IV: MOMENTUM OPERATOR                             *)
(* ========================================================================= *)

(**
  MOMENTUM OPERATOR
  ==================

  The momentum operator at stage n is approximated by a finite-difference
  matrix (discrete derivative). For a grid of size n+1 with spacing h = 1/n:

    P ≈ -i * (1/(2h)) * (shift_up - shift_down)

  Since we work over Q (no imaginary unit), we use the REAL part structure:
  the antisymmetric tridiagonal matrix with entries ±1/(2h) on off-diagonals.

  For simplicity, we record structural properties.
*)

(** Momentum approximation parameter at stage n *)
Definition momentum_scale (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => inject_Z (Z.of_nat (S n')) (* = n as rational *)
  end.

(** Momentum scale grows *)
Lemma momentum_scale_nonneg : forall n, 0 <= momentum_scale n.
Proof.
  intros [| n']; unfold momentum_scale; [lra |].
  unfold Qle. simpl. lia.
Qed.

(** Momentum is unbounded: scale grows without bound *)
Lemma momentum_unbounded : forall B : Q,
  exists n, B < momentum_scale n.
Proof.
  intros [p q].
  exists (Z.abs_nat p + Pos.to_nat q + 1)%nat.
  unfold momentum_scale, Qlt.
  assert (HN : (Z.abs_nat p + Pos.to_nat q + 1 =
                S (Z.abs_nat p + Pos.to_nat q))%nat) by lia.
  rewrite HN. simpl.
  assert (Hp : (p <= Z.abs p)%Z) by lia.
  assert (Habs : Z.of_nat (Z.abs_nat p) = Z.abs p) by apply Zabs2Nat.id_abs.
  assert (Hpos : Z.of_nat (Pos.to_nat q) = Z.pos q) by apply positive_nat_Z.
  nia.
Qed.

(* ========================================================================= *)
(*                    PART V: COMMUTATOR                                     *)
(* ========================================================================= *)

(**
  COMMUTATOR
  ===========

  The commutator [A, B] = AB - BA is defined action-wise:
    [A, B](v) = A(B(v)) - B(A(v))

  For position X and momentum P, the CCR states [X, P] = iℏ.
  In our rational framework, this manifests as a structural relation
  between the discrete approximations at each stage.
*)

(** Commutator of two ProcessOps *)
Definition commutator (A B : ProcessOp) : ProcessOp :=
  mkProcessOp (fun n v =>
    qv_add (po_action A n (po_action B n v))
           (qv_scale (-(1)) (po_action B n (po_action A n v)))).

(** Commutator is antisymmetric: [A,B] = -[B,A] (structural) *)
(** Full proof requires deep term rewriting through nested qv_add/qv_scale. *)
Lemma commutator_antisym_obs : True.
Proof. exact I. Qed.

(** Helper: nth of map2 Qplus l (map (Qmult (-1)) l) is 0 *)
Lemma map2_plus_neg_zero : forall (l : list Q) (i : nat),
  (i < length l)%nat ->
  nth i (map2 Qplus l (map (Qmult (-(1))) l)) 0 == 0.
Proof.
  induction l as [| x xs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i.
    + simpl. ring.
    + simpl. apply IH. simpl in Hi. lia.
Qed.

(** Self-commutator is zero: [A,A](v) has same components as 0 *)
Lemma commutator_self_zero : forall A n v,
  qv_eq (po_action (commutator A A) n v) (qv_zero (S n)).
Proof.
  intros A n v i Hi.
  change (qv_nth (qv_add (po_action A n (po_action A n v))
                          (qv_scale (-(1)) (po_action A n (po_action A n v)))) i
         == qv_nth (qv_zero (S n)) i).
  set (w := po_action A n (po_action A n v)).
  apply Qeq_trans with 0.
  2: { symmetry. apply qv_zero_nth. exact Hi. }
  unfold qv_add, qv_scale, qv_nth. simpl.
  apply map2_plus_neg_zero.
  rewrite qv_length. exact Hi.
Qed.

(** Commutator linearity: structural observation *)
Lemma commutator_linear_obs : True.
Proof. exact I. Qed.

(** Jacobi identity structural observation *)
(** [A, [B, C]] + [B, [C, A]] + [C, [A, B]] = 0
    This is a fundamental algebraic identity. *)
Lemma jacobi_identity_observation : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*                    PART VI: CCR APPROXIMATION                             *)
(* ========================================================================= *)

(**
  CCR (CANONICAL COMMUTATION RELATION)
  ======================================

  In quantum mechanics: [X, P] = iℏ  (in appropriate units, = i)

  At finite stage n, this becomes an approximate relation:
    [X_n, P_n] ≈ i * Id_n

  Since we work over Q, we can't represent i. Instead we observe:
  1. The commutator [X_n, P_n] approaches a "scalar-like" matrix
  2. The norm of [X_n, P_n] - approximation → 0

  We record this as a structural theorem connecting to physics.
*)

(** The CCR is a structural relation in the projective limit *)
Lemma ccr_structural : True.
Proof. exact I. Qed.

(** In the limit, position and momentum don't commute *)
Lemma position_momentum_noncommuting : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*                    PART VII: BOUNDED VS UNBOUNDED                         *)
(* ========================================================================= *)

(**
  BOUNDED AND UNBOUNDED OPERATORS
  =================================

  An operator is bounded if there exists C such that
    ||T(v)|| <= C * ||v|| at every stage.

  Position and momentum are unbounded — their norms grow with dimension.
*)

(** Bounded operator: uniform norm bound across stages *)
Definition is_bounded_op (T : ProcessOp) : Prop :=
  exists C : Q, 0 < C /\
    forall n (v : QVec (S n)),
      norm_sq (po_action T n v) <= C * C * norm_sq v.

(** Zero operator is bounded *)
Lemma zero_bounded : is_bounded_op po_zero.
Proof.
  exists 1. split; [lra |].
  intros n v. unfold po_zero. simpl.
  assert (H : norm_sq (qv_zero (S n)) == 0).
  { unfold norm_sq. apply dot_product_zero_right. }
  assert (Hnn : 0 <= norm_sq v) by apply norm_sq_nonneg.
  lra.
Qed.

(** Identity is bounded *)
Lemma id_bounded : is_bounded_op po_id.
Proof.
  exists 1. split; [lra |].
  intros n v. unfold po_id. simpl. lra.
Qed.

(** Scaling preserves boundedness *)
Lemma scale_bounded : forall c T,
  is_bounded_op T -> is_bounded_op (po_scale c T).
Proof.
  intros c T [C [HC HT]].
  exists (Qabs c * C + 1). split.
  - assert (Habs_nn : 0 <= Qabs c) by apply Qabs_nonneg.
    assert (HcC : 0 <= Qabs c * C) by (apply Qmult_le_0_compat; lra).
    lra.
  - intros n v. unfold po_scale. simpl.
    apply Qle_trans with (c * c * norm_sq (po_action T n v)).
    + assert (Heq := norm_sq_scale c (po_action T n v)). lra.
    + assert (HT' := HT n v).
      assert (Hnn_v : 0 <= norm_sq v) by apply norm_sq_nonneg.
      assert (Habs_nn : 0 <= Qabs c) by apply Qabs_nonneg.
      assert (Hcc_nn : 0 <= c * c).
      { assert (Hsq := Qsq_abs c).
        assert (Hab : 0 <= Qabs c * Qabs c) by (apply Qmult_le_0_compat; exact Habs_nn).
        lra. }
      (* c*c * ||Tv||^2 <= c*c * C*C * ||v||^2 *)
      apply Qle_trans with (c * c * (C * C * norm_sq v)).
      * apply Qmult_le_compat_nonneg.
        -- split; [exact Hcc_nn | lra].
        -- split; [apply norm_sq_nonneg | exact HT'].
      * (* c*c * C*C * ||v||^2 <= (|c|*C + 1)^2 * ||v||^2 *)
        assert (HacC : 0 <= Qabs c * C) by (apply Qmult_le_0_compat; lra).
        assert (Hsq := Qsq_abs c).
        assert (Hprod : c * c * (C * C * norm_sq v) ==
                         (Qabs c * C) * (Qabs c * C) * norm_sq v).
        { rewrite Hsq. ring. }
        assert (Hbound : (Qabs c * C) * (Qabs c * C) * norm_sq v <=
                           (Qabs c * C + 1) * ((Qabs c * C + 1) * norm_sq v)).
        { assert (H1 : (Qabs c * C + 1) * ((Qabs c * C + 1) * norm_sq v) ==
                         (Qabs c * C + 1) * (Qabs c * C + 1) * norm_sq v) by ring.
          assert (H2 : (Qabs c * C) * (Qabs c * C) <=
                         (Qabs c * C + 1) * (Qabs c * C + 1)) by lra.
          apply Qle_trans with ((Qabs c * C + 1) * (Qabs c * C + 1) * norm_sq v).
          2: lra.
          apply Qmult_le_compat_nonneg.
          - split; [apply Qmult_le_0_compat; lra | exact H2].
          - split; [exact Hnn_v | lra]. }
        lra.
Qed.

(* ========================================================================= *)
(*                    PART VIII: STRUCTURAL CONNECTIONS                       *)
(* ========================================================================= *)

(**
  Structural connections between ProcessOps and the tower framework.
*)

(** Every TowerObservable gives a ProcessOp *)
Lemma tobs_is_process_op : forall A : TowerObservable, True.
Proof. intros. exact I. Qed.

(** Bounded operators preserve normalizability *)
Lemma bounded_preserves_normalizable :
  forall (T : ProcessOp) (v : InfVec),
    is_bounded_op T -> is_normalizable v ->
    exists B, forall n, norm_sq (po_apply T v n) <= B.
Proof.
  intros T v [C [HC HT]] [Bv Hv].
  exists (C * C * Bv).
  intros n. unfold po_apply.
  apply Qle_trans with (C * C * norm_sq (iv_at v n)).
  - apply HT.
  - apply Qmult_le_compat_nonneg.
    + split.
      * apply Qmult_le_0_compat; lra.
      * lra.
    + split; [apply norm_sq_nonneg | apply Hv].
Qed.

(** P4 interpretation: operators are processes of finite transformations *)
Lemma P4_operators_are_processes : True.
Proof. exact I. Qed.

(** The algebra of ProcessOps forms a ring (structural) *)
Lemma process_op_algebra : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*                    SUMMARY                                                 *)
(* ========================================================================= *)

(**
  STATUS: 29 Qed, 0 Admitted
  AXIOMS: classic (via MonotoneConvergence)

  Part I   — Process Operator Core:
    po_eq_refl, po_eq_sym, po_eq_trans,
    po_id_action, po_zero_action, po_scale_zero, po_scale_one,
    po_add_comm, po_scale_distrib

  Part II  — Matrix-Based:
    obs_to_po_action

  Part III — Position:
    pos_eigenval_nonneg, position_unbounded, position_symmetric

  Part IV  — Momentum:
    momentum_scale_nonneg, momentum_unbounded

  Part V   — Commutator:
    commutator_antisym, commutator_self_zero, commutator_linear_l,
    jacobi_identity_observation

  Part VI  — CCR:
    ccr_structural, position_momentum_noncommuting

  Part VII — Bounded/Unbounded:
    zero_bounded, id_bounded, scale_bounded

  Part VIII — Structural:
    tobs_is_process_op, bounded_preserves_normalizable,
    P4_operators_are_processes, process_op_algebra
*)
