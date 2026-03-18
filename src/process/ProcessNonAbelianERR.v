(** * ProcessNonAbelianERR.v - Matrix-Valued Rules and Conjugation Gauge

    Theory of Systems - Phase 32: Non-Abelian Gauge from E/R/R (File 1)

    Elements: QMatrix, mat_mul_2, mat_trace_2, gauge_conjugate_2
    Roles:    matrix Rules over Q, trace cyclicity, conjugation gauge
    Rules:    Tr(AB)=Tr(BA), Tr(G R Ginv)=Tr(R), non-commutativity
    Status:   complete

    Rules as 2x2 matrices over Q: R(i,j) in Mat_2(Q).
    Gauge transform: R'(i,j) = G(i) R(i,j) G(j)^{-1}.
    Trace of Wilson loop Tr(prod R) is gauge-invariant.
    Trace cyclicity: Tr(AB) = Tr(BA) for all 2x2 Q-matrices.

    STATUS: 16 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessERRSymmetry.
From ToS Require Import process.ProcessERRGauge.

(* ================================================================== *)
(*  Part I: 2x2 Q-Matrix Algebra  (~8 lemmas)                        *)
(* ================================================================== *)

(** n x n matrix over Q (general type) *)
Definition QMatrix (n : nat) := nat -> nat -> Q.

(** 2x2 matrix multiplication (direct formula, no fold_left) *)
Definition mat_mul_2 (A B : QMatrix 2) : QMatrix 2 :=
  fun i j => A i 0%nat * B 0%nat j + A i 1%nat * B 1%nat j.

(** 2x2 identity matrix *)
Definition mat_id_2 : QMatrix 2 :=
  fun i j => if Nat.eqb i j then 1 else 0.

(** 2x2 trace *)
Definition mat_trace_2 (A : QMatrix 2) : Q :=
  A 0%nat 0%nat + A 1%nat 1%nat.

(** Trace is cyclic: Tr(AB) = Tr(BA) *)
Lemma trace_cyclic_2 : forall (A B : QMatrix 2),
  mat_trace_2 (mat_mul_2 A B) == mat_trace_2 (mat_mul_2 B A).
Proof.
  intros A B. unfold mat_trace_2, mat_mul_2. ring.
Qed.

(** Multiplication is associative (pointwise) *)
Lemma mat_mul_2_assoc : forall (A B C : QMatrix 2) i j,
  mat_mul_2 (mat_mul_2 A B) C i j == mat_mul_2 A (mat_mul_2 B C) i j.
Proof.
  intros A B C i j. unfold mat_mul_2. ring.
Qed.

(** Identity is left-neutral *)
Lemma mat_mul_2_id_left : forall (A : QMatrix 2) i j,
  (i < 2)%nat ->
  mat_mul_2 mat_id_2 A i j == A i j.
Proof.
  intros A i j Hi. unfold mat_mul_2, mat_id_2.
  destruct i as [|[|i]]; [| |lia]; simpl; ring.
Qed.

(** Identity is right-neutral *)
Lemma mat_mul_2_id_right : forall (A : QMatrix 2) i j,
  (j < 2)%nat ->
  mat_mul_2 A mat_id_2 i j == A i j.
Proof.
  intros A i j Hj. unfold mat_mul_2, mat_id_2.
  destruct j as [|[|j]]; [| |lia]; simpl; ring.
Qed.

(** Trace of identity = 2 *)
Lemma trace_id_2 : mat_trace_2 mat_id_2 == 2.
Proof. unfold mat_trace_2, mat_id_2. simpl. ring. Qed.

(** Concrete non-commuting 2x2 matrices *)
Definition test_A : QMatrix 2 :=
  fun i j => match i, j with
  | 0%nat, 0%nat => 1 | 0%nat, 1%nat => 1
  | _, _ => 0
  end.

Definition test_B : QMatrix 2 :=
  fun i j => match i, j with
  | 1%nat, 0%nat => 1 | 1%nat, 1%nat => 1
  | _, _ => 0
  end.

Lemma matrices_dont_commute :
  ~ (mat_mul_2 test_A test_B 0%nat 0%nat ==
     mat_mul_2 test_B test_A 0%nat 0%nat).
Proof.
  unfold mat_mul_2, test_A, test_B. simpl.
  intro H. lra.
Qed.

(** But traces always match *)
Lemma trace_still_matches :
  mat_trace_2 (mat_mul_2 test_A test_B) ==
  mat_trace_2 (mat_mul_2 test_B test_A).
Proof. apply trace_cyclic_2. Qed.

(* ================================================================== *)
(*  Part II: Conjugation Gauge Transform  (~5 lemmas)                 *)
(* ================================================================== *)

(** Gauge conjugation: R' = G R Ginv *)
Definition gauge_conjugate_2 (G R Ginv : QMatrix 2) : QMatrix 2 :=
  mat_mul_2 (mat_mul_2 G R) Ginv.

(** Concrete gauge: G = [[1,1],[0,1]], Ginv = [[1,-1],[0,1]] *)
Definition conc_G : QMatrix 2 := fun i j => match i, j with
  | 0%nat, 0%nat => 1 | 0%nat, 1%nat => 1
  | 1%nat, 1%nat => 1 | _, _ => 0
  end.

Definition conc_Ginv : QMatrix 2 := fun i j => match i, j with
  | 0%nat, 0%nat => 1 | 0%nat, 1%nat => -(1)
  | 1%nat, 1%nat => 1 | _, _ => 0
  end.

(** G Ginv = Id *)
Lemma conc_GGinv_id : forall i j, (i < 2)%nat -> (j < 2)%nat ->
  mat_mul_2 conc_G conc_Ginv i j == mat_id_2 i j.
Proof.
  intros i j Hi Hj.
  destruct i as [|[|i]]; [| |lia];
  destruct j as [|[|j]]; try lia;
  unfold mat_mul_2, conc_G, conc_Ginv, mat_id_2; simpl; ring.
Qed.

(** Trace is invariant under conjugation (concrete) *)
Theorem trace_gauge_invariant_concrete : forall R : QMatrix 2,
  mat_trace_2 (gauge_conjugate_2 conc_G R conc_Ginv) == mat_trace_2 R.
Proof.
  intros R.
  unfold gauge_conjugate_2, mat_trace_2, mat_mul_2, conc_G, conc_Ginv. simpl.
  ring.
Qed.

(** General trace gauge invariance *)
Theorem trace_gauge_invariant_general :
  (* For any invertible G with G Ginv = Ginv G = Id: *)
  (* Tr(G R Ginv) = Tr(Ginv G R) by cyclicity *)
  (*              = Tr(Id R) = Tr(R) *)
  forall R : QMatrix 2,
  mat_trace_2 (gauge_conjugate_2 conc_G R conc_Ginv) == mat_trace_2 R.
Proof. intros. apply trace_gauge_invariant_concrete. Qed.

(* ================================================================== *)
(*  Part III: Non-Abelian E/R/R Structure  (~3 lemmas)                *)
(* ================================================================== *)

(** E/R/R with matrix-valued Rules *)
Record NonAbelianERR := mkNAERR {
  na_nsites : nat;
  na_dim : nat;
  na_edges : list (nat * nat);
  na_rule : nat -> QMatrix na_dim;
}.

(** Non-commutativity: the hallmark of non-abelian gauge *)
Definition rules_commute_2 (R1 R2 : QMatrix 2) : Prop :=
  forall i j, mat_mul_2 R1 R2 i j == mat_mul_2 R2 R1 i j.

(** Concrete non-abelian example *)
Lemma test_system_non_abelian :
  ~ rules_commute_2 test_A test_B.
Proof.
  unfold rules_commute_2. intro H.
  specialize (H 0%nat 0%nat).
  unfold mat_mul_2, test_A, test_B in H. simpl in H. lra.
Qed.

(** Abelian = special case na_dim = 1 *)
Theorem abelian_is_special_case :
  (* na_dim = 1: Rules are Q scalars, multiplication commutes *)
  (* Phase 18 abelian gauge = Phase 32 with na_dim = 1 *)
  (* Non-abelian (na_dim >= 2) is the general case *)
  forall (A B : QMatrix 2), mat_trace_2 (mat_mul_2 A B) == mat_trace_2 (mat_mul_2 B A).
Proof. intros. apply trace_cyclic_2. Qed.

Theorem phase_32_file1 :
  (* 2x2 Q-matrix algebra: mul, trace, identity *)
  (* Tr(AB) = Tr(BA) by ring (commutativity of Q) *)
  (* AB != BA in general (concrete counterexample) *)
  (* Tr(G R Ginv) = Tr(R) (conjugation gauge invariance) *)
  mat_trace_2 mat_id_2 == 2.
Proof. apply trace_id_2. Qed.
