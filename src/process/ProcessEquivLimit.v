(** * ProcessEquivLimit.v — What process_equiv says, and what it does not

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapter II.1, places 1.6 and 1.7, 2026-11-13):

    Elements: processes over Q indexed by stages (RealProcess).
    Roles:    a process as a raw sequence of stage values; a process as a
              representative of a class under process_equiv; a constant
              process as a rational limit.
    Rules:    process_equiv R1 R2 — the difference of the two processes goes
              below every precision as the stage grows.
    Proved:   (1) the relation does NOT require convergence: the process
                  0, 1, 2, ... is equivalent to itself, is not Cauchy and
                  has no rational limit;
              (2) for processes that have a rational limit the relation is
                  exactly "they converge to the same limit";
              (3) the relation is not stagewise equality: the process of
                  nines and the constant process 1 are equivalent and differ
                  at every stage — the three modes of 0.999... in one
                  theorem.
    P4 diagnostic ("could it be otherwise?"): every statement is about
              finite stages and rational bounds. Forced: (1)-(3). NOT
              claimed: a quotient type of processes (a "class" is the
              relation itself); a limit that is not a rational number.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessNinePoint.

Open Scope Q_scope.

(* ========================================================================= *)
(*  1. The relation does not require convergence                             *)
(* ========================================================================= *)

(** The process 0, 1, 2, 3, ... *)
Definition stage_process : RealProcess := fun n => inject_Z (Z.of_nat n).

Lemma stage_process_not_Cauchy : ~ is_Cauchy stage_process.
Proof.
  intro H.
  assert (H01 : 0 < 1) by (unfold Qlt; simpl; lia).
  destruct (H 1 H01) as [N HN].
  assert (HS : (N <= S N)%nat) by lia.
  specialize (HN (S N) N HS (Nat.le_refl N)).
  unfold stage_process in HN.
  assert (E : inject_Z (Z.of_nat (S N)) - inject_Z (Z.of_nat N) == 1).
  { rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus.
    change (inject_Z 1) with 1. ring. }
  rewrite (Qabs_wd _ _ E) in HN.
  unfold Qlt in HN. simpl in HN. lia.
Qed.

(** A process that converges nowhere is still equivalent to itself. *)
Theorem equiv_does_not_require_convergence :
  stage_process ~~ stage_process /\ ~ is_Cauchy stage_process.
Proof. split; [apply process_equiv_refl | exact stage_process_not_Cauchy]. Qed.

Theorem stage_process_has_no_rational_limit :
  forall q : Q, ~ (stage_process ~~ const_process q).
Proof.
  intros q H. apply stage_process_not_Cauchy.
  apply (equiv_cauchy_l (const_process q) stage_process).
  - apply process_equiv_sym. exact H.
  - apply const_is_Cauchy.
Qed.

(* ========================================================================= *)
(*  2. For processes with a rational limit: "converge to the same limit"     *)
(* ========================================================================= *)

Lemma same_limit_gives_equiv : forall (R1 R2 : RealProcess) (q : Q),
  R1 ~~ const_process q -> R2 ~~ const_process q -> R1 ~~ R2.
Proof.
  intros R1 R2 q H1 H2.
  apply (process_equiv_trans R1 (const_process q) R2);
    [exact H1 | apply process_equiv_sym; exact H2].
Qed.

Lemma equiv_transfers_limit : forall (R1 R2 : RealProcess) (q : Q),
  R1 ~~ R2 -> R1 ~~ const_process q -> R2 ~~ const_process q.
Proof.
  intros R1 R2 q H12 H1.
  apply (process_equiv_trans R2 R1 (const_process q));
    [apply process_equiv_sym; exact H12 | exact H1].
Qed.

(** If one of two processes has the rational limit q, the two are equivalent
    exactly when the other has the same limit. *)
Theorem equiv_iff_same_limit_when_one_converges :
  forall (R1 R2 : RealProcess) (q : Q),
    R1 ~~ const_process q -> (R1 ~~ R2 <-> R2 ~~ const_process q).
Proof.
  intros R1 R2 q H1. split.
  - intro H12. exact (equiv_transfers_limit R1 R2 q H12 H1).
  - intro H2. exact (same_limit_gives_equiv R1 R2 q H1 H2).
Qed.

(* ========================================================================= *)
(*  3. Not stagewise equality: the three modes of 0.999...                   *)
(* ========================================================================= *)

(** The process of nines is not stagewise equal to the constant process 1. *)
Lemma nines_not_pointwise_equal :
  forall n : nat, ~ (nine_raw n == const_process 1 n).
Proof.
  intros n E. unfold const_process in E.
  pose proof (nine_raw_lt_one n) as H. rewrite E in H. exact (Qlt_irrefl 1 H).
Qed.

(** As raw processes 0.999... and 1 differ at every stage; as classes under
    process_equiv they coincide. *)
Theorem nines_three_modes :
  (forall n : nat, nine_raw n < const_process 1 n) /\
  (forall n : nat, ~ (nine_raw n == const_process 1 n)) /\
  nine_raw ~~ const_process 1.
Proof.
  split; [ | split].
  - intro n. unfold const_process. exact (nine_raw_lt_one n).
  - exact nines_not_pointwise_equal.
  - exact nine_equiv_one.
Qed.

(** process_equiv is not stagewise equality. *)
Theorem equiv_is_not_pointwise :
  exists R1 R2 : RealProcess, R1 ~~ R2 /\ forall n : nat, ~ (R1 n == R2 n).
Proof.
  exists nine_raw, (const_process 1).
  split; [exact nine_equiv_one | exact nines_not_pointwise_equal].
Qed.
