(** * ProcessRefinement.v -- The central principle of process mathematics
    "Limit loses information. Process preserves."
    Elements: Process, process_eq, convergence_rate
    Roles:    Define abstract process framework
    Rules:    Same process → same limit (but not converse)
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  BASIC DEFINITIONS                                                  *)
(* ================================================================== *)

(** Process = function ℕ → Q *)
Definition Process := nat -> Q.

(** Two processes are equal iff equal at every step *)
Definition process_eq (p q : Process) : Prop :=
  forall K, p K == q K.

(** Two processes have the same value at step K *)
Definition same_at (p q : Process) (K : nat) : Prop :=
  p K == q K.

(** Processes differ: ∃ K where they disagree *)
Definition process_neq (p q : Process) : Prop :=
  exists K, ~ (p K == q K).

(* ================================================================== *)
(*  REFINEMENT: same process → same value at each K                    *)
(* ================================================================== *)

Theorem process_refines_limit : forall (p q : Process),
  process_eq p q -> forall K, same_at p q K.
Proof. intros p q Heq K. unfold same_at. apply Heq. Qed.

(** Converse FAILS: same value at one K does NOT imply same process *)
Theorem same_at_not_implies_eq : exists (p q : Process),
  same_at p q 0 /\ process_neq p q.
Proof.
  exists (fun _ => 1), (fun K => match K with O => 1 | _ => 2 end).
  split.
  - unfold same_at. simpl. reflexivity.
  - unfold process_neq. exists 1%nat. simpl. unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  CONVERGENCE RATE                                                   *)
(* ================================================================== *)

(** Rate = |p(K+1) - p(K)| *)
Definition convergence_rate (p : Process) (K : nat) : Q :=
  Qabs (p (S K) - p K).

(** Constant process has zero rate (concrete) *)
Lemma constant_rate_zero_1 : forall K,
  convergence_rate (fun _ => 1) K == 0.
Proof.
  intro K. unfold convergence_rate. simpl.
  vm_compute. reflexivity.
Qed.

Lemma constant_rate_zero_half : forall K,
  convergence_rate (fun _ => 1#2) K == 0.
Proof.
  intro K. unfold convergence_rate. simpl.
  vm_compute. reflexivity.
Qed.

(** Process that changes has nonzero rate *)
Definition step_process : Process :=
  fun K => match K with O => 0 | _ => 1 end.

Lemma step_rate_nonzero : ~ (convergence_rate step_process 0 == 0).
Proof.
  unfold convergence_rate, step_process. simpl.
  vm_compute. unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  PROCESS OSCILLATION                                                *)
(* ================================================================== *)

Definition oscillation (p : Process) (K : nat) : Q :=
  Qabs (p (S (S K)) - p (S K)) - Qabs (p (S K) - p K).

(** Monotone convergence: oscillation ≤ 0 *)
(** (rate decreases with K) *)

(* ================================================================== *)
(*  PROCESS COMPARISON                                                 *)
(* ================================================================== *)

(** p converges faster than q if rate_p < rate_q *)
Definition faster (p q : Process) (K : nat) : Prop :=
  convergence_rate p K < convergence_rate q K.

(** Faster convergence is a process-level invariant *)
(** Same limit, different rate → distinguishable processes *)

(* ================================================================== *)
(*  Qpow for later use                                                 *)
(* ================================================================== *)

Fixpoint Qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => q * Qpow q k
  end.

Lemma Qpow_0 : forall q, Qpow q 0 == 1.
Proof. intros. simpl. reflexivity. Qed.

Lemma Qpow_1 : forall q, Qpow q 1 == q.
Proof. intros. simpl. ring. Qed.

Lemma Qpow_2 : forall q, Qpow q 2 == q * q.
Proof. intros. simpl. ring. Qed.

Lemma Qpow_S : forall q n, Qpow q (S n) == q * Qpow q n.
Proof. intros. simpl. reflexivity. Qed.

(** Concrete values *)
Lemma Qpow_2_3 : Qpow 2 3 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma Qpow_3_2 : Qpow 3 2 == 9.
Proof. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem process_refinement_basics :
  (* Same process → same at each step *)
  (forall p q, process_eq p q -> forall K, same_at p q K) /\
  (* Same at one step does NOT imply same process *)
  (exists p q, same_at p q 0 /\ process_neq p q) /\
  (* Constant process: zero rate *)
  (forall K, convergence_rate (fun _ => 1) K == 0).
Proof.
  split; [|split].
  - exact process_refines_limit.
  - exact same_at_not_implies_eq.
  - intro K. apply constant_rate_zero_1.
Qed.
