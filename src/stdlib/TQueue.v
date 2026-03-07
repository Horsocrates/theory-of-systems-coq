(* TQueue: FIFO Queue as ToS System *)
(* STATUS: 14 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: 2026 *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import InductiveSystems.

Record TQueue (A : Type) := mkTQueue {
  tq_front : list A;
  tq_back : list A;
}.

Arguments mkTQueue {A}.
Arguments tq_front {A}.
Arguments tq_back {A}.

Definition tq_empty {A} : TQueue A := mkTQueue [] [].

Definition tq_enqueue {A} (x : A) (q : TQueue A) : TQueue A :=
  mkTQueue (tq_front q) (x :: tq_back q).

Definition tq_to_list {A} (q : TQueue A) : list A :=
  tq_front q ++ rev (tq_back q).

Definition tq_size {A} (q : TQueue A) : nat :=
  length (tq_front q) + length (tq_back q).

Definition tq_is_empty {A} (q : TQueue A) : bool :=
  match tq_front q, tq_back q with
  | [], [] => true
  | _, _ => false
  end.

Definition tq_dequeue {A} (q : TQueue A) : option (A * TQueue A) :=
  match tq_front q with
  | x :: rest => Some (x, mkTQueue rest (tq_back q))
  | [] => match rev (tq_back q) with
          | x :: rest => Some (x, mkTQueue rest [])
          | [] => None
          end
  end.

Definition tq_peek {A} (q : TQueue A) : option A :=
  match tq_front q with
  | x :: _ => Some x
  | [] => match rev (tq_back q) with
          | x :: _ => Some x
          | [] => None
          end
  end.

Lemma tq_empty_size : forall A, @tq_size A tq_empty = 0.
Proof. intros A. unfold tq_size, tq_empty. simpl. reflexivity. Qed.

Lemma tq_empty_is_empty : forall A, @tq_is_empty A tq_empty = true.
Proof. intros A. unfold tq_is_empty, tq_empty. simpl. reflexivity. Qed.

Lemma tq_enqueue_size : forall A (x : A) (q : TQueue A),
  tq_size (tq_enqueue x q) = S (tq_size q).
Proof.
  intros A x q. unfold tq_size, tq_enqueue. simpl. lia.
Qed.

Lemma tq_to_list_empty : forall A, @tq_to_list A tq_empty = [].
Proof. intros A. unfold tq_to_list, tq_empty. simpl. reflexivity. Qed.

Lemma tq_enqueue_nonempty : forall A (x : A) (q : TQueue A),
  tq_is_empty (tq_enqueue x q) = false.
Proof.
  intros A x q. unfold tq_is_empty, tq_enqueue. simpl.
  destruct (tq_front q); reflexivity.
Qed.

Lemma tq_to_list_enqueue : forall A (x : A) (q : TQueue A),
  tq_to_list (tq_enqueue x q) = tq_to_list q ++ [x].
Proof.
  intros A x q. unfold tq_to_list, tq_enqueue. simpl.
  rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma tq_dequeue_empty : forall A, @tq_dequeue A tq_empty = None.
Proof. intros A. unfold tq_dequeue, tq_empty. simpl. reflexivity. Qed.

Lemma tq_peek_empty : forall A, @tq_peek A tq_empty = None.
Proof. intros A. unfold tq_peek, tq_empty. simpl. reflexivity. Qed.

Lemma tq_size_nonneg : forall A (q : TQueue A), 0 <= tq_size q.
Proof. intros A q. unfold tq_size. lia. Qed.

Lemma tq_to_list_length : forall A (q : TQueue A),
  length (tq_to_list q) = tq_size q.
Proof.
  intros A q. unfold tq_to_list, tq_size.
  rewrite length_app. rewrite rev_length. reflexivity.
Qed.

Lemma tq_dequeue_front : forall A (x : A) (rest : list A) (back : list A),
  tq_dequeue (mkTQueue (x :: rest) back) = Some (x, mkTQueue rest back).
Proof. intros. unfold tq_dequeue. simpl. reflexivity. Qed.

Lemma tq_enqueue_size_positive : forall A (x : A) (q : TQueue A),
  0 < tq_size (tq_enqueue x q).
Proof.
  intros A x q. rewrite tq_enqueue_size. lia.
Qed.

Definition tq_depth {A} (q : TQueue A) : nat := tq_size q.

Definition tqueue_fg (A : Type) : FinitelyGenerated (TQueue A) :=
  mkFinitelyGenerated (TQueue A) (@tq_depth A).

Lemma tqueue_fg_exists : forall A,
  exists (fg : FinitelyGenerated (TQueue A)),
    fg_depth (TQueue A) fg = @tq_depth A.
Proof. intros A. exists (tqueue_fg A). reflexivity. Qed.

Example queue_fifo_example :
  let q := tq_enqueue 1 (tq_enqueue 2 (tq_enqueue 3 (@tq_empty nat))) in
  tq_to_list q = [3; 2; 1].
Proof. simpl. reflexivity. Qed.

(* END OF TQueue.v: 14 Qed, 0 Admitted, 0 axioms *)
