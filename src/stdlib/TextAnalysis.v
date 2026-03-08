(** * TextAnalysis.v -- Text Analysis Models as ToS Systems

    Theory of Systems -- Verified Standard Library (Batch 6)

    Elements: tokens (nat), documents (list nat), term frequencies (Q)
    Roles:    token -> Term, document -> Collection, frequency -> Weight
    Rules:    bag-of-words model (constitution), frequency counting
    Status:   relevant | irrelevant | ambiguous

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(** We define count_token BEFORE opening Q_scope so that bare [+] is nat addition. *)

Definition Document := list nat.

Fixpoint count_token (tok : nat) (doc : Document) : nat :=
  match doc with
  | [] => 0
  | t :: rest =>
    (if Nat.eqb t tok then 1 else 0) + count_token tok rest
  end.

Definition doc_length (doc : Document) : nat := length doc.

Open Scope Q_scope.

Definition bow_vector (vocab : list nat) (doc : Document) : list Q :=
  map (fun tok => inject_Z (Z.of_nat (count_token tok doc))) vocab.

Fixpoint dot_Q (l1 l2 : list Q) : Q :=
  match l1, l2 with
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dot_Q xs ys
  end.

Fixpoint sum_sq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => x * x + sum_sq xs
  end.

Fixpoint token_overlap (d1 d2 : Document) : nat :=
  match d1 with
  | [] => 0%nat
  | t :: rest =>
    ((if existsb (Nat.eqb t) d2 then 1 else 0) + token_overlap rest d2)%nat
  end.

(* ================================================================= *)
(** ** Theorems *)
(* ================================================================= *)

(** 1. count_token_nil *)
Lemma count_token_nil : forall tok, count_token tok [] = 0%nat.
Proof. reflexivity. Qed.

(** 2. count_token_cons_match *)
Lemma count_token_cons_match : forall tok rest,
  count_token tok (tok :: rest) = S (count_token tok rest).
Proof.
  intros tok rest.
  unfold count_token; fold count_token.
  rewrite Nat.eqb_refl.
  simpl. lia.
Qed.

(** 3. count_token_cons_nomatch *)
Lemma count_token_cons_nomatch : forall tok t rest,
  tok <> t ->
  count_token tok (t :: rest) = count_token tok rest.
Proof.
  intros tok t rest Hneq.
  unfold count_token; fold count_token.
  destruct (Nat.eqb_spec t tok).
  - lia.
  - simpl. lia.
Qed.

(** 4. doc_length_nil *)
Lemma doc_length_nil : doc_length [] = 0%nat.
Proof. reflexivity. Qed.

(** 5. doc_length_cons *)
Lemma doc_length_cons : forall t rest,
  doc_length (t :: rest) = S (doc_length rest).
Proof. reflexivity. Qed.

(** 6. bow_vector_nil *)
Lemma bow_vector_nil : forall doc, bow_vector [] doc = [].
Proof. reflexivity. Qed.

(** 7. bow_vector_length *)
Lemma bow_vector_length : forall vocab doc,
  length (bow_vector vocab doc) = length vocab.
Proof.
  intros vocab doc.
  unfold bow_vector.
  apply map_length.
Qed.

(** 8. dot_Q_nil_l *)
Lemma dot_Q_nil_l : forall l, dot_Q [] l = 0.
Proof. reflexivity. Qed.

(** 9. dot_Q_singleton *)
Lemma dot_Q_singleton : forall a b,
  dot_Q [a] [b] == a * b.
Proof.
  intros a b. simpl. ring.
Qed.

(** 10. dot_Q_two *)
Lemma dot_Q_two : forall a1 a2 b1 b2,
  dot_Q [a1; a2] [b1; b2] == a1 * b1 + a2 * b2.
Proof.
  intros a1 a2 b1 b2. simpl. ring.
Qed.

(** 11. sum_sq_nil *)
Lemma sum_sq_nil : sum_sq [] = 0.
Proof. reflexivity. Qed.

(** Helper: square of any rational is non-negative. *)
Lemma Q_sq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - assert (H: 0 <= (-x) * (-x)).
    { apply Qmult_le_0_compat; lra. }
    ring_simplify in H. lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(** 12. sum_sq_nonneg *)
Lemma sum_sq_nonneg : forall l, 0 <= sum_sq l.
Proof.
  induction l as [| x xs IH].
  - simpl. lra.
  - simpl.
    assert (Hsq : 0 <= x * x) by (apply Q_sq_nonneg).
    lra.
Qed.

(** 13. token_overlap_nil *)
Lemma token_overlap_nil : forall d2, token_overlap [] d2 = 0%nat.
Proof. reflexivity. Qed.

(** 14. count_token_app *)
Lemma count_token_app : forall tok d1 d2,
  count_token tok (d1 ++ d2) = (count_token tok d1 + count_token tok d2)%nat.
Proof.
  intros tok d1 d2.
  induction d1 as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    destruct (Nat.eqb h tok); lia.
Qed.

(** 15. dot_Q_comm *)
Lemma dot_Q_comm : forall a b c d,
  dot_Q [a; b] [c; d] == dot_Q [c; d] [a; b].
Proof.
  intros a b c d. simpl. ring.
Qed.
