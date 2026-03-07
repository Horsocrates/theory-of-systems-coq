(** * Combinatorics.v — Counting Structures as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: natural numbers, finite sets/sequences
    Roles:    n -> UniverseSize, k -> SelectionSize
    Rules:    counting rules (factorial, binomial, pigeonhole)
    Status:   counted | overcounted

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ================================================================= *)
(*           PART I: FACTORIAL (6 Qed)                                *)
(* ================================================================= *)

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

(** fact 0 = 1 *)
Lemma fact_0 : fact 0 = 1.
Proof. reflexivity. Qed.

(** fact 1 = 1 *)
Lemma fact_1 : fact 1 = 1.
Proof. reflexivity. Qed.

(** Recursive unfolding *)
Lemma fact_succ : forall n, fact (S n) = S n * fact n.
Proof. reflexivity. Qed.

(** Factorial is always positive *)
Lemma fact_pos : forall n, 1 <= fact n.
Proof.
  induction n as [|n' IH].
  - simpl. lia.
  - simpl. assert (H : 1 <= fact n') by exact IH.
    destruct (fact n') as [|m] eqn:E.
    + lia.
    + lia.
Qed.

(** fact 5 = 120 *)
Lemma fact_example_5 : fact 5 = 120.
Proof. reflexivity. Qed.

(** fact 6 = 720 *)
Lemma fact_example_6 : fact 6 = 720.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*           PART II: BINOMIAL COEFFICIENTS (12 Qed)                  *)
(* ================================================================= *)

Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' => binomial n' k' + binomial n' (S k')
  end.

(** C(n, 0) = 1 *)
Lemma binomial_0_r : forall n, binomial n 0 = 1.
Proof. destruct n; reflexivity. Qed.

(** C(0, k) = 0 for k > 0 *)
Lemma binomial_0_l : forall k, 0 < k -> binomial 0 k = 0.
Proof. destruct k; [lia | reflexivity]. Qed.

(** When k > n, C(n, k) = 0 *)
Lemma binomial_gt : forall n k, n < k -> binomial n k = 0.
Proof.
  induction n as [|n' IH]; intros k Hlt.
  - destruct k; [lia | reflexivity].
  - destruct k as [|k']; [lia|].
    simpl. rewrite IH by lia. rewrite IH by lia. lia.
Qed.

(** C(n, n) = 1 *)
Lemma binomial_n_n : forall n, binomial n n = 1.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite binomial_gt by lia. lia.
Qed.

(** C(n, 1) = n *)
Lemma binomial_1_r : forall n, binomial n 1 = n.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite binomial_0_r. lia.
Qed.

(** Pascal's identity (definitional) *)
Lemma pascal_identity : forall n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. reflexivity. Qed.

(** C(4, 2) = 6 *)
Lemma binomial_example_4_2 : binomial 4 2 = 6.
Proof. reflexivity. Qed.

(** C(5, 3) = 10 *)
Lemma binomial_example_5_3 : binomial 5 3 = 10.
Proof. reflexivity. Qed.

(** C(10, 0) = 1 *)
Lemma binomial_example_10_0 : binomial 10 0 = 1.
Proof. reflexivity. Qed.

(** Row sum for n=2: C(2,0) + C(2,1) + C(2,2) = 4 = 2^2 *)
Lemma sum_binomial_2 :
  binomial 2 0 + binomial 2 1 + binomial 2 2 = 4.
Proof. reflexivity. Qed.

(** Symmetry examples: C(n, k) = C(n, n-k) *)
Lemma binomial_sym_4_1 : binomial 4 1 = binomial 4 3.
Proof. reflexivity. Qed.

Lemma binomial_sym_5_2 : binomial 5 2 = binomial 5 3.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*         PART III: PIGEONHOLE & LIST PROPERTIES (2 Qed)             *)
(* ================================================================= *)

(** NoDup for seq *)
Lemma nodup_seq : forall len start, NoDup (seq start len).
Proof.
  induction len as [|len' IH]; intros start.
  - simpl. constructor.
  - simpl. constructor.
    + intro Hin. apply in_seq in Hin. lia.
    + apply IH.
Qed.

(** Helper: NoDup + incl implies length bound *)
Lemma nodup_incl_length_nat :
  forall (l1 l2 : list nat),
    NoDup l1 -> incl l1 l2 -> length l1 <= length l2.
Proof.
  induction l1 as [|x l1' IH]; intros l2 Hnd Hincl.
  - simpl. lia.
  - inversion Hnd; subst.
    assert (Hx : In x l2) by (apply Hincl; simpl; auto).
    apply in_split in Hx.
    destruct Hx as [la [lb Heq]].
    subst l2.
    simpl.
    assert (Hlen : length l1' <= length (la ++ lb)).
    { apply IH.
      - exact H2.
      - intros y Hy.
        assert (Hy2 : In y (x :: l1')) by (simpl; auto).
        apply Hincl in Hy2.
        apply in_app_or in Hy2.
        apply in_or_app.
        destruct Hy2 as [Hla | [Heq | Hlb]].
        + left. exact Hla.
        + subst y. contradiction.
        + right. exact Hlb.
    }
    rewrite app_length in Hlen |- *.
    simpl. lia.
Qed.

(** Pigeonhole: if |l| > n, all elements < n, and l has no duplicates, contradiction *)
Lemma pigeonhole_simple :
  forall (l : list nat) (n : nat),
    length l > n ->
    (forall x, In x l -> x < n) ->
    NoDup l ->
    False.
Proof.
  intros l n Hlen Hbound Hnd.
  assert (Hincl : incl l (seq 0 n)).
  { intros x Hx. apply in_seq. split; [lia | apply Hbound; exact Hx]. }
  apply nodup_incl_length_nat in Hincl; [|exact Hnd].
  rewrite seq_length in Hincl. lia.
Qed.

(** Concrete pigeonhole example: [0;1;2;0] has a duplicate *)
Lemma pigeonhole_example : ~ NoDup [0; 1; 2; 0].
Proof.
  intro H.
  inversion H as [|x l Hn Hnd]; subst.
  apply Hn. simpl. auto.
Qed.
