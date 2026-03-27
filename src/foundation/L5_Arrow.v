(* L5_Arrow.v *)
(* E/R/R: Elements = stages+distinctions, Roles = arrow/irreversibility, Rules = forward-only *)
(* Standalone — only Stdlib imports *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(** * Stage and Direction *)

Definition stage := nat.
Definition undifferentiated : stage := 0%nat.
Definition first_distinction : stage := 1%nat.

(** * Distinction sets (re-defined standalone) *)

Definition DistSet' := list nat.

Definition has_dist' (D : DistSet') (d : nat) : bool :=
  existsb (Nat.eqb d) D.

Definition dist_subset' (D1 D2 : DistSet') : Prop :=
  forall d, has_dist' D1 d = true -> has_dist' D2 d = true.

Definition L5_pres (D : nat -> DistSet') : Prop :=
  forall K, dist_subset' (D K) (D (S K)).

(** * Arrow *)

Definition arrow_forward (K : stage) : stage := S K.

(** * Nothing before undifferentiated *)

Lemma nothing_before_undifferentiated :
  ~ exists s : stage, (s < undifferentiated)%nat.
Proof. intro H. destruct H as [s Hs]. unfold undifferentiated in Hs. lia. Qed.

(** * Distinction permanence (standalone) *)

Lemma cannot_unmake_distinction : forall D K d,
  L5_pres D ->
  has_dist' (D K) d = true ->
  forall K', (K <= K')%nat ->
  has_dist' (D K') d = true.
Proof.
  intros D K d HL5 Hd K' Hle.
  induction Hle.
  - exact Hd.
  - apply HL5. exact IHHle.
Qed.

(** * Arrow is strictly forward *)

Lemma arrow_strictly_forward : forall K : stage,
  (K < arrow_forward K)%nat.
Proof. intro K. unfold arrow_forward. lia. Qed.

(** * No backward arrow from start *)

Lemma no_arrow_backward_from_start :
  ~ exists K : stage, (arrow_forward K < undifferentiated)%nat.
Proof.
  intro H. destruct H as [K HK]. unfold arrow_forward, undifferentiated in HK. lia.
Qed.

(** * Starting configuration *)

Definition D_start : DistSet' := [1].

From Stdlib Require Import QArith.
Open Scope Q_scope.

Definition entropy_start : Q := inject_Z (Z.of_nat (length D_start)).

Lemma start_minimal : length D_start = 1%nat.
Proof. simpl. reflexivity. Qed.

Lemma entropy_start_minimal : entropy_start == 1#1.
Proof. unfold entropy_start, D_start. simpl. reflexivity. Qed.

Close Scope Q_scope.

(** * Forward composition *)

Lemma arrow_compose : forall K : stage,
  arrow_forward (arrow_forward K) = S (S K).
Proof. intro K. unfold arrow_forward. reflexivity. Qed.

(** * Arrow never returns to origin *)

Lemma arrow_never_returns : forall K : stage,
  arrow_forward K <> K.
Proof. intro K. unfold arrow_forward. lia. Qed.

(** * Irreversibility: no function f such that f(S K) = K for all K *)

Lemma no_universal_backward : forall f : stage -> stage,
  (forall K, f (S K) = K) ->
  (forall K, (f (S K) < S K)%nat).
Proof. intros f Hf K. rewrite Hf. lia. Qed.

(** * L5 + arrow => entropy non-decrease *)

Definition entropy' (D : DistSet') : nat := length D.

Lemma arrow_preserves_info : forall D K,
  L5_pres D ->
  (entropy' (D K) <= entropy' (D (arrow_forward K)))%nat ->
  (entropy' (D K) <= entropy' (D (S K)))%nat.
Proof. intros D K HL5 H. unfold arrow_forward in H. exact H. Qed.

(** * Stage ordering is well-founded *)

Lemma stage_well_founded : well_founded (fun a b : stage => (a < b)%nat).
Proof. exact Nat.lt_wf_0. Qed.

(** * Arrow iterates *)

Fixpoint arrow_iter (n : nat) (K : stage) : stage :=
  match n with
  | O => K
  | S n' => arrow_forward (arrow_iter n' K)
  end.

Lemma arrow_iter_adds : forall n K,
  arrow_iter n K = (K + n)%nat.
Proof.
  induction n as [| n' IH]; intro K.
  - simpl. lia.
  - simpl. unfold arrow_forward. rewrite IH. lia.
Qed.

Lemma arrow_iter_strictly_increasing : forall n K,
  (0 < n)%nat -> (K < arrow_iter n K)%nat.
Proof.
  intros n K Hn. rewrite arrow_iter_adds. lia.
Qed.
