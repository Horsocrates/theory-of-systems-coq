(** * EntropyProcess.v -- Entropy as process: exact Q at each step
    Elements: fib, phi_process, h_golden_process, h_full_process
    Roles:    Entropy is a process {h_K}_K, not a single number h
    Rules:    Golden mean: h_K = ln(fib(K+1)/fib(K)), full shift: constant
    Status:   Stdlib
    STATUS: 20 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.LyapunovProcess.
From ToS Require Import stdlib.TopologicalEntropy.

Open Scope Q_scope.

(* ================================================================== *)
(*  FIBONACCI AND GOLDEN RATIO AS PROCESS                              *)
(* ================================================================== *)

(** Fibonacci sequence for golden mean shift *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | O => 1
  | S O => 2
  | S (S m as p) => fib p + fib m
  end.

Lemma fib_0 : fib 0 = 1%nat.  Proof. reflexivity. Qed.
Lemma fib_1 : fib 1 = 2%nat.  Proof. reflexivity. Qed.
Lemma fib_2 : fib 2 = 3%nat.  Proof. reflexivity. Qed.
Lemma fib_3 : fib 3 = 5%nat.  Proof. reflexivity. Qed.
Lemma fib_4 : fib 4 = 8%nat.  Proof. reflexivity. Qed.
Lemma fib_5 : fib 5 = 13%nat. Proof. reflexivity. Qed.
Lemma fib_6 : fib 6 = 21%nat. Proof. reflexivity. Qed.

(** Golden ratio as process: φ_K = fib(K+1)/fib(K) *)
Definition phi_process (K : nat) : Q :=
  inject_Z (Z.of_nat (fib (S K))) / inject_Z (Z.of_nat (fib K)).

Lemma phi_0 : phi_process 0 == 2.
Proof. unfold phi_process. simpl. reflexivity. Qed.

Lemma phi_1 : phi_process 1 == 3#2.
Proof. unfold phi_process. simpl. reflexivity. Qed.

Lemma phi_2 : phi_process 2 == 5#3.
Proof. unfold phi_process. simpl. reflexivity. Qed.

Lemma phi_3 : phi_process 3 == 8#5.
Proof. unfold phi_process. simpl. reflexivity. Qed.

Lemma phi_4 : phi_process 4 == 13#8.
Proof. unfold phi_process. simpl. reflexivity. Qed.

Lemma phi_5 : phi_process 5 == 21#13.
Proof. unfold phi_process. simpl. reflexivity. Qed.

(** φ process oscillates and converges:
    2, 1.5, 1.667, 1.6, 1.625, 1.615, ... → φ ≈ 1.618 *)

Lemma phi_oscillates : phi_process 0 > phi_process 1 /\
                       phi_process 1 < phi_process 2 /\
                       phi_process 2 > phi_process 3.
Proof.
  rewrite phi_0, phi_1, phi_2, phi_3. lra.
Qed.

(* ================================================================== *)
(*  ENTROPY PROCESSES                                                   *)
(* ================================================================== *)

(** Entropy of golden mean shift as process.
    h_K = ln(φ_K) via Padé: ln(x) ≈ 2(x-1)/(x+1) *)
Definition h_golden_process (K : nat) : Q :=
  let phi_K := phi_process K in
  2 * (phi_K - 1) / (phi_K + 1).

Lemma h_golden_0 : h_golden_process 0 == 2#3.
Proof. unfold h_golden_process, phi_process. simpl. reflexivity. Qed.

Lemma h_golden_1 : h_golden_process 1 == 2#5.
Proof. unfold h_golden_process, phi_process. simpl. reflexivity. Qed.

Lemma h_golden_2 : h_golden_process 2 == 1#2.
Proof. unfold h_golden_process, phi_process. simpl. reflexivity. Qed.

Lemma h_golden_3 : h_golden_process 3 == 6#13.
Proof. unfold h_golden_process, phi_process. simpl. reflexivity. Qed.

Lemma h_golden_4 : h_golden_process 4 == 10#21.
Proof. unfold h_golden_process, phi_process. simpl. reflexivity. Qed.

(** Entropy of full shift = constant process *)
Definition h_full_process (K : nat) : Q := ln2_approx.

(** Entropy of identity = zero process *)
Definition h_id_process (K : nat) : Q := 0.

(* ================================================================== *)
(*  COMPARISONS: decidable at finite step                              *)
(* ================================================================== *)

(** h(golden) < h(full): decidable at step 1 *)
Theorem golden_less_than_full_at_1 :
  h_golden_process 1 < h_full_process 1.
Proof. rewrite h_golden_1. unfold h_full_process, ln2_approx. lra. Qed.

(** h(golden) > h(identity): decidable at step 0 *)
Theorem golden_positive_at_0 :
  h_id_process 0 < h_golden_process 0.
Proof. rewrite h_golden_0. unfold h_id_process. lra. Qed.

(** fib is always positive *)
Lemma fib_pos_aux : forall n, (1 <= fib n /\ 1 <= fib (S n))%nat.
Proof.
  induction n as [|n' [IH1 IH2]].
  - simpl. lia.
  - split.
    + exact IH2.
    + destruct n' as [|n''].
      * simpl. lia.
      * change (fib (S (S (S n'')))) with (fib (S (S n'')) + fib (S n''))%nat.
        lia.
Qed.

Lemma fib_pos : forall n, (1 <= fib n)%nat.
Proof. intro n. exact (proj1 (fib_pos_aux n)). Qed.

(** fib(n+1) > fib(n) *)
Lemma fib_increasing : forall n, (fib n < fib (S n))%nat.
Proof.
  induction n as [|n' IH].
  - simpl. lia.
  - destruct n' as [|n''].
    + simpl. lia.
    + change (fib (S (S n'')) < fib (S (S (S n''))))%nat.
      change (fib (S (S (S n'')))) with (fib (S (S n'')) + fib (S n''))%nat.
      assert (H := fib_pos (S n'')). lia.
Qed.

(** h(golden) > 0 at concrete steps *)
Lemma golden_positive_0 : 0 < h_golden_process 0.
Proof. rewrite h_golden_0. lra. Qed.

Lemma golden_positive_1 : 0 < h_golden_process 1.
Proof. rewrite h_golden_1. lra. Qed.

Lemma golden_positive_2 : 0 < h_golden_process 2.
Proof. rewrite h_golden_2. lra. Qed.

Lemma golden_positive_3 : 0 < h_golden_process 3.
Proof. rewrite h_golden_3. lra. Qed.

Lemma golden_positive_4 : 0 < h_golden_process 4.
Proof. rewrite h_golden_4. lra. Qed.
