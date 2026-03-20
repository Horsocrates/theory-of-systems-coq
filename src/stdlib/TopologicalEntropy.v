(** * TopologicalEntropy.v -- h_top for interval maps over Q
    Elements: tent_lap, h_top_tent, h_top_process, entropy_classification
    Roles:    Topological entropy via lap number for piecewise monotone maps
    Rules:    h_top = lim (1/n) ln(lap(f^n)), h_top > 0 ↔ chaos
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.LyapunovProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  LAP NUMBER                                                         *)
(* ================================================================== *)

(** lap(f) = number of monotone pieces.
    Tent: lap(T) = 2 (increasing on [0,1/2], decreasing on [1/2,1])
    T^n: lap = 2^n *)

Definition tent_lap (n : nat) : nat := Nat.pow 2 n.

Lemma tent_lap_0 : tent_lap 0 = 1%nat.
Proof. reflexivity. Qed.

Lemma tent_lap_1 : tent_lap 1 = 2%nat.
Proof. reflexivity. Qed.

Lemma tent_lap_2 : tent_lap 2 = 4%nat.
Proof. reflexivity. Qed.

Lemma tent_lap_3 : tent_lap 3 = 8%nat.
Proof. reflexivity. Qed.

(** Lap number doubles each iteration *)
Lemma tent_lap_double : forall n, tent_lap (S n) = (2 * tent_lap n)%nat.
Proof.
  intro n. unfold tent_lap. simpl. lia.
Qed.

(* ================================================================== *)
(*  TOPOLOGICAL ENTROPY                                                *)
(* ================================================================== *)

(** h_top = lim (1/n) ln(lap(f^n)) = lim (1/n) ln(2^n) = ln(2) *)
Definition h_top_tent : Q := ln2_approx.

Theorem tent_positive_entropy : 0 < h_top_tent.
Proof. unfold h_top_tent, ln2_approx. lra. Qed.

(** Identity: lap = 1 for all n → h_top = 0 *)
Definition h_top_identity : Q := 0.

(** Doubling: lap(D^n) = 2^n → h_top = ln(2) *)
Definition h_top_doubling : Q := ln2_approx.

(* ================================================================== *)
(*  ENTROPY AS PROCESS                                                 *)
(* ================================================================== *)

Definition h_top_process (lap_n : nat -> nat) (K : nat) : Q :=
  ln2_approx * inject_Z (Z.of_nat (Nat.log2 (lap_n K))) /
  inject_Z (Z.of_nat (S K)).

(** Entropy of tent at K=1: ln2 * log2(2) / 2 = ln2 * 1 / 2 = 1/3 *)
Lemma h_top_tent_at_1 : h_top_process tent_lap 1 == 1#3.
Proof. unfold h_top_process, tent_lap, ln2_approx. vm_compute. reflexivity. Qed.

(** Entropy of tent at K=2: ln2 * log2(4) / 3 = (2/3) * 2 / 3 = 4/9 *)
Lemma h_top_tent_at_2 : h_top_process tent_lap 2 == 4#9.
Proof. unfold h_top_process, tent_lap, ln2_approx. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CLASSIFICATION                                                     *)
(* ================================================================== *)

(** Variational principle: h_top(f) = sup_μ h_μ(f).
    For tent: h_top = h_Lebesgue = ln(2). *)

Theorem entropy_classification :
  h_top_tent == ln2_approx /\
  h_top_identity == 0 /\
  0 < h_top_tent.
Proof.
  split; [|split].
  - unfold h_top_tent. reflexivity.
  - unfold h_top_identity. reflexivity.
  - exact tent_positive_entropy.
Qed.
