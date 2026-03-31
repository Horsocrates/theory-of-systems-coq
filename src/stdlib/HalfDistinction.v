(** * HalfDistinction.v -- Half-Distinction: i^k as 2x2 rotation on Q
    Elements: i_power, half_turn, quarter_turn
    Roles:    i^k cycles through {I, i, -I, -i} with period 4
    Rules:    Quarter-turn = half a distinction; two quarter-turns = negation
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.ComplexOverQ.

Open Scope Q_scope.

(* ================================================================== *)
(*  i^n AS MATRIX POWER (period 4)                                     *)
(* ================================================================== *)

(** i_power n = C_i raised to the n-th power using mat2_pow *)
Definition i_power (n : nat) : Mat2 := mat2_pow C_i n.

(** quarter_turn = i^1, half_turn = i^2 *)
Definition quarter_turn : Mat2 := i_power 1.
Definition half_turn : Mat2 := i_power 2.

(* ================================================================== *)
(*  i^0 = I (identity)                                                 *)
(* ================================================================== *)

Lemma i_pow_0_00 : i_power 0 0%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_0_01 : i_power 0 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_0_10 : i_power 0 1%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_0_11 : i_power 0 1%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  i^1 = i (quarter turn)                                             *)
(* ================================================================== *)

Lemma i_pow_1_00 : i_power 1 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_1_01 : i_power 1 0%nat 1%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_1_10 : i_power 1 1%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  i^2 = -I (half turn = negation)                                    *)
(* ================================================================== *)

Lemma i_pow_2_00 : i_power 2 0%nat 0%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_2_11 : i_power 2 1%nat 1%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  i^4 = I (full cycle, period 4)                                     *)
(* ================================================================== *)

Lemma i_pow_4_00 : i_power 4 0%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_4_11 : i_power 4 1%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma i_pow_4_01 : i_power 4 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Period-4 cycle: i^0 = i^4                                          *)
(* ================================================================== *)

Lemma period_4_00 : i_power 0 0%nat 0%nat == i_power 4 0%nat 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma period_4_11 : i_power 0 1%nat 1%nat == i_power 4 1%nat 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Two quarter-turns = negation                                        *)
(* ================================================================== *)

Lemma two_quarters_negate :
  half_turn 0%nat 0%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Synthesis: half-distinction is the square root of negation          *)
(* ================================================================== *)

Theorem half_distinction_synthesis :
  (* i is a quarter turn *)
  quarter_turn 0%nat 0%nat == 0 /\
  quarter_turn 1%nat 0%nat == 1 /\
  (* i^2 is negation *)
  half_turn 0%nat 0%nat == -(1) /\
  (* i^4 is identity *)
  i_power 4 0%nat 0%nat == 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
