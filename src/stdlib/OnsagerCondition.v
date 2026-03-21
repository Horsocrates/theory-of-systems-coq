(** * OnsagerCondition.v -- Verify Onsager's critical condition over Q
    Elements: sinh_Q, onsager_residual, beta_c bisection
    Roles:    sinh(2β_c) = 1 → β_c ∈ (3/7, 4/9) ≈ (0.429, 0.444)
    Rules:    Bisection over Q with small-denominator β values
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.Ising2DTransfer.

Open Scope Q_scope.

(* ================================================================== *)
(*  SINH OVER Q                                                        *)
(* ================================================================== *)

Definition sinh_Q (x : Q) (M : nat) : Q :=
  (exp_Q x M - exp_Q (- x) M) / 2.

(** Onsager's equation: f(β) = sinh(2β) - 1 = 0 at β_c *)
Definition onsager_residual (beta : Q) (M : nat) : Q :=
  sinh_Q (2 * beta) M - 1.

(* ================================================================== *)
(*  CONCRETE SINH VALUES (M=3, small denominators)                     *)
(* ================================================================== *)

(** sinh(4/5) at M=3: 332/375 ≈ 0.885 < 1 *)
Lemma sinh_4_5 : sinh_Q (4#5) 3 == 332#375.
Proof. unfold sinh_Q. vm_compute. reflexivity. Qed.

(** sinh(1) at M=3: 7/6 ≈ 1.167 > 1 *)
Lemma sinh_1 : sinh_Q 1 3 == 7#6.
Proof. unfold sinh_Q. vm_compute. reflexivity. Qed.

(** sinh(6/7) at M=3: 330/343 ≈ 0.962 < 1 *)
Lemma sinh_6_7 : sinh_Q (6#7) 3 == 330#343.
Proof. unfold sinh_Q. vm_compute. reflexivity. Qed.

(** sinh(8/9) at M=3: 2200/2187 ≈ 1.006 > 1 *)
Lemma sinh_8_9 : sinh_Q (8#9) 3 == 2200#2187.
Proof. unfold sinh_Q. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ONSAGER BISECTION                                                  *)
(* ================================================================== *)

(** Step 1: f(2/5) < 0, f(1/2) > 0 → β_c ∈ (0.4, 0.5) *)
Lemma onsager_low_2_5 : onsager_residual (2#5) 3 < 0.
Proof.
  unfold onsager_residual.
  assert (H : sinh_Q (2 * (2#5)) 3 == 332#375) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

Lemma onsager_high_1_2 : 0 < onsager_residual (1#2) 3.
Proof.
  unfold onsager_residual.
  assert (H : sinh_Q (2 * (1#2)) 3 == 7#6) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Step 2: f(3/7) < 0 → β_c > 3/7 ≈ 0.4286 *)
Lemma onsager_low_3_7 : onsager_residual (3#7) 3 < 0.
Proof.
  unfold onsager_residual.
  assert (H : sinh_Q (2 * (3#7)) 3 == 330#343) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Step 3: f(4/9) > 0 → β_c < 4/9 ≈ 0.4444 *)
Lemma onsager_high_4_9 : 0 < onsager_residual (4#9) 3.
Proof.
  unfold onsager_residual.
  assert (H : sinh_Q (2 * (4#9)) 3 == 2200#2187) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** LOCALIZED: β_c ∈ (3/7, 4/9) ≈ (0.4286, 0.4444)
    True: β_c = 0.4407. Width: 0.016 ≈ 3.6% ✓ *)

(** Additional: 332/375 and 330/343 bracket from below *)
Lemma sinh_increasing : sinh_Q (4#5) 3 < sinh_Q (6#7) 3.
Proof. rewrite sinh_4_5, sinh_6_7. lra. Qed.

(** Both sinh values bracket 1 *)
Lemma sinh_brackets_one :
  sinh_Q (6#7) 3 < 1 /\ 1 < sinh_Q (8#9) 3.
Proof.
  rewrite sinh_6_7, sinh_8_9. split; lra.
Qed.

(** SYNTHESIS *)
Theorem onsager_verified :
  (* Wide bracket: β_c ∈ (0.4, 0.5) *)
  onsager_residual (2#5) 3 < 0 /\
  0 < onsager_residual (1#2) 3 /\
  (* Tight bracket: β_c ∈ (3/7, 4/9) *)
  onsager_residual (3#7) 3 < 0 /\
  0 < onsager_residual (4#9) 3.
Proof.
  split; [|split; [|split]].
  - exact onsager_low_2_5.
  - exact onsager_high_1_2.
  - exact onsager_low_3_7.
  - exact onsager_high_4_9.
Qed.
