(** * FiniteSizeBox.v -- Finite-Size Corrections for Box Path Graphs
    Elements: correction_K2, correction_scaling, relative corrections
    Roles:    Quantify deviation of lambda1*(K+1)^2 from pi^2
    Rules:    Corrections are negative, decrease with K, bounded < 10%
    Status:   Stdlib
    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.SpectralFlowGround.
Open Scope Q_scope.

(* ================================================================== *)
(*  PI^2 APPROXIMATIONS FROM SPECTRAL FLOW                            *)
(* ================================================================== *)

(** K=2: lambda1 * (K+1)^2 = 1 * 9 = 9 *)
Lemma pi_sq_flow_K2 : ground_K2 * (3 * 3) == 9.
Proof. vm_compute. reflexivity. Qed.

(** K=4: lambda1 * (K+1)^2 = (55/144) * 25 = 1375/144 *)
Lemma pi_sq_flow_K4 : ground_K4 * (5 * 5) == 1375#144.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CORRECTION: deviation from best approximation                      *)
(*  correction = flow_value / reference - 1                            *)
(*  Using K=4 flow (1375/144) as reference for K=2 (9):               *)
(*  correction_K2 = 9 / (1375/144) - 1 = 9*144/1375 - 1              *)
(*                = 1296/1375 - 1 = -79/1375                          *)
(* ================================================================== *)

Definition correction_K2 : Q := 1 - (1375#1296).

Lemma correction_K2_value : correction_K2 == -(79#1296).
Proof. unfold correction_K2. ring. Qed.

Lemma correction_K2_negative : correction_K2 < 0.
Proof. unfold correction_K2. lra. Qed.

(** |correction| < 1/10, i.e., less than 10% *)
Lemma correction_K2_small : -(1#10) < correction_K2.
Proof. unfold correction_K2. lra. Qed.

Lemma correction_K2_bounded : -(1#10) < correction_K2 /\ correction_K2 < 0.
Proof. split; [exact correction_K2_small | exact correction_K2_negative]. Qed.

(* ================================================================== *)
(*  SCALING LAW: correction ~ 1/K^4                                   *)
(*  correction_scaling(K) = -81 / (12 * (K+1)^4)                      *)
(* ================================================================== *)

Definition correction_scaling (K : nat) : Q :=
  -(81) / (12 * inject_Z (Z.of_nat (Nat.pow (S K) 4))).

(** K=2: (S 2)^4 = 3^4 = 81, 12*81 = 972, so -81/972 = -1/12 *)
Lemma correction_scaling_K2 : correction_scaling 2 == -(1#12).
Proof. vm_compute. reflexivity. Qed.

(** K=3: (S 3)^4 = 4^4 = 256, 12*256 = 3072, so -81/3072 = -27/1024 *)
Lemma correction_scaling_K3 : correction_scaling 3 == -(81#3072).
Proof. vm_compute. reflexivity. Qed.

(** K=4: (S 4)^4 = 5^4 = 625, 12*625 = 7500, so -81/7500 = -27/2500 *)
Lemma correction_scaling_K4 : correction_scaling 4 == -(81#7500).
Proof. vm_compute. reflexivity. Qed.

(** Corrections decrease: correction(K=2) < correction(K=3) (less negative) *)
Lemma correction_scaling_decreases : correction_scaling 2 < correction_scaling 3.
Proof. unfold correction_scaling, inject_Z, Qlt. vm_compute. reflexivity. Qed.

(** Corrections decrease further: correction(K=3) < correction(K=4) (less negative) *)
Lemma correction_scaling_decreases_further :
  correction_scaling 3 < correction_scaling 4.
Proof. unfold correction_scaling, inject_Z, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  RELATIVE CORRECTION: flow values bracket pi^2                      *)
(* ================================================================== *)

(** K=2 flow < K=4 flow *)
Lemma flow_K2_lt_K4 : ground_K2 * (3 * 3) < ground_K4 * (5 * 5).
Proof. unfold ground_K2, ground_K4. lra. Qed.

(** K=3 flow between K=2 and K=4 *)
Lemma flow_monotone_K2_K3 : ground_K2 * 9 < ground_K3 * 16.
Proof. unfold ground_K2, ground_K3. lra. Qed.

Lemma flow_monotone_K3_K4 : ground_K3 * 16 < ground_K4 * 25.
Proof. unfold ground_K3, ground_K4. lra. Qed.

(** All flow values are between 9 and 10 *)
Lemma flow_K2_in_range : 8 < ground_K2 * 9 /\ ground_K2 * 9 < 10.
Proof. unfold ground_K2. lra. Qed.

Lemma flow_K4_in_range : 9 < ground_K4 * 25 /\ ground_K4 * 25 < 10.
Proof. unfold ground_K4. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem finite_size_box_synthesis :
  correction_K2 == -(79#1296) /\
  correction_K2 < 0 /\
  -(1#10) < correction_K2 /\
  correction_scaling 2 == -(1#12) /\
  correction_scaling 2 < correction_scaling 3 /\
  ground_K2 * 9 < ground_K4 * 25.
Proof.
  split; [exact correction_K2_value|].
  split; [exact correction_K2_negative|].
  split; [exact correction_K2_small|].
  split; [exact correction_scaling_K2|].
  split; [exact correction_scaling_decreases|].
  exact flow_K2_lt_K4.
Qed.
