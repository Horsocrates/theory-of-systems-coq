(** * PadeApprox.v — Padé [2,2] Approximant for exp(-x)
    Elements: Padé numerator P(x), denominator Q(x), rational approximant
    Roles:    Provide accurate rational approximation to exp(-x) for screening
    Rules:    pade22(x) = (12 - 6x + x²)/(12 + 6x + x²); pade22(0) = 1
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  PADÉ [2,2] APPROXIMANT FOR exp(-x)                                *)
(*  P(x) = 12 - 6x + x²                                              *)
(*  Q(x) = 12 + 6x + x²                                              *)
(*  pade22(x) = P(x)/Q(x)                                             *)
(* ================================================================== *)

Definition pade_num (x : Q) : Q := 12 - 6 * x + x * x.

Definition pade_den (x : Q) : Q := 12 + 6 * x + x * x.

Definition pade22 (x : Q) : Q := pade_num x / pade_den x.

(* ================================================================== *)
(*  CONCRETE EVALUATION: pade22(0) = 1                                 *)
(* ================================================================== *)

Lemma pade_num_at_0 : pade_num 0 == 12.
Proof. unfold pade_num. ring. Qed.

Lemma pade_den_at_0 : pade_den 0 == 12.
Proof. unfold pade_den. ring. Qed.

Lemma pade_at_0 : pade22 0 == 1.
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE EVALUATION: pade22(1) = 7/19                              *)
(*  P(1) = 12 - 6 + 1 = 7, Q(1) = 12 + 6 + 1 = 19                   *)
(* ================================================================== *)

Lemma pade_num_at_1 : pade_num 1 == 7.
Proof. unfold pade_num. ring. Qed.

Lemma pade_den_at_1 : pade_den 1 == 19.
Proof. unfold pade_den. ring. Qed.

Lemma pade_at_1 : pade22 1 == 7 # 19.
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE EVALUATION: pade22(1/2) = 37/61                           *)
(*  P(1/2) = 12 - 3 + 1/4 = 37/4                                     *)
(*  Q(1/2) = 12 + 3 + 1/4 = 61/4                                     *)
(* ================================================================== *)

Lemma pade_at_half : pade22 (1#2) == 37 # 61.
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE EVALUATION: pade22(2) = 1/7                               *)
(*  P(2) = 12 - 12 + 4 = 4, Q(2) = 12 + 12 + 4 = 28                 *)
(*  4/28 = 1/7                                                        *)
(* ================================================================== *)

Lemma pade_at_2 : pade22 2 == 1 # 7.
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  POSITIVITY: pade22(1/2) > 0                                        *)
(* ================================================================== *)

Lemma pade_positive_half : 0 < pade22 (1#2).
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  MONOTONE DECREASE: pade22(1) < pade22(1/2)                         *)
(* ================================================================== *)

Lemma pade_decreasing : pade22 1 < pade22 (1#2).
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SYMMETRY AT ORIGIN: pade22(0) = 1 = exp(0)                        *)
(* ================================================================== *)

Lemma pade_symmetry : pade22 0 == 1.
Proof. exact pade_at_0. Qed.

(* ================================================================== *)
(*  ACCURACY: pade22(1/10) = 1141/1261 ≈ 0.9048                       *)
(*  exp(-0.1) ≈ 0.9048                                                *)
(* ================================================================== *)

Lemma pade_at_tenth : pade22 (1#10) == 1141 # 1261.
Proof.
  unfold pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.
