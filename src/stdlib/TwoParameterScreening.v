(** * TwoParameterScreening.v — Two-Parameter Screening Model
    Elements: Z_eff with two Padé terms, He/Li parameter sets, constraints
    Roles:    Extend single-parameter screening to two-term model for accuracy
    Rules:    Z_eff_two = 1 + c1*pade22(i/(r1*M)) + c2*pade22(i/(r2*M))
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Require Import ToS.stdlib.PadeApprox.

Open Scope Q_scope.

(* ================================================================== *)
(*  TWO-PARAMETER EFFECTIVE CHARGE                                     *)
(*  Z_eff = 1 + c1 * pade22(i/(r1*M)) + c2 * pade22(i/(r2*M))       *)
(* ================================================================== *)

Definition Z_eff_two (c1 c2 r1 r2 M i : Q) : Q :=
  1 + c1 * pade22 (i / (r1 * M)) + c2 * pade22 (i / (r2 * M)).

(* ================================================================== *)
(*  HELIUM PARAMETERS                                                  *)
(* ================================================================== *)

Definition he_c1 : Q := 7 # 10.
Definition he_c2 : Q := 3 # 10.
Definition he_r1 : Q := 1 # 5.
Definition he_r2 : Q := 1 # 2.

(* ================================================================== *)
(*  LITHIUM PARAMETERS                                                 *)
(* ================================================================== *)

Definition li_c1 : Q := 3 # 2.
Definition li_c2 : Q := 1 # 2.
Definition li_r1 : Q := 3 # 20.
Definition li_r2 : Q := 3 # 5.

(* ================================================================== *)
(*  CONSTRAINT: He coefficients sum to 1 (Z-1 = 2-1 = 1)              *)
(* ================================================================== *)

Lemma he_constraint : he_c1 + he_c2 == 1.
Proof.
  unfold he_c1, he_c2. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CONSTRAINT: Li coefficients sum to 2 (Z-1 = 3-1 = 2)              *)
(* ================================================================== *)

Lemma li_constraint : li_c1 + li_c2 == 2.
Proof.
  unfold li_c1, li_c2. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  He Z_eff at site 0 (pade22(0) = 1): Z_eff = 1 + 0.7 + 0.3 = 2   *)
(* ================================================================== *)

Lemma he_Z_eff_site0 : Z_eff_two he_c1 he_c2 he_r1 he_r2 10 0 == 2.
Proof.
  unfold Z_eff_two, he_c1, he_c2, he_r1, he_r2, pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Li Z_eff at site 0: Z_eff = 1 + 1.5 + 0.5 = 3                    *)
(* ================================================================== *)

Lemma li_Z_eff_site0 : Z_eff_two li_c1 li_c2 li_r1 li_r2 10 0 == 3.
Proof.
  unfold Z_eff_two, li_c1, li_c2, li_r1, li_r2, pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  He parameters are positive                                         *)
(* ================================================================== *)

Lemma he_c1_positive : 0 < he_c1.
Proof. unfold he_c1. vm_compute. reflexivity. Qed.

Lemma he_c2_positive : 0 < he_c2.
Proof. unfold he_c2. vm_compute. reflexivity. Qed.

Lemma he_r1_positive : 0 < he_r1.
Proof. unfold he_r1. vm_compute. reflexivity. Qed.

Lemma he_r2_positive : 0 < he_r2.
Proof. unfold he_r2. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Li parameters are positive                                         *)
(* ================================================================== *)

Lemma li_c1_positive : 0 < li_c1.
Proof. unfold li_c1. vm_compute. reflexivity. Qed.

Lemma li_c2_positive : 0 < li_c2.
Proof. unfold li_c2. vm_compute. reflexivity. Qed.

Lemma li_r1_positive : 0 < li_r1.
Proof. unfold li_r1. vm_compute. reflexivity. Qed.

Lemma li_r2_positive : 0 < li_r2.
Proof. unfold li_r2. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  He Z_eff at site 0 is positive                                     *)
(* ================================================================== *)

Lemma he_Z_eff_positive : 0 < Z_eff_two he_c1 he_c2 he_r1 he_r2 10 0.
Proof.
  unfold Z_eff_two, he_c1, he_c2, he_r1, he_r2, pade22, pade_num, pade_den.
  vm_compute. reflexivity.
Qed.
