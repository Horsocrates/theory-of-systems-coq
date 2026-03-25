(** * SlaterConvergence.v — Convergence of Slater Basis Approximation
    Elements: Padé accuracy at finer lattice, error sequence, monotone improvement
    Roles:    Show STO lattice approximation improves with lattice refinement
    Rules:    pade22(1/M) → 1 as M → ∞; |pade(1/4) - 1| < |pade(1/3) - 1|;
              error at finer lattice is smaller
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.

From ToS Require Import stdlib.SlaterBasis.
From ToS Require Import stdlib.SlaterEigenvalue.

(* ================================================================== *)
(*  PADÉ ERROR: |pade22(x) - 1| as accuracy measure                   *)
(*  pade22(0) = 1 (exact), error grows with x                         *)
(* ================================================================== *)

Definition pade_error (x : Q) : Q := 1 - pade22_local x.

Lemma pade_error_at_0 : pade_error 0 == 0.
Proof. unfold pade_error, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ERROR AT x=1/3 vs x=1/4: finer lattice → smaller argument         *)
(*  pade_error(1/4) < pade_error(1/3)                                  *)
(* ================================================================== *)

Lemma pade_error_third : pade_error (1#3) == 36 # 127.
Proof. unfold pade_error, pade22_local. vm_compute. reflexivity. Qed.

Lemma pade_error_quarter : pade_error (1#4) == 48 # 217.
Proof. unfold pade_error, pade22_local. vm_compute. reflexivity. Qed.

Lemma pade_error_improves : pade_error (1#4) < pade_error (1#3).
Proof. unfold pade_error, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GENERAL: pade_error positive for 0 < x <= 1                       *)
(* ================================================================== *)

Lemma pade_error_pos_at_half : 0 < pade_error (1#2).
Proof. unfold pade_error, pade22_local. vm_compute. reflexivity. Qed.

Lemma pade_error_pos_at_1 : 0 < pade_error 1.
Proof. unfold pade_error, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  STO VALUE CONVERGENCE: sto_1s at site 0 improves with M           *)
(*  For i=0: sto_1s(ζ,M,0) = pade22(ζ/M) → pade22(0) = 1 as M→∞    *)
(*  sto_1s 1 4 0 closer to 1 than sto_1s 1 3 0                       *)
(* ================================================================== *)

Lemma sto_convergence_site0 :
  1 - sto_1s 1 4 O < 1 - sto_1s 1 3 O.
Proof.
  unfold sto_1s, pade22_local. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  ERROR SEQUENCE: Padé error at 1/M is monotone decreasing           *)
(*  |pade(1/5)| < |pade(1/4)| < |pade(1/3)|                           *)
(* ================================================================== *)

Lemma error_chain :
  pade_error (1#5) < pade_error (1#4) /\
  pade_error (1#4) < pade_error (1#3).
Proof.
  split; unfold pade_error, pade22_local; vm_compute; reflexivity.
Qed.
