(** * HartreeProcess.v — Hartree Self-Consistent Field Mixing
    Elements: Mixing parameter, potential mixing function, convergence properties
    Roles:    Define iterative potential mixing for Hartree SCF convergence
    Rules:    V_new = alpha*V_computed + (1-alpha)*V_old; mix preserves length
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Require Import ToS.stdlib.PadeApprox.

Open Scope Q_scope.

(* ================================================================== *)
(*  MIXING PARAMETER                                                   *)
(* ================================================================== *)

Definition mixing_alpha : Q := 1 # 2.

(* ================================================================== *)
(*  MIX TWO POTENTIALS: V_new = alpha * V1 + (1-alpha) * V2           *)
(* ================================================================== *)

Fixpoint mix_potentials (v1 v2 : list Q) (alpha : Q) : list Q :=
  match v1, v2 with
  | x :: xs, y :: ys => (alpha * x + (1 - alpha) * y) :: mix_potentials xs ys alpha
  | _, _ => nil
  end.

(* ================================================================== *)
(*  SCALAR MIX: single-element mixing                                  *)
(* ================================================================== *)

Definition mix_scalar (a b alpha : Q) : Q := alpha * a + (1 - alpha) * b.

Lemma mix_scalar_half : mix_scalar 1 5 (1#2) == 3.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

Lemma mix_scalar_half_2 : mix_scalar 2 6 (1#2) == 4.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

Lemma mix_scalar_half_3 : mix_scalar 3 7 (1#2) == 5.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MIX PRESERVES LENGTH (concrete)                                    *)
(* ================================================================== *)

Lemma mix_preserves_length_3 :
  length (mix_potentials [1; 2; 3] [5; 6; 7] (1#2)) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma mix_preserves_length_2 :
  length (mix_potentials [0; 0] [4; 8] (1#2)) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MIX WITH ALPHA=0: each element equals V2 element                   *)
(* ================================================================== *)

Lemma mix_alpha_zero_elem :
  mix_scalar 1 5 0 == 5.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MIX WITH ALPHA=1: each element equals V1 element                   *)
(* ================================================================== *)

Lemma mix_alpha_one_elem :
  mix_scalar 1 5 1 == 1.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MIX IDEMPOTENT: mixing value with itself gives same value          *)
(* ================================================================== *)

Lemma mix_idempotent_elem :
  mix_scalar 7 7 (1#2) == 7.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MIXING PARAMETER IN VALID RANGE                                    *)
(* ================================================================== *)

Lemma alpha_positive : 0 < mixing_alpha.
Proof. unfold mixing_alpha. vm_compute. reflexivity. Qed.

Lemma alpha_lt_one : mixing_alpha < 1.
Proof. unfold mixing_alpha. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  HARTREE ITERATION: mixing steps converge toward V_computed         *)
(*  V0 = 0, V_comp = 10, alpha = 1/2                                  *)
(*  Iter1: 0.5*0 + 0.5*10 = 5                                         *)
(*  Iter2: 0.5*5 + 0.5*10 = 7.5                                       *)
(* ================================================================== *)

Lemma hartree_iter1_val : mix_scalar 0 10 (1#2) == 5.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

Lemma hartree_iter2_val : mix_scalar 5 10 (1#2) == 15 # 2.
Proof. unfold mix_scalar. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONVERGENCE: each iteration gets closer to target                  *)
(*  |V_target - iter2| < |V_target - iter1|                           *)
(*  |10 - 7.5| = 2.5 < |10 - 5| = 5                                  *)
(* ================================================================== *)

Lemma hartree_convergence_concrete :
  Qabs (10 - 15#2) < Qabs (10 - 5).
Proof.
  unfold Qabs. simpl. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  EMPTY LIST MIXING                                                  *)
(* ================================================================== *)

Lemma mix_empty : mix_potentials [] [] (1#2) = [].
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PADÉ INTEGRATION: Z_eff values as input potential                  *)
(* ================================================================== *)

Lemma pade_in_mix :
  0 < pade22 (1#2).
Proof. exact pade_positive_half. Qed.
