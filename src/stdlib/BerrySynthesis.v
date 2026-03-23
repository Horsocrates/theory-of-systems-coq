(** * BerrySynthesis.v -- Grand synthesis: Berry phase + quaternion connection
    Elements: Berry product, double cycle, quaternion i^2 = -I
    Roles:    -1 from Berry cycle ↔ i^2 = -1 from quaternion algebra
    Rules:    Both arise from distinction: 2-sided → i; 3-sided → H; cycle → spinor
    Status:   Stdlib
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.BerryPhase.
From ToS Require Import stdlib.QuaternionFromDistinction.
From ToS Require Import stdlib.ProcessHilbert.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: BERRY PHASE RECAP                                          *)
(* ================================================================== *)

Lemma berry_minus_one : berry_product == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma spinor_double : double_cycle == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART II: QUATERNION i^2 = -1 RECAP                                  *)
(* ================================================================== *)

Lemma quat_i_sq_diag : mat4_mul quat_i quat_i O O == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: CROSS-CONNECTIONS                                         *)
(* ================================================================== *)

(* The -1 in Berry phase and i^2 = -1 are the SAME -1:               *)
(* Berry: cyclic evolution through parameter space → sign flip         *)
(* Quaternion: double application of 90° rotation → 180° = negation   *)
(* Both reflect the fundamental half-turn property of spinors          *)

Lemma berry_eq_i_squared :
  berry_product == mat4_mul quat_i quat_i O O.
Proof. vm_compute. reflexivity. Qed.

(* Orthogonality of antipodal states mirrors quaternion anticommutativity *)
Lemma antipodal_orthogonal :
  inner gs_0 gs_2 == 0 /\ inner gs_1 gs_3 == 0.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: BORN PROBABILITIES FROM BERRY STATES                       *)
(* ================================================================== *)

(* Measuring gs_1 = [1;-1] in the gs_2 = [1;0] basis *)
Lemma born_gs2_in_gs1 : born_prob gs_2 gs_1 == (1#2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

Theorem berry_quaternion_grand_synthesis :
  (* Berry phase = -1 *)
  berry_product == -(1) /\
  (* Double cycle = +1 (spinor) *)
  double_cycle == 1 /\
  (* Quaternion i^2 = -1 at (0,0) *)
  mat4_mul quat_i quat_i O O == -(1) /\
  (* Berry = i^2 *)
  berry_product == mat4_mul quat_i quat_i O O /\
  (* Antipodal orthogonality *)
  inner gs_0 gs_2 == 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
