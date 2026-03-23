(** * BerryPhase.v -- Berry phase from cyclic ground state evolution
    Elements: ground states gs_0..gs_3, overlaps, Berry product
    Roles:    Berry phase = arg of product of overlaps around a cycle
    Rules:    Product = -1 → phase = pi → spinor behavior (sign flip per cycle)
    Status:   Stdlib
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessHilbert.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: GROUND STATES AT FOUR PARAMETER VALUES                     *)
(* ================================================================== *)

(* Paramagnetic chain with varying field direction *)
Definition gs_0 : PState := [0; 1].     (* |down> *)
Definition gs_1 : PState := [1; -(1)].  (* |+> - |-> *)
Definition gs_2 : PState := [1; 0].     (* |up> *)
Definition gs_3 : PState := [1; 1].     (* |+> + |-> *)

(* ================================================================== *)
(*  PART II: OVERLAPS (inner products)                                  *)
(* ================================================================== *)

Lemma overlap_01 : inner gs_0 gs_1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_12 : inner gs_1 gs_2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_23 : inner gs_2 gs_3 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_30 : inner gs_3 gs_0 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: BERRY PRODUCT = product of overlaps around cycle          *)
(* ================================================================== *)

Definition berry_product : Q :=
  inner gs_0 gs_1 * inner gs_1 gs_2 * inner gs_2 gs_3 * inner gs_3 gs_0.

Lemma berry_product_eq : berry_product == -(1).
Proof. vm_compute. reflexivity. Qed.

(* Berry phase = arg(-1) = pi *)
(* State acquires factor of -1 after one cycle *)

(* ================================================================== *)
(*  PART IV: TWO CYCLES → +1 (spinor double cover)                    *)
(* ================================================================== *)

Definition double_cycle : Q := berry_product * berry_product.

Lemma double_cycle_eq : double_cycle == 1.
Proof. vm_compute. reflexivity. Qed.

(* Two complete parameter cycles restore the original sign *)
(* This is the hallmark of spinor behavior: 2pi rotation = identity *)

(* ================================================================== *)
(*  PART V: NORM COMPUTATIONS                                          *)
(* ================================================================== *)

Lemma norm_gs_0 : norm_sq gs_0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_gs_1 : norm_sq gs_1 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_gs_2 : norm_sq gs_2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_gs_3 : norm_sq gs_3 == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART VI: ORTHOGONALITY                                              *)
(* ================================================================== *)

Lemma gs_02_orthogonal : inner gs_0 gs_2 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma gs_13_inner : inner gs_1 gs_3 == 0.
Proof. vm_compute. reflexivity. Qed.

(* gs_0 ⊥ gs_2 and gs_1 ⊥ gs_3: antipodal states are orthogonal *)

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem berry_phase_synthesis :
  (* Overlaps *)
  inner gs_0 gs_1 == -(1) /\
  inner gs_1 gs_2 == 1 /\
  inner gs_2 gs_3 == 1 /\
  inner gs_3 gs_0 == 1 /\
  (* Berry product = -1 *)
  berry_product == -(1) /\
  (* Double cycle = +1 (spinor) *)
  double_cycle == 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
