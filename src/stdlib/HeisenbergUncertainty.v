(** * HeisenbergUncertainty.v — State-Dependent Uncertainty on Finite Lattice
    Elements: comm_exp_K2, comm_exp_K3, uncertainty bounds
    Roles:    Finite-lattice uncertainty = |<[X,P]>|/2, state-dependent
    Rules:    K=2 bound = 1/2 (standard); K=3 bound = 2/3 (exceeds standard!)
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessHilbert.
From ToS Require Import stdlib.HeisenbergReturn.
Open Scope Q_scope.

(* ================================================================== *)
(*  COMMUTATOR EXPECTATION FOR UNIFORM STATES                          *)
(*  <psi|[X,P]|psi> / <psi|psi> for psi = (1,1,...,1)                 *)
(* ================================================================== *)

(** K=2, psi = (1,1): <psi|[X,P]|psi> / <psi|psi> *)
Definition comm_exp_K2 : Q :=
  let c00 := XP_comm 2 0 0 in let c01 := XP_comm 2 0 1 in
  let c10 := XP_comm 2 1 0 in let c11 := XP_comm 2 1 1 in
  let v0 := c00 * 1 + c01 * 1 in
  let v1 := c10 * 1 + c11 * 1 in
  (1 * v0 + 1 * v1) / (1 * 1 + 1 * 1).

Lemma comm_exp_K2_value : comm_exp_K2 == -(1).
Proof. vm_compute. reflexivity. Qed.

(** K=3, psi = (1,1,1): <psi|[X,P]|psi> / <psi|psi> *)
Definition comm_exp_K3 : Q :=
  let v0 := XP_comm 3 0 0 * 1 + XP_comm 3 0 1 * 1 + XP_comm 3 0 2 * 1 in
  let v1 := XP_comm 3 1 0 * 1 + XP_comm 3 1 1 * 1 + XP_comm 3 1 2 * 1 in
  let v2 := XP_comm 3 2 0 * 1 + XP_comm 3 2 1 * 1 + XP_comm 3 2 2 * 1 in
  (1 * v0 + 1 * v1 + 1 * v2) / (1 * 1 + 1 * 1 + 1 * 1).

Lemma comm_exp_K3_value : comm_exp_K3 == -(4#3).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  UNCERTAINTY BOUND: Delta_X * Delta_P >= |<[X,P]>| / 2              *)
(* ================================================================== *)

(** Uncertainty bound = |<[X,P]>| / 2 *)
Definition uncertainty_bound_K2 : Q := Qabs comm_exp_K2 / 2.
Definition uncertainty_bound_K3 : Q := Qabs comm_exp_K3 / 2.

Lemma uncertainty_K2 : uncertainty_bound_K2 == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma uncertainty_K3 : uncertainty_bound_K3 == (2#3).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=3 EXCEEDS STANDARD BOUND                                         *)
(* ================================================================== *)

(** The finite-lattice uncertainty bound exceeds the standard hbar/2 *)
Lemma finite_uncertainty_exceeds_standard :
  uncertainty_bound_K3 - (1#2) == (1#6).
Proof. vm_compute. reflexivity. Qed.

Lemma uncertainty_K3_gt_half : (1#2) < uncertainty_bound_K3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COMMUTATOR EXPECTATION FOR LOCALIZED STATE                          *)
(*  psi = (1,0,0) at K=3: only site 0                                  *)
(* ================================================================== *)

Definition comm_exp_K3_localized : Q :=
  let v0 := XP_comm 3 0 0 * 1 + XP_comm 3 0 1 * 0 + XP_comm 3 0 2 * 0 in
  let v1 := XP_comm 3 1 0 * 1 + XP_comm 3 1 1 * 0 + XP_comm 3 1 2 * 0 in
  let v2 := XP_comm 3 2 0 * 1 + XP_comm 3 2 1 * 0 + XP_comm 3 2 2 * 0 in
  (1 * v0 + 0 * v1 + 0 * v2) / (1 * 1 + 0 * 0 + 0 * 0).

Lemma comm_exp_K3_localized_value : comm_exp_K3_localized == 0.
Proof. vm_compute. reflexivity. Qed.

(** Localized state sees zero commutator — pure boundary effect *)
Lemma uncertainty_localized_is_zero :
  Qabs comm_exp_K3_localized / 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  STATE DEPENDENCE                                                    *)
(* ================================================================== *)

Lemma state_dependence :
  ~(comm_exp_K3 == comm_exp_K3_localized).
Proof.
  intro H. vm_compute in H. discriminate.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem heisenberg_uncertainty_synthesis :
  (* K=2 uniform: standard bound 1/2 *)
  uncertainty_bound_K2 == (1#2) /\
  (* K=3 uniform: enhanced bound 2/3 > 1/2 *)
  uncertainty_bound_K3 == (2#3) /\
  (1#2) < uncertainty_bound_K3 /\
  (* Localized state: zero bound *)
  Qabs comm_exp_K3_localized / 2 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
