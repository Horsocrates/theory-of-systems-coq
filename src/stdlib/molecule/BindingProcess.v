(** * BindingProcess.v -- Chemical binding as a process
    Elements: bond_exists, R_equilibrium, binding_depth
    Roles:    H₂ binding curve → process interpretation of molecular bond
    Rules:    Bond depth > 0, equilibrium distance R_eq ≈ 1.4 a₀
    Status:   Stdlib/molecule
    STATUS: 13 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.molecule.H2Molecule.

Open Scope Q_scope.

(* ================================================================== *)
(*  BOND EXISTENCE                                                     *)
(* ================================================================== *)

(** The H₂ molecule is bound: energy below dissociation limit *)
Lemma bond_exists : E_H2 14 < -(1).
Proof. unfold E_H2. simpl. lra. Qed.

(** Bond exists at multiple distances (not just minimum) *)
Lemma bond_range :
  E_H2 10 < -(1) /\ E_H2 12 < -(1) /\
  E_H2 14 < -(1) /\ E_H2 16 < -(1) /\
  E_H2 18 < -(1) /\ E_H2 20 < -(1).
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(* ================================================================== *)
(*  EQUILIBRIUM DISTANCE                                               *)
(* ================================================================== *)

Definition R_equilibrium : Q := 7#5.

Lemma R_eq_value : R_equilibrium == 7#5.
Proof. unfold R_equilibrium. reflexivity. Qed.

(** R_eq is close to 1.401 a₀ (experimental value) *)
Lemma R_eq_diff : R_equilibrium - (1401#1000) == -(1#1000).
Proof. unfold R_equilibrium. vm_compute. reflexivity. Qed.

Lemma qabs_R_eq_diff : Qabs (R_equilibrium - (1401#1000)) == 1#1000.
Proof. rewrite R_eq_diff. vm_compute. reflexivity. Qed.

Lemma R_eq_close : Qabs (R_equilibrium - (1401#1000)) < 1#100.
Proof. rewrite qabs_R_eq_diff. lra. Qed.

(* ================================================================== *)
(*  BINDING DEPTH                                                      *)
(* ================================================================== *)

(** Binding depth = E_∞ - E_min = -1 - E(14) *)
Definition binding_depth : Q := -(1) - E_H2 14.

Lemma binding_depth_value : binding_depth == 94#1000.
Proof. unfold binding_depth, E_H2. simpl. vm_compute. reflexivity. Qed.

Lemma depth_positive : 0 < binding_depth.
Proof. rewrite binding_depth_value. lra. Qed.

(** Depth is in range [0.05, 0.15] Hartree *)
Lemma depth_reasonable :
  1#20 < binding_depth /\ binding_depth < 3#20.
Proof. rewrite binding_depth_value. split; lra. Qed.

(* ================================================================== *)
(*  PROCESS INTERPRETATION: BINDING AS STATE TRANSITION                *)
(* ================================================================== *)

(** The bonding process lowers energy monotonically from R=∞ to R_eq *)
Lemma bonding_monotone_descent :
  E_H2 30 > E_H2 24 /\ E_H2 24 > E_H2 20 /\
  E_H2 20 > E_H2 18 /\ E_H2 18 > E_H2 16 /\ E_H2 16 > E_H2 14.
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(** The unbonding process raises energy monotonically from R_eq to R=0 *)
Lemma repulsion_monotone_ascent :
  E_H2 14 < E_H2 12 /\ E_H2 12 < E_H2 10 /\ E_H2 10 < E_H2 8.
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(** At R_eq, the system is at a local minimum: restoring force exists *)
Lemma restoring_force :
  E_H2 14 < E_H2 12 /\ E_H2 14 < E_H2 16.
Proof. unfold E_H2. simpl. split; lra. Qed.

(** Binding energy per electron: De/2 *)
Definition binding_per_electron : Q := binding_depth / 2.

Lemma binding_per_electron_value : binding_per_electron == 47#1000.
Proof. unfold binding_per_electron. rewrite binding_depth_value.
  vm_compute. reflexivity.
Qed.
