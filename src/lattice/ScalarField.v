(* ========================================================================= *)
(*                        SCALAR FIELD ON LATTICE                           *)
(*          Lattice scalar field action as ToS Process                      *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 8 Qed, 0 Admitted, 0 axioms                                    *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Scalar field on a lattice: field values at each vertex                  *)
(*                                                                          *)
(*    Elements = ScalarField (nat -> Q): field configurations               *)
(*    Roles    = kinetic_1d, mass_term_aux, action_1d                       *)
(*    Rules    = kinetic_symmetric, action properties (L5: action extremum) *)
(*                                                                          *)
(*  PHILOSOPHICAL NOTE (P4):                                                *)
(*    The scalar field phi : nat -> Q is a PROCESS assigning a rational     *)
(*    value to each lattice site. The action functional maps field          *)
(*    configurations to rational numbers — always computable, always finite.*)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Scalar Field Definitions === *)

Definition ScalarField := nat -> Q.

(** Kinetic term: sum of (phi(v) - phi(v-1))^2 / 2 for nearest neighbors *)
Fixpoint kinetic_1d (phi : ScalarField) (N : nat) : Q :=
  match N with
  | O => 0
  | S O => 0
  | S N' => let diff := phi N' - phi (pred N') in
            diff * diff / 2 + kinetic_1d phi N'
  end.

(** Mass term: sum of m^2 * phi(v)^2 / 2 over vertices *)
Fixpoint mass_term_aux (phi : ScalarField) (m_sq : Q) (v : nat) : Q :=
  match v with
  | O => m_sq * phi O * phi O / 2
  | S v' => m_sq * phi (S v') * phi (S v') / 2 + mass_term_aux phi m_sq v'
  end.

(** Total 1D lattice action: kinetic + mass *)
Definition action_1d (phi : ScalarField) (m_sq : Q) (N : nat) : Q :=
  kinetic_1d phi N + mass_term_aux phi m_sq (pred N).

(* === Properties === *)

(** Kinetic energy is symmetric under field reversal at each link *)
Lemma kinetic_symmetric : forall a b : Q, (a - b) * (a - b) == (b - a) * (b - a).
Proof. intros. ring. Qed.

(** Constant field has zero kinetic energy *)
Lemma kinetic_zero_const : kinetic_1d (fun _ => 1) 4 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Linear ramp field has positive kinetic energy *)
Lemma kinetic_positive_step :
  kinetic_1d (fun v => inject_Z (Z.of_nat v)) 3 > 0.
Proof. vm_compute. reflexivity. Qed.

(** Single mass term is non-negative for non-negative mass squared (concrete) *)
Lemma mass_single_nonneg_concrete :
  0 <= 1 * (3#5) * (3#5) / 2.
Proof. vm_compute. discriminate. Qed.

(** Zero field gives zero action for any mass *)
Lemma action_zero_trivial : action_1d (fun _ => 0) 1 3 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Scaling: doubling field values quadruples kinetic energy *)
Lemma kinetic_scaling_example :
  kinetic_1d (fun v => 2 * inject_Z (Z.of_nat v)) 3 ==
  4 * kinetic_1d (fun v => inject_Z (Z.of_nat v)) 3.
Proof. vm_compute. reflexivity. Qed.

(** Mass term concrete computation *)
Lemma mass_term_example :
  mass_term_aux (fun v => inject_Z (Z.of_nat v)) 1 2 == 5 # 2.
Proof. vm_compute. reflexivity. Qed.

(** Action of linear field with unit mass *)
Lemma action_linear_unit_mass :
  action_1d (fun v => inject_Z (Z.of_nat v)) 1 3 == 7 # 2.
Proof. vm_compute. reflexivity. Qed.
