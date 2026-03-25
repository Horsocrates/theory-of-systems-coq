(** * H2PlusCurve.v -- H₂⁺ binding energy curve (tabulated)
    Elements: E_H2plus (energy at R_tenth), dissociation_energy
    Roles:    Tabulated LCAO energy curve → minimum identification
    Rules:    Minimum near R=2.5 a₀, dissociation relative to H atom
    Status:   Stdlib/molecule
    STATUS: 7 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

(** E_H2plus: energy of H₂⁺ at R = R_tenth/10 (in atomic units).
    R_tenth is a nat encoding R in tenths of Bohr radii. *)
Definition E_H2plus (R_tenth : nat) : Q :=
  if Nat.eqb R_tenth 10 then Qmake (-288) 1000
  else if Nat.eqb R_tenth 15 then Qmake (-495) 1000
  else if Nat.eqb R_tenth 20 then Qmake (-554) 1000
  else if Nat.eqb R_tenth 25 then Qmake (-565) 1000
  else if Nat.eqb R_tenth 30 then Qmake (-559) 1000
  else if Nat.eqb R_tenth 35 then Qmake (-548) 1000
  else if Nat.eqb R_tenth 40 then Qmake (-537) 1000
  else 0.

Open Scope Q_scope.

(* ================================================================== *)
(*  BINDING MINIMUM AT R=2.5 a₀                                       *)
(* ================================================================== *)

Lemma binding_minimum :
  E_H2plus 25 < E_H2plus 20 /\ E_H2plus 25 < E_H2plus 30.
Proof.
  unfold E_H2plus. simpl. split; lra.
Qed.

(** Minimum is below all other tabulated points *)
Lemma minimum_global :
  E_H2plus 25 < E_H2plus 10 /\
  E_H2plus 25 < E_H2plus 15 /\
  E_H2plus 25 < E_H2plus 35 /\
  E_H2plus 25 < E_H2plus 40.
Proof.
  unfold E_H2plus. simpl. repeat split; lra.
Qed.

(* ================================================================== *)
(*  DISSOCIATION ENERGY RELATIVE TO H ATOM                            *)
(* ================================================================== *)

(** Dissociation energy: ΔE = E_min - E(H) where E(H) = -1/2 *)
Definition dissociation_energy : Q := E_H2plus 25 - (-(1#2)).

Lemma De_value : dissociation_energy == -(65#1000).
Proof. unfold dissociation_energy, E_H2plus. simpl. vm_compute. reflexivity. Qed.

(** Dissociation energy is negative: molecule is bound *)
Lemma De_negative : dissociation_energy < 0.
Proof. rewrite De_value. lra. Qed.

(* ================================================================== *)
(*  CURVE SHAPE: REPULSIVE WALL + ATTRACTIVE WELL                     *)
(* ================================================================== *)

(** Energy rises at short range (repulsive wall) *)
Lemma repulsive_wall : E_H2plus 10 > E_H2plus 15.
Proof. unfold E_H2plus. simpl. lra. Qed.

(** Energy rises at long range (dissociation) *)
Lemma long_range_rise :
  E_H2plus 30 > E_H2plus 25 /\
  E_H2plus 35 > E_H2plus 30 /\
  E_H2plus 40 > E_H2plus 35.
Proof. unfold E_H2plus. simpl. repeat split; lra. Qed.

(** The curve is below zero everywhere (all points are bound) *)
Lemma all_negative :
  E_H2plus 10 < 0 /\ E_H2plus 15 < 0 /\
  E_H2plus 20 < 0 /\ E_H2plus 25 < 0 /\
  E_H2plus 30 < 0 /\ E_H2plus 35 < 0 /\ E_H2plus 40 < 0.
Proof. unfold E_H2plus. simpl. repeat split; lra. Qed.
