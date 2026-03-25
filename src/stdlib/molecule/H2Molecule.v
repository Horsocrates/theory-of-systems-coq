(** * H2Molecule.v -- H₂ molecule: binding energy curve (tabulated)
    Elements: E_H2 (energy at R_tenth), H2_dissociation
    Roles:    Tabulated Hartree-Fock-level energy curve for H₂
    Rules:    Minimum near R=1.4 a₀, dissociation relative to 2×E(H) = -1
    Status:   Stdlib/molecule
    STATUS: 13 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

(** E_H2: total energy of H₂ at R = R_tenth/10 (in atomic units).
    Includes nuclear repulsion 1/R. Values from simple LCAO-MO. *)
Definition E_H2 (R_tenth : nat) : Q :=
  if Nat.eqb R_tenth 8 then Qmake (-869) 1000
  else if Nat.eqb R_tenth 10 then Qmake (-1038) 1000
  else if Nat.eqb R_tenth 12 then Qmake (-1082) 1000
  else if Nat.eqb R_tenth 14 then Qmake (-1094) 1000
  else if Nat.eqb R_tenth 16 then Qmake (-1083) 1000
  else if Nat.eqb R_tenth 18 then Qmake (-1063) 1000
  else if Nat.eqb R_tenth 20 then Qmake (-1038) 1000
  else if Nat.eqb R_tenth 24 then Qmake (-990) 1000
  else if Nat.eqb R_tenth 30 then Qmake (-935) 1000
  else 0.

Open Scope Q_scope.

(* ================================================================== *)
(*  BINDING MINIMUM AT R=1.4 a₀                                       *)
(* ================================================================== *)

Lemma H2_minimum :
  E_H2 14 < E_H2 10 /\ E_H2 14 < E_H2 20.
Proof. unfold E_H2. simpl. split; lra. Qed.

Lemma H2_local_minimum :
  E_H2 14 < E_H2 12 /\ E_H2 14 < E_H2 16.
Proof. unfold E_H2. simpl. split; lra. Qed.

(** Minimum is below all other tabulated points *)
Lemma H2_global_minimum :
  E_H2 14 < E_H2 8 /\
  E_H2 14 < E_H2 10 /\
  E_H2 14 < E_H2 12 /\
  E_H2 14 < E_H2 16 /\
  E_H2 14 < E_H2 18 /\
  E_H2 14 < E_H2 20 /\
  E_H2 14 < E_H2 24 /\
  E_H2 14 < E_H2 30.
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(* ================================================================== *)
(*  DISSOCIATION ENERGY                                                *)
(* ================================================================== *)

(** Dissociation limit: 2 × E(H) = 2 × (-1/2) = -1 *)
Definition H2_dissociation : Q := E_H2 14 - (-(1)).

Lemma H2_dissociation_value : H2_dissociation == -(94#1000).
Proof. unfold H2_dissociation, E_H2. simpl. vm_compute. reflexivity. Qed.

(** H₂ is bound: energy below dissociation limit *)
Lemma H2_bound : H2_dissociation < 0.
Proof. rewrite H2_dissociation_value. lra. Qed.

(** Bond energy (positive value): De = |E_min - E_∞| *)
Lemma H2_bond_energy_positive : 0 < -(H2_dissociation).
Proof. rewrite H2_dissociation_value. lra. Qed.

(* ================================================================== *)
(*  CURVE SHAPE                                                        *)
(* ================================================================== *)

(** Repulsive wall at short range *)
Lemma H2_repulsive_wall :
  E_H2 8 > E_H2 10 /\ E_H2 10 > E_H2 12.
Proof. unfold E_H2. simpl. split; lra. Qed.

(** Attractive well rising to dissociation at long range *)
Lemma H2_long_range :
  E_H2 14 < E_H2 20 /\ E_H2 20 < E_H2 30.
Proof. unfold E_H2. simpl. split; lra. Qed.

(** All tabulated energies are negative *)
Lemma H2_all_negative :
  E_H2 8 < 0 /\ E_H2 10 < 0 /\ E_H2 12 < 0 /\
  E_H2 14 < 0 /\ E_H2 16 < 0 /\ E_H2 18 < 0 /\
  E_H2 20 < 0 /\ E_H2 24 < 0 /\ E_H2 30 < 0.
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(** All tabulated energies are below the dissociation limit -1 *)
Lemma H2_all_bound :
  E_H2 10 < -(1) /\ E_H2 12 < -(1) /\
  E_H2 14 < -(1) /\ E_H2 16 < -(1) /\
  E_H2 18 < -(1) /\ E_H2 20 < -(1).
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(** Equilibrium distance R_eq ≈ 1.4 a₀ *)
Lemma H2_equilibrium_R : E_H2 14 == -(1094#1000).
Proof. unfold E_H2. simpl. vm_compute. reflexivity. Qed.

(** Energy at equilibrium is deeper than H₂⁺ would be *)
Lemma H2_deeper_than_H2plus :
  E_H2 14 < -(1#2).
Proof. unfold E_H2. simpl. lra. Qed.

(** Monotone descent from R=0.8 to R=1.4 *)
Lemma H2_descent :
  E_H2 8 > E_H2 10 /\ E_H2 10 > E_H2 12 /\ E_H2 12 > E_H2 14.
Proof. unfold E_H2. simpl. repeat split; lra. Qed.
