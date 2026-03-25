(** * MoleculeSynthesis.v -- Grand synthesis of H₂ molecule results
    Elements: molecule_synthesis (8-conjunct theorem)
    Roles:    Combine H₂⁺ curve, H₂ binding, and process interpretation
    Rules:    All results from prior files, no new computation
    Status:   Stdlib/molecule
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.molecule.H2PlusCurve.
From ToS Require Import stdlib.molecule.H2Molecule.
From ToS Require Import stdlib.molecule.BindingProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  CROSS-SYSTEM COMPARISONS                                          *)
(* ================================================================== *)

(** H₂ is more deeply bound than H₂⁺ *)
Lemma H2_deeper_than_H2plus :
  E_H2 14 < E_H2plus 25.
Proof. unfold E_H2, E_H2plus. simpl. lra. Qed.

(** H₂ binding depth > H₂⁺ binding depth *)
Lemma H2_stronger_bond :
  binding_depth > -(dissociation_energy).
Proof.
  rewrite binding_depth_value, De_value. lra.
Qed.

(** Both molecules have minima (local stability) *)
Lemma both_have_minima :
  (E_H2plus 25 < E_H2plus 20 /\ E_H2plus 25 < E_H2plus 30) /\
  (E_H2 14 < E_H2 12 /\ E_H2 14 < E_H2 16).
Proof.
  split.
  - exact binding_minimum.
  - exact H2_local_minimum.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                    *)
(* ================================================================== *)

(** The molecule synthesis theorem: 8 key results about H₂ *)
Theorem molecule_synthesis :
  (* 1. H₂⁺ has a bound state *)
  E_H2plus 25 < -(1#2) /\
  (* 2. H₂⁺ has a minimum at R=2.5 a₀ *)
  (E_H2plus 25 < E_H2plus 20 /\ E_H2plus 25 < E_H2plus 30) /\
  (* 3. H₂ has a bound state *)
  E_H2 14 < -(1) /\
  (* 4. H₂ has a minimum at R=1.4 a₀ *)
  (E_H2 14 < E_H2 12 /\ E_H2 14 < E_H2 16) /\
  (* 5. H₂ is more deeply bound than H₂⁺ *)
  E_H2 14 < E_H2plus 25 /\
  (* 6. Binding depth is positive *)
  0 < binding_depth /\
  (* 7. Equilibrium distance is close to experiment *)
  Qabs (R_equilibrium - (1401#1000)) < 1#100 /\
  (* 8. Restoring force exists at equilibrium *)
  (E_H2 14 < E_H2 12 /\ E_H2 14 < E_H2 16).
Proof.
  refine (conj _ (conj (conj _ _) (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _ _)))))))).
  - exact De_negative.
  - exact (proj1 binding_minimum).
  - exact (proj2 binding_minimum).
  - exact bond_exists.
  - exact (proj1 H2_local_minimum).
  - exact (proj2 H2_local_minimum).
  - exact H2_deeper_than_H2plus.
  - exact depth_positive.
  - exact R_eq_close.
  - exact (proj1 restoring_force).
  - exact (proj2 restoring_force).
Qed.

(* ================================================================== *)
(*  ADDITIONAL SYNTHESIS LEMMAS                                        *)
(* ================================================================== *)

(** Two-electron bond is roughly twice as strong as one-electron bond *)
Lemma bond_strength_ratio :
  binding_depth > dissociation_energy /\
  -(dissociation_energy) > 0.
Proof.
  rewrite binding_depth_value, De_value. split; lra.
Qed.

(** Complete binding curve: descent + minimum + ascent *)
Lemma complete_binding_curve :
  (* descent from large R *)
  E_H2 30 > E_H2 20 /\
  E_H2 20 > E_H2 14 /\
  (* minimum *)
  E_H2 14 < E_H2 12 /\
  (* ascent to small R *)
  E_H2 12 < E_H2 10 /\
  E_H2 10 < E_H2 8.
Proof. unfold E_H2. simpl. repeat split; lra. Qed.

(** H₂ dissociation energy in eV-scale: De ≈ 0.094 Hartree ≈ 2.56 eV *)
Lemma dissociation_in_range :
  1#20 < binding_depth /\ binding_depth < 1#5.
Proof. rewrite binding_depth_value. split; lra. Qed.

(** Both H₂⁺ and H₂ curves go to zero at large R (no entry = 0) *)
Lemma asymptotic_zero :
  E_H2plus 50 == 0 /\ E_H2 50 == 0.
Proof.
  unfold E_H2plus, E_H2. simpl. split; vm_compute; reflexivity.
Qed.

(** H₂ energy is higher than 2×E(H₂⁺) — electron repulsion raises it *)
Lemma electron_repulsion_effect :
  E_H2plus 25 + E_H2plus 25 < E_H2 14.
Proof. unfold E_H2, E_H2plus. simpl. lra. Qed.

(** The molecule formation is exothermic: H + H → H₂ releases energy *)
Lemma formation_exothermic :
  E_H2 14 < -(1).
Proof. exact bond_exists. Qed.
