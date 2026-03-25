(** * H2Plus.v -- H₂⁺ molecular ion: bonding and antibonding energies
    Elements: H_AA, H_AB_full, E_bonding, E_antibonding
    Roles:    Two-center integrals → Hamiltonian matrix elements → LCAO energies
    Rules:    E_bonding < E_antibonding, bonding is bound state
    Status:   Stdlib/molecule
    STATUS: 14 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.molecule.TwoCenterIntegrals.

Open Scope Q_scope.

(* ================================================================== *)
(*  HAMILTONIAN MATRIX ELEMENTS FOR H₂⁺                               *)
(* ================================================================== *)

(** Diagonal Hamiltonian element: H_AA = T_AA + V_AA + V_AA_B + 1/R *)
Definition H_AA (alpha R s : Q) : Q :=
  kinetic_AA alpha + nuclear_AA alpha + nuclear_AA_B alpha R s + 1 / R.

(** Off-diagonal Hamiltonian element: H_AB = T_AB + 2·V_AB + S_AB/R *)
Definition H_AB_full (alpha R s : Q) : Q :=
  kinetic_AB alpha R s + 2 * nuclear_AB alpha R s + overlap_AB alpha R s / R.

(** Bonding energy: E_+ = (H_AA + H_AB) / (1 + S_AB) *)
Definition E_bonding (alpha R s : Q) : Q :=
  (H_AA alpha R s + H_AB_full alpha R s) / (1 + overlap_AB alpha R s).

(** Antibonding energy: E_- = (H_AA - H_AB) / (1 - S_AB) *)
Definition E_antibonding (alpha R s : Q) : Q :=
  (H_AA alpha R s - H_AB_full alpha R s) / (1 - overlap_AB alpha R s).

(* ================================================================== *)
(*  CONCRETE VALUES AT α=1, R=3/2, s=7/31                             *)
(* ================================================================== *)

Lemma V_AA_B_value : nuclear_AA_B 1 (3#2) (7#31) == -(559#961).
Proof. unfold nuclear_AA_B. vm_compute. reflexivity. Qed.

Lemma H_AA_value : H_AA 1 (3#2) (7#31) == -(2393#5766).
Proof.
  unfold H_AA, kinetic_AA, nuclear_AA, nuclear_AA_B.
  vm_compute. reflexivity.
Qed.

Lemma H_AB_value : H_AB_full 1 (3#2) (7#31) == -(329#744).
Proof.
  unfold H_AB_full, kinetic_AB, nuclear_AB, overlap_AB.
  vm_compute. reflexivity.
Qed.

Lemma E_bonding_value :
  E_bonding 1 (3#2) (7#31) == -(19771#39990).
Proof.
  unfold E_bonding, H_AA, H_AB_full, kinetic_AA, nuclear_AA,
    nuclear_AA_B, kinetic_AB, nuclear_AB, overlap_AB.
  vm_compute. reflexivity.
Qed.

Lemma E_antibonding_value :
  E_antibonding 1 (3#2) (7#31) == 19#186.
Proof.
  unfold E_antibonding, H_AA, H_AB_full, kinetic_AA, nuclear_AA,
    nuclear_AA_B, kinetic_AB, nuclear_AB, overlap_AB.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  KEY PHYSICAL PROPERTIES                                            *)
(* ================================================================== *)

(** Bonding is lower than antibonding *)
Lemma bonding_lower :
  E_bonding 1 (3#2) (7#31) < E_antibonding 1 (3#2) (7#31).
Proof.
  rewrite E_bonding_value, E_antibonding_value. lra.
Qed.

(** Bonding energy is negative (bound state) *)
Lemma bonding_negative :
  E_bonding 1 (3#2) (7#31) < 0.
Proof.
  rewrite E_bonding_value. lra.
Qed.

(** Antibonding energy is positive *)
Lemma antibonding_positive :
  0 < E_antibonding 1 (3#2) (7#31).
Proof.
  rewrite E_antibonding_value. lra.
Qed.

(** Bonding energy close to -1/2: |E_bonding + 1/2| < 1/100 *)
Lemma bonding_near_H_atom :
  E_bonding 1 (3#2) (7#31) - (-(1#2)) == 224#39990.
Proof.
  rewrite E_bonding_value. vm_compute. reflexivity.
Qed.

Lemma bonding_close_to_half :
  -(1#2) < E_bonding 1 (3#2) (7#31) /\
  E_bonding 1 (3#2) (7#31) < -(49#100).
Proof.
  rewrite E_bonding_value. split; lra.
Qed.

(** H_AA diagonal element is negative *)
Lemma H_AA_negative : H_AA 1 (3#2) (7#31) < 0.
Proof. rewrite H_AA_value. lra. Qed.

(** H_AB off-diagonal element is negative *)
Lemma H_AB_negative : H_AB_full 1 (3#2) (7#31) < 0.
Proof. rewrite H_AB_value. lra. Qed.

(** Energy gap between bonding and antibonding *)
Lemma energy_gap_positive :
  0 < E_antibonding 1 (3#2) (7#31) - E_bonding 1 (3#2) (7#31).
Proof.
  rewrite E_bonding_value, E_antibonding_value. lra.
Qed.

(** Overlap integral is less than 1 (physical requirement) *)
Lemma overlap_less_than_one :
  overlap_AB 1 (3#2) (7#31) < 1.
Proof. rewrite S_AB_value. lra. Qed.
