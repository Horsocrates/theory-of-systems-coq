(** * G2Atomization.v — Atomization energies for G2 test set molecules

    Elements: D_e for H2, LiH — energy to dissociate into atoms
    Roles:    atomization energy -> measure of bond strength
    Rules:    D_e > 0 for bound molecules; H-H > Li-H (stronger bond)
    Status:   verified | computed

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.G2Energies.
Open Scope Q_scope.

(** Atomization energy: D_e = sum of atom energies - molecule energy *)
Definition D_e_H2 : Q := 2 * E_H - E_H2.
Definition D_e_LiH : Q := E_Li + E_H - E_LiH.

(** Concrete values *)
Theorem D_e_H2_value : D_e_H2 == 1745 # 10000.
Proof. vm_compute. reflexivity. Qed.

Theorem D_e_LiH_value : D_e_LiH == 1188 # 10000.
Proof. vm_compute. reflexivity. Qed.

(** Both atomization energies positive (molecules are bound) *)
Theorem D_e_H2_positive : 0 < D_e_H2.
Proof. vm_compute. reflexivity. Qed.

Theorem D_e_LiH_positive : 0 < D_e_LiH.
Proof. vm_compute. reflexivity. Qed.

(** H-H bond stronger than Li-H bond *)
Theorem HH_stronger_than_LiH : D_e_LiH < D_e_H2.
Proof. vm_compute. reflexivity. Qed.

(** H2 bond energy in sub-Hartree range *)
Theorem D_e_H2_sub_hartree : D_e_H2 < 1.
Proof. vm_compute. reflexivity. Qed.

Theorem D_e_H2_above_100mH : 1 # 10 < D_e_H2.
Proof. vm_compute. reflexivity. Qed.

(** LiH bond energy bounds *)
Theorem D_e_LiH_sub_hartree : D_e_LiH < 1.
Proof. vm_compute. reflexivity. Qed.

Theorem D_e_LiH_above_50mH : 1 # 20 < D_e_LiH.
Proof. vm_compute. reflexivity. Qed.

(** Ratio: D_e_H2 is roughly 1.5x D_e_LiH *)
Theorem H2_ratio_bound : D_e_LiH < D_e_H2 /\ D_e_H2 < 2 * D_e_LiH.
Proof. split; vm_compute; reflexivity. Qed.

(** Total binding: H2 more efficient per electron *)
Theorem H2_per_electron : D_e_H2 / 2 > D_e_LiH / 4.
Proof. vm_compute. reflexivity. Qed.

Theorem molecules_are_bound : 0 < D_e_H2 /\ 0 < D_e_LiH.
Proof. split; vm_compute; reflexivity. Qed.
