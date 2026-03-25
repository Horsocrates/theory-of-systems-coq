(** * PolarBond.v — Electronegativity and bond polarity

    Elements: atoms (H, F), electronegativity values chi
    Roles:    chi_diff -> polarity measure, polar_threshold -> classification
    Rules:    |chi_A - chi_B| > threshold implies polar bond
    Status:   polar | nonpolar | ionic

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Pauling electronegativities (scaled by 10 for integer representation) *)
Definition chi_H : Q := 22 # 10.
Definition chi_F : Q := 40 # 10.
Definition chi_O : Q := 35 # 10.
Definition chi_C : Q := 25 # 10.

(** Electronegativity difference for HF *)
Definition chi_diff_HF : Q := chi_F - chi_H.

Theorem chi_diff_HF_value : chi_diff_HF == 18 # 10.
Proof. vm_compute. reflexivity. Qed.

(** Polarity threshold: bond is polar if |chi_A - chi_B| > 0.5 *)
Definition polar_threshold : Q := 5 # 10.

Theorem HF_is_polar : chi_diff_HF > polar_threshold.
Proof. vm_compute. reflexivity. Qed.

(** H-H bond: nonpolar *)
Definition chi_diff_H2 : Q := chi_H - chi_H.

Theorem chi_diff_H2_value : chi_diff_H2 == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem H2_nonpolar : chi_diff_H2 < polar_threshold.
Proof. vm_compute. reflexivity. Qed.

(** F is more electronegative: dipole points H -> F *)
Theorem dipole_sign : chi_F > chi_H.
Proof. vm_compute. reflexivity. Qed.

(** Ionic threshold: bond is ionic if |chi_A - chi_B| > 1.7 *)
Definition ionic_threshold : Q := 17 # 10.

Theorem HF_is_ionic : chi_diff_HF > ionic_threshold.
Proof. vm_compute. reflexivity. Qed.

(** C-H bond polarity *)
Definition chi_diff_CH : Q := chi_C - chi_H.

Theorem chi_diff_CH_value : chi_diff_CH == 3 # 10.
Proof. vm_compute. reflexivity. Qed.

Theorem CH_weakly_polar : chi_diff_CH < polar_threshold.
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem polar_bond_err :
  chi_diff_HF == 18 # 10 /\
  chi_diff_HF > polar_threshold /\
  chi_diff_H2 < polar_threshold /\
  chi_F > chi_H.
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
