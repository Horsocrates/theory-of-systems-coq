(** * G2Energies.v — NIST total energies for G2 test set molecules

    Elements: total energies E_H, E_He, E_Li, E_H2, E_LiH, E_HeH_plus, E_H2O, E_CH4
    Roles:    NIST reference values -> ground truth for quantum chemistry
    Rules:    ordering by binding: more electrons = more bound (more negative)
    Status:   verified | reference data

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** NIST total energies in Hartree *)
Definition E_H : Q := -(1 # 2).
Definition E_He : Q := -(29037 # 10000).
Definition E_Li : Q := -(74327 # 10000).
Definition E_H2 : Q := -(11745 # 10000).
Definition E_LiH : Q := -(80515 # 10000).
Definition E_HeH_plus : Q := -(29633 # 10000).
Definition E_H2O : Q := -(763500 # 10000).
Definition E_CH4 : Q := -(405300 # 10000).

(** All energies are negative (bound states) *)
Theorem E_H_negative : E_H < 0.
Proof. vm_compute. reflexivity. Qed.

Theorem E_He_negative : E_He < 0.
Proof. vm_compute. reflexivity. Qed.

Theorem E_Li_negative : E_Li < 0.
Proof. vm_compute. reflexivity. Qed.

Theorem E_H2_negative : E_H2 < 0.
Proof. vm_compute. reflexivity. Qed.

Theorem E_LiH_negative : E_LiH < 0.
Proof. vm_compute. reflexivity. Qed.

(** Ordering: H > He > Li (more electrons = more bound) *)
Theorem H_above_He : E_He < E_H.
Proof. vm_compute. reflexivity. Qed.

Theorem He_above_Li : E_Li < E_He.
Proof. vm_compute. reflexivity. Qed.

Theorem H_above_Li : E_Li < E_H.
Proof. vm_compute. reflexivity. Qed.

(** Hydrogen is lightest = least bound *)
Theorem H_least_bound : E_He < E_H /\ E_Li < E_H.
Proof. split; vm_compute; reflexivity. Qed.

(** Molecules more bound than atoms *)
Theorem H2_more_bound_than_H : E_H2 < E_H.
Proof. vm_compute. reflexivity. Qed.

Theorem LiH_more_bound_than_Li : E_LiH < E_Li.
Proof. vm_compute. reflexivity. Qed.

(** Polyatomics: H2O and CH4 are deeply bound *)
Theorem H2O_deeply_bound : E_H2O < -(70 # 1).
Proof. vm_compute. reflexivity. Qed.

Theorem CH4_deeply_bound : E_CH4 < -(40 # 1).
Proof. vm_compute. reflexivity. Qed.

(** HeH+ more bound than He alone *)
Theorem HeH_more_bound_than_He : E_HeH_plus < E_He.
Proof. vm_compute. reflexivity. Qed.

Theorem HeH_more_bound_than_H : E_HeH_plus < E_H.
Proof. vm_compute. reflexivity. Qed.
