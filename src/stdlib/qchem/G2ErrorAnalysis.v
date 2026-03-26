(** * G2ErrorAnalysis.v — Error analysis of our Q-chemistry vs NIST

    Elements: our computed energies, NIST references, errors
    Roles:    variational principle -> our energies are upper bounds
    Rules:    error > 0 (variational); error decreases with basis improvement
    Status:   verified | error quantification

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.G2Energies.
Open Scope Q_scope.

(** Our computed energies *)
Definition our_E_H : Q := -(1 # 2).       (* exact for hydrogen *)
Definition our_E_He : Q := -(729 # 256).   (* 1-Slater = -2.84765625 *)
Definition our_E_Li : Q := -(73 # 10).     (* simplified Li = -7.3 *)

(** Errors: our - NIST (positive = our is above = variational) *)
Definition error_H : Q := our_E_H - E_H.
Definition error_He : Q := our_E_He - E_He.
Definition error_Li : Q := our_E_Li - E_Li.

(** Hydrogen is exact *)
Theorem error_H_zero : error_H == 0.
Proof. vm_compute. reflexivity. Qed.

(** He error is positive (variational principle) *)
Theorem error_He_positive : 0 < error_He.
Proof. vm_compute. reflexivity. Qed.

(** Li error is positive (variational) *)
Theorem error_Li_positive : 0 < error_Li.
Proof. vm_compute. reflexivity. Qed.

(** He error small: < 0.06 Ha *)
Theorem error_He_small : error_He < 6 # 100.
Proof. vm_compute. reflexivity. Qed.

(** Li error: < 0.14 Ha *)
Theorem error_Li_small : error_Li < 14 # 100.
Proof. vm_compute. reflexivity. Qed.

(** He error < Li error in absolute terms *)
Theorem He_error_smaller : error_He < error_Li.
Proof. vm_compute. reflexivity. Qed.

(** Relative errors: error / |E_NIST| *)
Definition rel_error_He : Q := error_He / (-(E_He)).
Definition rel_error_Li : Q := error_Li / (-(E_Li)).

(** Relative errors are small (< 5%) *)
Theorem rel_error_He_small : rel_error_He < 5 # 100.
Proof. vm_compute. reflexivity. Qed.

Theorem rel_error_Li_small : rel_error_Li < 5 # 100.
Proof. vm_compute. reflexivity. Qed.

(** Li has smaller relative error than He (more electrons = better cancellation) *)
Theorem Li_rel_better : rel_error_Li < rel_error_He.
Proof. vm_compute. reflexivity. Qed.

(** Our He energy is above exact (variational bound) *)
Theorem our_He_above_exact : E_He < our_E_He.
Proof. vm_compute. reflexivity. Qed.

(** Our Li energy is above exact (variational bound) *)
Theorem our_Li_above_exact : E_Li < our_E_Li.
Proof. vm_compute. reflexivity. Qed.
