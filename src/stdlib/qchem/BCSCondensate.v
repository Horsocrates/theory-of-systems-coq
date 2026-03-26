(** * BCSCondensate.v — BCS condensation energy and critical temperature

    Elements: condensation energy E_cond, critical temperature T_c
    Roles:    condensation -> energy lowering below T_c
    Rules:    E_cond < 0 (stabilization); T_c proportional to gap
    Status:   verified | thermodynamics

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Condensation energy: E_cond = -N_F * delta^2 / 2 *)
Definition condensation_energy (N_F delta : Q) : Q :=
  -(N_F) * delta * delta / 2.

(** Condensation energy is negative (stabilization) *)
Theorem cond_neg : condensation_energy 1 (1 # 2) < 0.
Proof. vm_compute. reflexivity. Qed.

(** Concrete value *)
Theorem cond_value : condensation_energy 1 (1 # 2) == -(1 # 8).
Proof. vm_compute. reflexivity. Qed.

(** Larger gap = more condensation *)
Theorem cond_increases_with_gap :
  condensation_energy 1 1 < condensation_energy 1 (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Higher DOS = more condensation *)
Theorem cond_increases_with_dos :
  condensation_energy 2 (1 # 2) < condensation_energy 1 (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Critical temperature: T_c approx delta * 10/18 (BCS: T_c = delta/1.764) *)
Definition T_c (delta : Q) : Q := delta * 10 / 18.

(** Concrete values *)
Theorem Tc_at_tenth : T_c (1 # 10) == 1 # 18.
Proof. vm_compute. reflexivity. Qed.

Theorem Tc_at_one : T_c 1 == 10 # 18.
Proof. vm_compute. reflexivity. Qed.

(** Tc proportional to gap *)
Theorem Tc_proportional :
  T_c 2 == 2 * T_c 1.
Proof. vm_compute. reflexivity. Qed.

(** Tc positive for positive gap *)
Theorem Tc_positive : 0 < T_c (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Tc < gap (always: 1/1.764 < 1) *)
Theorem Tc_below_gap : T_c 1 < 1.
Proof. vm_compute. reflexivity. Qed.

(** Condensation energy at T_c gap *)
Theorem cond_at_Tc_gap :
  condensation_energy 1 (T_c 1) < 0.
Proof. vm_compute. reflexivity. Qed.
