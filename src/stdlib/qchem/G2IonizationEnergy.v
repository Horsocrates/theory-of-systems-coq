(** * G2IonizationEnergy.v — Ionization energies for G2 atoms

    Elements: IE_H, IE_He, IE_Li — first ionization energies
    Roles:    ionization -> electron removal energy
    Rules:    periodic trend: IE_Li < IE_H < IE_He (shell structure)
    Status:   verified | NIST reference

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** First ionization energies in Hartree *)
Definition IE_H : Q := 1 # 2.         (* exact: 13.6 eV *)
Definition IE_He : Q := 9036 # 10000.  (* 0.9036 Ha = 24.59 eV *)
Definition IE_Li : Q := 1984 # 10000.  (* 0.1984 Ha = 5.39 eV *)
Definition IE_Be : Q := 3426 # 10000.  (* 0.3426 Ha = 9.32 eV *)

(** All IE positive *)
Theorem IE_H_positive : 0 < IE_H.
Proof. vm_compute. reflexivity. Qed.

Theorem IE_He_positive : 0 < IE_He.
Proof. vm_compute. reflexivity. Qed.

Theorem IE_Li_positive : 0 < IE_Li.
Proof. vm_compute. reflexivity. Qed.

(** Periodic ordering: Li < H < He *)
Theorem IE_Li_lt_H : IE_Li < IE_H.
Proof. vm_compute. reflexivity. Qed.

Theorem IE_H_lt_He : IE_H < IE_He.
Proof. vm_compute. reflexivity. Qed.

Theorem IE_Li_lt_He : IE_Li < IE_He.
Proof. vm_compute. reflexivity. Qed.

(** Full periodic trend *)
Theorem periodic_trend : IE_Li < IE_H /\ IE_H < IE_He.
Proof. split; vm_compute; reflexivity. Qed.

(** IE drops from He to Li = new shell opens *)
Theorem shell_drop : IE_Li < IE_He / 2.
Proof. vm_compute. reflexivity. Qed.

(** He has largest IE (noble gas = full shell) *)
Theorem He_largest_IE : IE_H < IE_He /\ IE_Li < IE_He /\ IE_Be < IE_He.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Be > Li (same period, increasing Z) *)
Theorem Be_above_Li : IE_Li < IE_Be.
Proof. vm_compute. reflexivity. Qed.

(** IE in eV: 1 Ha = 27.2114 eV, so IE_H ~ 13.6 eV *)
(** IE_H * 27 = 13.5 which is close to 13.6 eV *)
Definition IE_H_eV_approx : Q := IE_H * (272 # 10).
Theorem IE_H_eV_range : 13 < IE_H_eV_approx /\ IE_H_eV_approx < 14.
Proof. split; vm_compute; reflexivity. Qed.
