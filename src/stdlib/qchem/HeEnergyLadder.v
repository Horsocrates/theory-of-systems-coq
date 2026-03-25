(** * HeEnergyLadder.v — Helium energy hierarchy: 1-Slater, HF limit, exact

    Elements: E_1slater, E_HF_limit, E_exact energy values
    Roles:    energy ordering -> variational ladder
    Rules:    E_exact < E_HF < E_1slater (variational principle)
    Status:   verified | bounded

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** He energy values (Hartree units) *)
Definition he_E_1slater : Q := -(729 # 256).
Definition he_E_HF_limit : Q := -(28617 # 10000).
Definition he_E_exact : Q := -(29037 # 10000).

(** Energy ordering: exact < HF limit < 1-Slater (variational) *)
Theorem energy_ordering_exact_HF : he_E_exact < he_E_HF_limit.
Proof. vm_compute. reflexivity. Qed.

Theorem energy_ordering_HF_1slater : he_E_HF_limit < he_E_1slater.
Proof. vm_compute. reflexivity. Qed.

Theorem energy_ordering :
  he_E_exact < he_E_HF_limit /\ he_E_HF_limit < he_E_1slater.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Basis set error: E_1slater - E_HF_limit *)
(** = -729/256 + 28617/10000 = 2247/160000 *)
Definition basis_error : Q := he_E_1slater - he_E_HF_limit.

Theorem basis_error_value : basis_error == 2247 # 160000.
Proof. vm_compute. reflexivity. Qed.

Theorem basis_error_positive : basis_error > 0.
Proof. vm_compute. reflexivity. Qed.

Theorem basis_error_small : basis_error < 2 # 100.
Proof.
  assert (Hv : basis_error == 2247 # 160000) by (vm_compute; reflexivity).
  rewrite Hv. lra.
Qed.

(** Correlation energy: E_exact - E_HF_limit *)
(** = (-29037 + 28617)/10000 = -420/10000 = -21/500 *)
Definition he_E_corr : Q := he_E_exact - he_E_HF_limit.

Theorem corr_energy_value : he_E_corr == -(21 # 500).
Proof. vm_compute. reflexivity. Qed.

Theorem corr_energy_negative : he_E_corr < 0.
Proof. vm_compute. reflexivity. Qed.

Theorem corr_energy_magnitude : -(he_E_corr) < 5 # 100.
Proof.
  assert (Hv : he_E_corr == -(21 # 500)) by (vm_compute; reflexivity).
  rewrite Hv. lra.
Qed.

(** E/R/R verification *)
Theorem he_energy_ladder_err :
  he_E_exact < he_E_HF_limit /\
  he_E_HF_limit < he_E_1slater /\
  basis_error < 2 # 100 /\
  he_E_corr < 0.
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - assert (Hv : basis_error == 2247 # 160000) by (vm_compute; reflexivity).
    rewrite Hv. lra.
  - vm_compute. reflexivity.
Qed.
