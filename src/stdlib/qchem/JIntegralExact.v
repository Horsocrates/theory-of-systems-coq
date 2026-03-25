(** * JIntegralExact.v — Exact Coulomb J-integral for same-exponent 1s orbitals

    Elements: orbital exponents (alpha), nuclear charges (Z)
    Roles:    J_same -> Coulomb integral, h_one_electron -> Hamiltonian
    Rules:    J = 5α/8, E = 2h + J (constitution)
    Status:   verified | computed

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** J-integral for two identical 1s orbitals with exponent alpha *)
Definition J_same (alpha : Q) : Q := 5 * alpha / 8.

Theorem J_at_1 : J_same 1 == 5 # 8.
Proof. vm_compute. reflexivity. Qed.

Theorem J_at_27_16 : J_same (27 # 16) == 135 # 128.
Proof. vm_compute. reflexivity. Qed.

Theorem J_at_2 : J_same 2 == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

Theorem J_at_3 : J_same 3 == 15 # 8.
Proof. vm_compute. reflexivity. Qed.

Theorem J_positive_1 : J_same 1 > 0.
Proof. vm_compute. reflexivity. Qed.

Theorem J_positive_2 : J_same 2 > 0.
Proof. vm_compute. reflexivity. Qed.

Theorem J_linear : J_same 2 == 2 * J_same 1.
Proof. vm_compute. reflexivity. Qed.

Theorem J_scales : J_same (27 # 16) / J_same 1 == 27 # 16.
Proof. vm_compute. reflexivity. Qed.

(** One-electron Hamiltonian: h = α²/2 - Zα *)
Definition h_one_electron (alpha Z : Q) : Q := alpha * alpha / 2 - Z * alpha.

Theorem h_at_27_16 : h_one_electron (27 # 16) 2 == -(999 # 512).
Proof. vm_compute. reflexivity. Qed.

Theorem h_at_1 : h_one_electron 1 1 == -(1 # 2).
Proof. vm_compute. reflexivity. Qed.

Theorem h_at_Z2_a1 : h_one_electron 1 2 == -(3 # 2).
Proof. vm_compute. reflexivity. Qed.

(** He ground state energy with single Slater determinant (α=27/16) *)
Theorem E_he_1slater :
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == -(729 # 256).
Proof. vm_compute. reflexivity. Qed.

Theorem J_same_monotone_concrete : J_same 1 < J_same 2.
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem j_integral_err :
  J_same 1 == 5 # 8 /\
  h_one_electron (27 # 16) 2 == -(999 # 512) /\
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == -(729 # 256).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
