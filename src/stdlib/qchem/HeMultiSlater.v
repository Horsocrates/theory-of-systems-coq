(** * HeMultiSlater.v — Two-basis Slater matrix elements for Helium

    Elements: exponents alpha_1=1, alpha_2=5/2; overlap S, Hamiltonian h
    Roles:    S_ij -> overlap matrix, h_ij -> Hamiltonian matrix
    Rules:    S_ij = 2/(a_i+a_j)^3, h_ij = a_i*a_j/(a_i+a_j)^3 - 2/(a_i+a_j)^2
    Status:   computed | verified

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.

(** Local qpow: rational power by nat *)
Fixpoint qpow (b : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S m => Qmult b (qpow b m)
  end.

Open Scope Q_scope.

(** Basis exponents *)
Definition he_alpha_1 : Q := 1.
Definition he_alpha_2 : Q := 5 # 2.

(** Overlap matrix elements: S_ij = 2 / (alpha_i + alpha_j)^3 *)
Definition he2_S_11 : Q := 2 / qpow (he_alpha_1 + he_alpha_1) 3.
Definition he2_S_12 : Q := 2 / qpow (he_alpha_1 + he_alpha_2) 3.
Definition he2_S_22 : Q := 2 / qpow (he_alpha_2 + he_alpha_2) 3.

Theorem S11_value : he2_S_11 == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

Theorem S12_value : he2_S_12 == 16 # 343.
Proof. vm_compute. reflexivity. Qed.

Theorem S22_value : he2_S_22 == 2 # 125.
Proof. vm_compute. reflexivity. Qed.

(** Hamiltonian matrix elements: h_ij = a_i*a_j/(a_i+a_j)^3 - Z*2/(a_i+a_j)^2 *)
(** For He: Z = 2 *)
Definition he2_h_11 : Q :=
  he_alpha_1 * he_alpha_1 / qpow (he_alpha_1 + he_alpha_1) 3
  - 2 / qpow (he_alpha_1 + he_alpha_1) 2.

Definition he2_h_12 : Q :=
  he_alpha_1 * he_alpha_2 / qpow (he_alpha_1 + he_alpha_2) 3
  - 2 / qpow (he_alpha_1 + he_alpha_2) 2.

Definition he2_h_22 : Q :=
  he_alpha_2 * he_alpha_2 / qpow (he_alpha_2 + he_alpha_2) 3
  - 2 / qpow (he_alpha_2 + he_alpha_2) 2.

Theorem h11_value : he2_h_11 == -(3 # 8).
Proof. vm_compute. reflexivity. Qed.

Theorem h12_value : he2_h_12 == -(36 # 343).
Proof. vm_compute. reflexivity. Qed.

Theorem h22_value : he2_h_22 == -(3 # 100).
Proof. vm_compute. reflexivity. Qed.

(** Overlap ordering: S_11 > S_12 > S_22 (tighter exponents -> more overlap) *)
Theorem overlap_ordering : he2_S_11 > he2_S_12 /\ he2_S_12 > he2_S_22.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Hamiltonian ordering: h_11 < h_12 < h_22 (more negative = lower energy) *)
Theorem hamiltonian_ordering : he2_h_11 < he2_h_12 /\ he2_h_12 < he2_h_22.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** All overlaps positive *)
Theorem overlaps_positive : he2_S_11 > 0 /\ he2_S_12 > 0 /\ he2_S_22 > 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** All Hamiltonian elements negative (bound state) *)
Theorem hamiltonian_negative : he2_h_11 < 0 /\ he2_h_12 < 0 /\ he2_h_22 < 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** Diagonal dominance: |h_11| > |h_12| *)
(** h_11 = -3/8 = -0.375, h_12 = -36/343 ≈ -0.105 *)
Theorem diagonal_dominance_h :
  -(he2_h_11) > -(he2_h_12).
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem he_multi_slater_err :
  he2_S_11 == 1 # 4 /\
  he2_h_11 == -(3 # 8) /\
  he2_h_12 == -(36 # 343) /\
  he2_h_22 == -(3 # 100).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
