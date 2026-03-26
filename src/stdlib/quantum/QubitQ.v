(** * QubitQ.v — Qubit gates as rational matrix entries

    Elements: Pauli X, Pauli Z, unnormalized Hadamard matrix entries
    Roles:    gate action on computational basis states
    Rules:    X^2 = I; H_u^2 = 2I; Born rule probability = 1/2
    Status:   verified | single-qubit gates

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool.
Open Scope Q_scope.

(** Pauli X gate: X = [[0,1],[1,0]] *)
Definition pauli_X (i j : nat) : Q :=
  match i, j with
  | O, S O => 1
  | S O, O => 1
  | _, _ => 0
  end.

(** Pauli Z gate: Z = [[1,0],[0,-1]] *)
Definition pauli_Z (i j : nat) : Q :=
  match i, j with
  | O, O => 1
  | S O, S O => -(1)
  | _, _ => 0
  end.

(** Unnormalized Hadamard: H_u = [[1,1],[1,-1]] *)
Definition hadamard_u (i j : nat) : Q :=
  match i, j with
  | O, O => 1
  | O, S O => 1
  | S O, O => 1
  | S O, S O => -(1)
  | _, _ => 0
  end.

(** ---- Pauli X entries ---- *)

Theorem pauli_X_01 : pauli_X 0%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pauli_X_10 : pauli_X 1%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pauli_X_00 : pauli_X 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** X^2 = I at (0,0): sum_k X_{0k} X_{k0} = X_{00}X_{00} + X_{01}X_{10} = 0+1 = 1 *)
Theorem pauli_X_sq_00 :
  pauli_X 0%nat 0%nat * pauli_X 0%nat 0%nat +
  pauli_X 0%nat 1%nat * pauli_X 1%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(** X^2 = I at (0,1): X_{00}X_{01} + X_{01}X_{11} = 0+0 = 0 *)
Theorem pauli_X_sq_01 :
  pauli_X 0%nat 0%nat * pauli_X 0%nat 1%nat +
  pauli_X 0%nat 1%nat * pauli_X 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** ---- Hadamard entries ---- *)

(** H_u^2 = 2I at (0,0): H_{00}H_{00} + H_{01}H_{10} = 1+1 = 2 *)
Theorem hadamard_sq_00 :
  hadamard_u 0%nat 0%nat * hadamard_u 0%nat 0%nat +
  hadamard_u 0%nat 1%nat * hadamard_u 1%nat 0%nat == 2.
Proof. vm_compute. reflexivity. Qed.

(** H_u^2 = 2I at (0,1): H_{00}H_{01} + H_{01}H_{11} = 1-1 = 0 *)
Theorem hadamard_sq_01 :
  hadamard_u 0%nat 0%nat * hadamard_u 0%nat 1%nat +
  hadamard_u 0%nat 1%nat * hadamard_u 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** ---- Born rule: H|0> has probability 1/2 per outcome ---- *)

(** After H on |0>: amplitude of |0> is 1/sqrt(2), prob = 1/2.
    In unnormalized form: |H_{00}|^2 / (|H_{00}|^2 + |H_{10}|^2) = 1/2 *)
Definition born_prob_0 : Q :=
  (hadamard_u 0%nat 0%nat * hadamard_u 0%nat 0%nat) /
  (hadamard_u 0%nat 0%nat * hadamard_u 0%nat 0%nat +
   hadamard_u 1%nat 0%nat * hadamard_u 1%nat 0%nat).

Theorem born_hadamard : born_prob_0 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** Pauli Z entries *)
Theorem pauli_Z_00 : pauli_Z 0%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pauli_Z_11 : pauli_Z 1%nat 1%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(** XZ + ZX = 0 at (0,0): anticommutation *)
Theorem xz_anticommute_00 :
  (pauli_X 0%nat 0%nat * pauli_Z 0%nat 0%nat +
   pauli_X 0%nat 1%nat * pauli_Z 1%nat 0%nat) +
  (pauli_Z 0%nat 0%nat * pauli_X 0%nat 0%nat +
   pauli_Z 0%nat 1%nat * pauli_X 1%nat 0%nat) == 0.
Proof. vm_compute. reflexivity. Qed.

(** Hadamard maps |0> to equal superposition: H_u|0> = (1,1) *)
Theorem hadamard_on_zero :
  hadamard_u 0%nat 0%nat == 1 /\ hadamard_u 1%nat 0%nat == 1.
Proof. split; vm_compute; reflexivity. Qed.
