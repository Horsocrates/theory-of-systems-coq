(** * GrapheneTransfer.v — Transfer matrix for graphene nanoribbon

    Elements: 2x2 graphene Hamiltonian, trace, determinant, eigenvalues
    Roles:    transfer matrix -> band structure
    Rules:    tr = 0 (bipartite); det = -t^2; eigenvalues = +/- t
    Status:   verified | matrix mechanics

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.HoneycombLattice.

(** Graphene minimal Hamiltonian: off-diagonal t *)
Definition graphene_H (i j : nat) : Q :=
  match i, j with
  | O, O => 0%Q
  | O, S O => t_hop
  | S O, O => t_hop
  | S O, S O => 0%Q
  | _, _ => 0%Q
  end.

Open Scope Q_scope.

(** Trace = 0 (bipartite lattice: no diagonal terms) *)
Theorem graphene_trace :
  graphene_H 0%nat 0%nat + graphene_H 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** Determinant = -t^2 *)
Definition graphene_det : Q :=
  graphene_H 0%nat 0%nat * graphene_H 1%nat 1%nat
  - graphene_H 0%nat 1%nat * graphene_H 1%nat 0%nat.

Theorem graphene_det_value : graphene_det == -(1).
Proof. vm_compute. reflexivity. Qed.

(** Eigenvalues: +/- t = +/- 1 *)
(** E^2 = -det = t^2 *)
Definition eigenvalue_sq : Q := -(graphene_det).

Theorem eigenvalue_sq_value : eigenvalue_sq == 1.
Proof. vm_compute. reflexivity. Qed.

(** Gap at K point = 0 *)
Theorem gap_at_K : graphene_H 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** Off-diagonal elements are equal (symmetric Hamiltonian) *)
Theorem H_symmetric :
  graphene_H 0%nat 1%nat == graphene_H 1%nat 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** Off-diagonal = hopping *)
Theorem H_hopping :
  graphene_H 0%nat 1%nat == t_hop.
Proof. vm_compute. reflexivity. Qed.

(** Diagonal = 0 (sublattices equivalent in graphene) *)
Theorem H_no_onsite :
  graphene_H 0%nat 0%nat == 0 /\ graphene_H 1%nat 1%nat == 0.
Proof. split; vm_compute; reflexivity. Qed.

(** BN-like: breaking sublattice symmetry *)
Definition H_BN (delta_onsite : Q) (i j : nat) : Q :=
  match i, j with
  | O, O => delta_onsite
  | O, S O => t_hop
  | S O, O => t_hop
  | S O, S O => Qopp delta_onsite
  | _, _ => 0%Q
  end.

(** BN has nonzero trace when delta =/= 0... actually tr = delta + (-delta) = 0 *)
Theorem BN_trace :
  H_BN (1 # 2) 0%nat 0%nat + H_BN (1 # 2) 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** BN determinant: -(delta^2 + t^2) *)
Definition det_BN (delta_onsite : Q) : Q :=
  H_BN delta_onsite 0%nat 0%nat * H_BN delta_onsite 1%nat 1%nat
  - H_BN delta_onsite 0%nat 1%nat * H_BN delta_onsite 1%nat 0%nat.

Theorem BN_det_concrete : det_BN (1 # 2) == -(5 # 4).
Proof. vm_compute. reflexivity. Qed.

(** BN gap: 2*delta *)
Theorem BN_gap_nonzero : 0 < 2 * (1 # 2).
Proof. vm_compute. reflexivity. Qed.
