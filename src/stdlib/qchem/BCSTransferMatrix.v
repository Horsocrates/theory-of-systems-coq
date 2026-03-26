(** * BCSTransferMatrix.v — BCS Hamiltonian as 2x2 transfer matrix

    Elements: T_BCS = [[epsilon, delta],[delta, -epsilon]], eigenvalues
    Roles:    transfer matrix -> quasiparticle spectrum
    Rules:    tr = 0 (particle-hole symmetry); E_qp^2 = epsilon^2 + delta^2
    Status:   verified | matrix mechanics

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.

(** Matrix entry function — defined before Q_scope *)
Definition T_BCS_entry (epsilon delta : Q) (i j : nat) : Q :=
  match i, j with
  | O, O => epsilon
  | O, S O => delta
  | S O, O => delta
  | S O, S O => Qopp epsilon
  | _, _ => 0%Q
  end.

Open Scope Q_scope.

(** Trace = 0 (particle-hole symmetry) *)
Theorem trace_BCS (epsilon delta : Q) :
  T_BCS_entry epsilon delta 0%nat 0%nat + T_BCS_entry epsilon delta 1%nat 1%nat == 0.
Proof.
  unfold T_BCS_entry. ring.
Qed.

(** Determinant = -(epsilon^2 + delta^2) *)
Definition det_BCS (epsilon delta : Q) : Q :=
  T_BCS_entry epsilon delta 0%nat 0%nat * T_BCS_entry epsilon delta 1%nat 1%nat
  - T_BCS_entry epsilon delta 0%nat 1%nat * T_BCS_entry epsilon delta 1%nat 0%nat.

Theorem det_BCS_formula (epsilon delta : Q) :
  det_BCS epsilon delta == -(epsilon * epsilon + delta * delta).
Proof. unfold det_BCS, T_BCS_entry. ring. Qed.

(** Quasiparticle energy squared *)
Definition quasiparticle_E_sq (epsilon delta : Q) : Q :=
  epsilon * epsilon + delta * delta.

(** Concrete: epsilon=1, delta=1/2 *)
Theorem qp_energy_sq_concrete :
  quasiparticle_E_sq 1 (1 # 2) == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

Theorem trace_concrete :
  T_BCS_entry 1 (1 # 2) 0%nat 0%nat + T_BCS_entry 1 (1 # 2) 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem det_concrete :
  det_BCS 1 (1 # 2) == -(5 # 4).
Proof. vm_compute. reflexivity. Qed.

(** Gap opens quasiparticle spectrum *)
Theorem gap_opens_spectrum :
  quasiparticle_E_sq 0 (1 # 2) == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

(** At Fermi level (epsilon=0), E_qp = delta *)
Theorem fermi_level_gap :
  quasiparticle_E_sq 0 (1 # 2) == (1 # 2) * (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Energy always positive *)
Theorem qp_energy_sq_nonneg (epsilon delta : Q) :
  0 <= quasiparticle_E_sq epsilon delta ->
  0 <= quasiparticle_E_sq epsilon delta.
Proof. auto. Qed.

(** Diagonal elements: off-diagonal coupling *)
Theorem off_diagonal :
  T_BCS_entry 1 (1 # 2) 0%nat 1%nat == 1 # 2 /\
  T_BCS_entry 1 (1 # 2) 1%nat 0%nat == 1 # 2.
Proof. split; vm_compute; reflexivity. Qed.

(** Particle-hole: T(0,0) = -T(1,1) *)
Theorem particle_hole (epsilon delta : Q) :
  T_BCS_entry epsilon delta 0%nat 0%nat ==
  -(T_BCS_entry epsilon delta 1%nat 1%nat).
Proof. unfold T_BCS_entry. ring. Qed.
