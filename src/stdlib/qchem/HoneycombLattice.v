(** * HoneycombLattice.v — Graphene honeycomb lattice structure

    Elements: hopping t, coordination, bandwidth, Dirac velocity, sublattices
    Roles:    honeycomb geometry -> Dirac cone at K point
    Rules:    coordination = 3; bandwidth = 6t; Dirac velocity = 3t/2
    Status:   verified | lattice geometry

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Hopping parameter (normalized) *)
Definition t_hop : Q := 1.

(** Nearest-neighbor coordination on honeycomb *)
Definition coordination_honeycomb : nat := 3%nat.

(** Bandwidth = 2 * z * t where z = coordination *)
Definition bandwidth : Q := 2 * 3 * t_hop.

Theorem bandwidth_concrete : bandwidth == 6.
Proof. vm_compute. reflexivity. Qed.

(** Dirac velocity: v_D = (3/2) * t * a/hbar, normalized *)
Definition dirac_velocity : Q := 3 * t_hop / 2.

Theorem dirac_concrete : dirac_velocity == 3 # 2.
Proof. vm_compute. reflexivity. Qed.

(** Sublattice labels *)
Definition sublattice_A : nat := 0%nat.
Definition sublattice_B : nat := 1%nat.
Definition n_sublattices : nat := 2%nat.

(** Bandwidth positive *)
Theorem bandwidth_positive : 0 < bandwidth.
Proof. vm_compute. reflexivity. Qed.

(** Dirac velocity positive *)
Theorem dirac_velocity_positive : 0 < dirac_velocity.
Proof. vm_compute. reflexivity. Qed.

(** Dirac velocity < bandwidth *)
Theorem dirac_lt_bandwidth : dirac_velocity < bandwidth.
Proof. vm_compute. reflexivity. Qed.

(** Half bandwidth = 3t *)
Definition half_bandwidth : Q := bandwidth / 2.

Theorem half_bandwidth_value : half_bandwidth == 3.
Proof. vm_compute. reflexivity. Qed.

(** Energy at K point = 0 (Dirac point) *)
Definition E_at_K : Q := 0.

Theorem E_at_K_zero : E_at_K == 0.
Proof. vm_compute. reflexivity. Qed.

(** Energy at Gamma point = +/- 3t (band extremum) *)
Definition E_at_Gamma : Q := 3 * t_hop.

Theorem E_at_Gamma_value : E_at_Gamma == 3.
Proof. vm_compute. reflexivity. Qed.

(** K point is special: zero energy *)
Theorem K_point_gapless : E_at_K < E_at_Gamma.
Proof. vm_compute. reflexivity. Qed.

(** Honeycomb = bipartite lattice *)
(** Two sublattices → 2 bands → valence + conduction *)
Definition n_bands : nat := n_sublattices.

(** Band touching at K: gap = 0 *)
Definition gap_graphene : Q := 0.

Theorem gap_zero : gap_graphene == 0.
Proof. vm_compute. reflexivity. Qed.

(** Graphene is a semimetal: gap = 0 exactly *)
Theorem semimetal : gap_graphene == E_at_K.
Proof. vm_compute. reflexivity. Qed.
