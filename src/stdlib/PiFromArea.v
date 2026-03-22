(* PiFromArea.v — Pi approximations from area counting and walk perimeter *)
(* E/R/R: Elements = lattice ratios, Roles = area/walk estimator, Rules = convergence to pi *)

From Stdlib Require Import QArith Lra.
From ToS Require Import DiscreteCircle.

Open Scope Q_scope.

(** pi from area: N(R) / R^2 -> pi *)
Definition pi_area (R : nat) : Q :=
  inject_Z (N_circle R) / inject_Z (Z.of_nat (R * R)).

(** pi from walk perimeter: P(R) / (2R) -> 2pi, so P(R)/(2R) is the walk constant *)
Definition pi_walk (R : nat) : Q :=
  inject_Z (P_circle R) / inject_Z (Z.of_nat (2 * R)).

(* --- Concrete pi_area values --- *)

Lemma pi_area_1 : pi_area 1 == 5#1.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_area_2 : pi_area 2 == 13#4.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_area_3 : pi_area 3 == 29#9.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_area_5 : pi_area 5 == 81#25.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_area_10 : pi_area 10 == 317#100.
Proof. vm_compute. reflexivity. Qed.

(* --- Concrete pi_walk values --- *)

Lemma pi_walk_1 : pi_walk 1 == 6#1.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_walk_5 : pi_walk 5 == 22#5.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_walk_10 : pi_walk 10 == 21#5.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_walk_20 : pi_walk 20 == 41#10.
Proof. vm_compute. reflexivity. Qed.

(* --- Walk constant decreasing (converging to 4 from above) --- *)

Lemma pi_walk_20_lt_10 : pi_walk 20 < pi_walk 10.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_walk_10_lt_5 : pi_walk 10 < pi_walk 5.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_walk_5_lt_1 : pi_walk 5 < pi_walk 1.
Proof. vm_compute. reflexivity. Qed.
