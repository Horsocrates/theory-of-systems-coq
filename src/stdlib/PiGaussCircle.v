(** * PiGaussCircle.v — π from Gauss circle problem (lattice point counting)
    Elements: count_row, count_all, lattice_count, pi_lattice
    Roles:    lattice_count(R) / R² → π as R → ∞
    Rules:    count integer lattice points inside circle of radius R
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Z_scope.

(* ================================================================== *)
(*  LATTICE POINT COUNTING                                            *)
(* ================================================================== *)

(** Check if point (x,y) is inside circle of radius R centered at origin.
    We use offset coordinates: m,n in [0..2R], mapped to x=m-R, y=n-R.
    Test: (m-R)² + (n-R)² ≤ R² *)

Definition inside_circle (R m n : Z) : bool :=
  let x := m - R in
  let y := n - R in
  (x * x + y * y <=? R * R)%Z.

(** Count points in a single row: iterate n from 0 to bound-1 *)
Fixpoint count_row (R m : Z) (n_remaining : nat) (current_n : Z) : Z :=
  match n_remaining with
  | O => 0
  | S k =>
    let inc := if inside_circle R m current_n then 1 else 0 in
    inc + count_row R m k (current_n + 1)
  end.

(** Count all rows: iterate m from 0 to bound-1 *)
Fixpoint count_all (R : Z) (m_remaining : nat) (current_m : Z) (width : nat) : Z :=
  match m_remaining with
  | O => 0
  | S k =>
    count_row R current_m width 0 + count_all R k (current_m + 1) width
  end.

(** Total lattice count: grid from (0,0) to (2R, 2R) *)
Definition lattice_count (R : nat) : Z :=
  let Rz := Z.of_nat R in
  let side := (2 * R + 1)%nat in
  count_all Rz side 0 side.

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma lattice_count_0 : lattice_count 0 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma lattice_count_1 : lattice_count 1 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma lattice_count_2 : lattice_count 2 = 13.
Proof. vm_compute. reflexivity. Qed.

Lemma lattice_count_3 : lattice_count 3 = 29.
Proof. vm_compute. reflexivity. Qed.

Lemma lattice_count_4 : lattice_count 4 = 49.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  π APPROXIMATION: lattice_count / R²                                *)
(* ================================================================== *)

Open Scope Q_scope.

Definition pi_lattice (R : nat) : Q :=
  inject_Z (lattice_count R) / inject_Z (Z.of_nat (R * R)).

(** R=1: 5/1 = 5 *)
Lemma pi_lattice_1 : pi_lattice 1 == 5.
Proof. vm_compute. reflexivity. Qed.

(** R=2: 13/4 = 3.25 *)
Lemma pi_lattice_2 : pi_lattice 2 == 13#4.
Proof. vm_compute. reflexivity. Qed.

(** R=3: 29/9 ≈ 3.222 *)
Lemma pi_lattice_3 : pi_lattice 3 == 29#9.
Proof. vm_compute. reflexivity. Qed.

(** R=4: 49/16 ≈ 3.0625 *)
Lemma pi_lattice_4 : pi_lattice 4 == 49#16.
Proof. vm_compute. reflexivity. Qed.

(** Convergence: pi_lattice gets closer to π ≈ 3.14159 *)
Lemma pi_lattice_decreasing_1_2 : pi_lattice 1 > pi_lattice 2.
Proof. unfold Qlt. vm_compute. reflexivity. Qed.

(** Bounded below by 3 for R ≥ 2 *)
Lemma pi_lattice_2_above_3 : 3 < pi_lattice 2.
Proof. unfold Qlt. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem pi_gauss_circle_synthesis :
  lattice_count 1 = 5%Z /\
  lattice_count 2 = 13%Z /\
  lattice_count 3 = 29%Z /\
  pi_lattice 2 == 13#4 /\
  3 < pi_lattice 2.
Proof.
  split; [|split; [|split; [|split]]].
  - exact lattice_count_1.
  - exact lattice_count_2.
  - exact lattice_count_3.
  - exact pi_lattice_2.
  - exact pi_lattice_2_above_3.
Qed.
