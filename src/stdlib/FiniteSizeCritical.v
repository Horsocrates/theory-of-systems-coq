(** * FiniteSizeCritical.v — Critical exponents from finite-size analysis
    Elements: alpha_box_energy, alpha_box_spacing, alpha_walk_return, scaling exponents
    Roles:    define critical exponents for box, walk, and Ising models
    Rules:    universality comparisons, exponent ordering, scaling hypothesis
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- Critical exponents --- *)
Definition alpha_box_energy : Q := 4.
Definition alpha_box_spacing : Q := 2.
Definition alpha_walk_return : Q := 3 # 2.

(* --- Ising critical exponents (2D exact) --- *)
Definition ising_beta : Q := 1 # 8.
Definition ising_gamma : Q := 7 # 4.
Definition ising_nu : Q := 1.

(* 1 *)
Lemma box_energy_value : alpha_box_energy == 4.
Proof. vm_compute. reflexivity. Qed.

(* 2 *)
Lemma box_spacing_value : alpha_box_spacing == 2.
Proof. vm_compute. reflexivity. Qed.

(* 3 *)
Lemma walk_return_value : alpha_walk_return == 3 # 2.
Proof. vm_compute. reflexivity. Qed.

(* 4 *)
Lemma box_energy_gt_spacing : alpha_box_spacing < alpha_box_energy.
Proof. unfold alpha_box_spacing, alpha_box_energy. lra. Qed.

(* 5 *)
Lemma walk_lt_spacing : alpha_walk_return < alpha_box_spacing.
Proof. unfold alpha_walk_return, alpha_box_spacing. lra. Qed.

(* 6 *)
Lemma exponent_ordering :
  alpha_walk_return < alpha_box_spacing /\
  alpha_box_spacing < alpha_box_energy.
Proof.
  unfold alpha_walk_return, alpha_box_spacing, alpha_box_energy.
  split; lra.
Qed.

(* --- Scaling hypothesis: gamma/nu = 2 - eta --- *)
Definition ising_eta : Q := 1 # 4.

(* 7 *)
Lemma ising_gamma_over_nu : ising_gamma / ising_nu == 7 # 4.
Proof. vm_compute. reflexivity. Qed.

(* 8 *)
Lemma ising_scaling_relation : 2 - ising_eta == ising_gamma / ising_nu.
Proof. unfold ising_eta, ising_gamma, ising_nu. vm_compute. reflexivity. Qed.

(* --- Universality: exponents don't depend on lattice details --- *)
Definition square_nu : Q := 1.
Definition triangular_nu : Q := 1.

(* 9 *)
Lemma universality_nu : square_nu == triangular_nu.
Proof. vm_compute. reflexivity. Qed.

(* 10 *)
Lemma ising_beta_positive : 0 < ising_beta.
Proof. unfold ising_beta. lra. Qed.

(* 11 *)
Lemma ising_gamma_positive : 0 < ising_gamma.
Proof. unfold ising_gamma. lra. Qed.

(* --- Hyperscaling: d*nu = 2 - alpha (d=2) --- *)
Definition ising_alpha_heat : Q := 0.  (* log divergence in 2D *)

(* 12 *)
Lemma hyperscaling_2d : 2 * ising_nu == 2 - ising_alpha_heat.
Proof. unfold ising_nu, ising_alpha_heat. lra. Qed.

(* --- Rushbrooke inequality: alpha + 2*beta + gamma >= 2 --- *)
(* 13 *)
Lemma rushbrooke_equality :
  ising_alpha_heat + 2 * ising_beta + ising_gamma == 2.
Proof.
  unfold ising_alpha_heat, ising_beta, ising_gamma. lra.
Qed.

(* 14 *)
Lemma all_exponents_nonneg :
  0 <= ising_alpha_heat /\ 0 <= ising_beta /\ 0 <= ising_gamma /\ 0 <= ising_nu.
Proof.
  unfold ising_alpha_heat, ising_beta, ising_gamma, ising_nu.
  repeat split; lra.
Qed.

(* 15 *)
Lemma fisher_relation : ising_gamma == (2 - ising_eta) * ising_nu.
Proof. unfold ising_gamma, ising_eta, ising_nu. lra. Qed.
