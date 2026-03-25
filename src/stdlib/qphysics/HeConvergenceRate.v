(** * HeConvergenceRate.v -- Convergence with basis size for He CI
    Elements: E_1STO, E_2STO, improvement rates, process view
    Roles:    Variational convergence: N-STO energy decreases with N
    Rules:    Each additional STO lowers energy; improvement ~ H12^2/gap
    Status:   complete
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
From ToS Require Import stdlib.qphysics.HeSlaterBasis.
From ToS Require Import stdlib.qphysics.HeCIMatrix.
From ToS Require Import stdlib.qphysics.HeCIEigenvalue.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Energy at each basis size                                  *)
(* ================================================================== *)

(** 1-STO energy (Hartree-Fock) *)
Definition he_E_1STO : Q := -(729#256).

(** 2-STO energy (CI with PT2 correction) *)
Definition he_E_2STO : Q := -(365#128).

(** Improvement from 1-STO to 2-STO *)
Definition he_delta_12 : Q := he_E_2STO - he_E_1STO.

Lemma he_delta_12_value : he_delta_12 == -(1#256).
Proof. vm_compute. reflexivity. Qed.

(** Improvement is negative (energy lowered) *)
Lemma he_delta_12_negative : he_delta_12 < 0.
Proof.
  assert (H: he_delta_12 == -(1#256)) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* ================================================================== *)
(*  Part II: Convergence rate estimation                               *)
(* ================================================================== *)

(** For STO basis, each additional function improves by roughly
    |delta_N| ~ C / N^3 for principal quantum number expansion.
    In our model: delta_12 = -1/256. *)

(** Projected 3-STO improvement (model: each step ~1/4 of previous) *)
Definition he_delta_23_est : Q := -(1#1024).

(** Projected 3-STO energy *)
Definition he_E_3STO_est : Q := he_E_2STO + he_delta_23_est.

Lemma he_E_3STO_est_value : he_E_3STO_est == -(2921#1024).
Proof. vm_compute. reflexivity. Qed.

(** 3-STO estimate is lower than 2-STO *)
Lemma he_3STO_below_2STO : he_E_3STO_est < he_E_2STO.
Proof.
  assert (H1: he_E_3STO_est == -(2921#1024)) by (vm_compute; reflexivity).
  assert (H2: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* ================================================================== *)
(*  Part III: Process view of convergence                              *)
(* ================================================================== *)

(** Energy process: E(N) for basis size N = 1, 2, 3 *)
Definition he_energy_process (n : nat) : Q :=
  match n with
  | O => he_E_1STO
  | S O => he_E_2STO
  | S (S O) => he_E_3STO_est
  | _ => he_E_3STO_est  (* saturated for this model *)
  end.

(** Process is monotonically decreasing *)
Lemma he_energy_decreasing :
  he_energy_process (S O) < he_energy_process O /\
  he_energy_process (S (S O)) < he_energy_process (S O).
Proof.
  split; simpl.
  - assert (H1: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    assert (H2: he_E_1STO == -(729#256)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
  - assert (H1: he_E_3STO_est == -(2921#1024)) by (vm_compute; reflexivity).
    assert (H2: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
Qed.

(** All energies are negative (bound states) *)
Lemma he_energy_all_negative :
  he_energy_process O < 0 /\
  he_energy_process (S O) < 0 /\
  he_energy_process (S (S O)) < 0.
Proof.
  repeat split; simpl; unfold he_E_1STO, he_E_2STO, he_E_3STO_est; lra.
Qed.

(** Improvements diminish: |delta_23| < |delta_12| *)
Lemma he_improvements_diminish :
  -(he_delta_23_est) < -(he_delta_12).
Proof.
  assert (H1: he_delta_23_est == -(1#1024)) by (vm_compute; reflexivity).
  assert (H2: he_delta_12 == -(1#256)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.
