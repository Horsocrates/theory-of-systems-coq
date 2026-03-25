(** * HeCISynthesis.v -- Grand synthesis of He CI accuracy results
    Elements: combined theorems from HeSlaterBasis through HeConvergenceRate
    Roles:    Unified view: E_HF < E_CI < 0, variational improvement quantified
    Rules:    CI lowers energy; convergence with basis size; all over Q
    Status:   complete
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
From ToS Require Import stdlib.qphysics.HeSlaterBasis.
From ToS Require Import stdlib.qphysics.HeCIMatrix.
From ToS Require Import stdlib.qphysics.HeCIEigenvalue.
From ToS Require Import stdlib.qphysics.HeCorrelationEnergy.
From ToS Require Import stdlib.qphysics.HeConvergenceRate.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Main CI theorem                                            *)
(* ================================================================== *)

(** THE MAIN RESULT: CI improves over HF for helium.
    E_CI(PT2) = -365/128 < E_HF = -729/256 < 0. *)
Theorem he_ci_improves_over_hf :
  he_E_2STO < he_E_1STO /\ he_E_1STO < 0.
Proof.
  split.
  - assert (H1: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    assert (H2: he_E_1STO == -(729#256)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
  - unfold he_E_1STO. lra.
Qed.

(** Energy chain: E_3STO < E_2STO < E_1STO < 0 *)
Theorem he_energy_chain :
  he_E_3STO_est < he_E_2STO /\ he_E_2STO < he_E_1STO /\ he_E_1STO < 0.
Proof.
  split; [| split].
  - assert (H1: he_E_3STO_est == -(2921#1024)) by (vm_compute; reflexivity).
    assert (H2: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
  - assert (H1: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    assert (H2: he_E_1STO == -(729#256)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
  - unfold he_E_1STO. lra.
Qed.

(* ================================================================== *)
(*  Part II: Quantified improvement                                    *)
(* ================================================================== *)

(** CI improvement is exactly 1/256 hartree *)
Theorem he_ci_improvement_exact :
  he_E_1STO - he_E_2STO == 1#256.
Proof. vm_compute. reflexivity. Qed.

(** Correlation energy is negative *)
Theorem he_correlation_negative : he_E_corr < 0.
Proof. exact he_E_corr_negative. Qed.

(* ================================================================== *)
(*  Part III: Basis convergence                                        *)
(* ================================================================== *)

(** Successive improvements diminish *)
Theorem he_convergence_diminishing :
  -(he_delta_23_est) < -(he_delta_12).
Proof. exact he_improvements_diminish. Qed.

(** CI discriminant is positive (real eigenvalues exist) *)
Theorem he_ci_well_posed : 0 < he_CI_disc.
Proof. exact he_CI_disc_positive. Qed.

(* ================================================================== *)
(*  Part IV: Complete summary                                          *)
(* ================================================================== *)

(** Grand summary: all key results in one record *)
Theorem he_ci_grand_summary :
  (* 1. CI lowers energy *)
  he_E_2STO < he_E_1STO /\
  (* 2. All energies negative *)
  he_E_1STO < 0 /\
  (* 3. Improvement quantified *)
  he_E_1STO - he_E_2STO == 1#256 /\
  (* 4. Convergence *)
  he_E_3STO_est < he_E_2STO /\
  (* 5. Diminishing returns *)
  -(he_delta_23_est) < -(he_delta_12).
Proof.
  split; [| split; [| split; [| split]]].
  - assert (H1: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    assert (H2: he_E_1STO == -(729#256)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
  - unfold he_E_1STO. lra.
  - vm_compute. reflexivity.
  - assert (H1: he_E_3STO_est == -(2921#1024)) by (vm_compute; reflexivity).
    assert (H2: he_E_2STO == -(365#128)) by (vm_compute; reflexivity).
    rewrite H1, H2. lra.
  - exact he_improvements_diminish.
Qed.
