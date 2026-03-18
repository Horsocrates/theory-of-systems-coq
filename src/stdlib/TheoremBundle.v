(* TheoremBundle.v — Central re-export of all key results *)
(* Every major theorem accessible from one import *)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* === GAUGE THEORY === *)
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.GapRatio.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import gauge.ProofClosure.
From ToS Require Import gauge.ReflectionPositivity.
From ToS Require Import process.ProcessPhysicalSigma.
From ToS Require Import process.ProcessWeinbergAngle.

(* === PROCESS PHYSICS === *)
From ToS Require Import process.ProcessERRSymmetry.
From ToS Require Import process.ProcessERRDerived.
From ToS Require Import process.ProcessERRFermion.
From ToS Require Import process.ProcessPauliExclusion.
From ToS Require Import process.ProcessRegge.
From ToS Require Import process.ProcessSpacetime.
From ToS Require Import process.ProcessP3Gravity.

(* ================================================================== *)
(*  GAUGE: Mass Gap                                                    *)
(* ================================================================== *)

Theorem bundle_gap_value : matrix_mass_gap 1 1 0 == 289 # 384.
Proof. exact mass_gap_value_beta_1. Qed.

Theorem bundle_gap_positive : 0 < matrix_mass_gap 1 1 0.
Proof. exact mass_gap_positive_beta_1. Qed.

Theorem bundle_gap_value_2 : matrix_mass_gap 1 2 0 == 1 # 24.
Proof. exact mass_gap_value_beta_2. Qed.

Theorem bundle_gap_positive_2 : 0 < matrix_mass_gap 1 2 0.
Proof. exact mass_gap_positive_beta_2. Qed.

(* ================================================================== *)
(*  GAUGE: Reflection Positivity                                       *)
(* ================================================================== *)

Theorem bundle_rp : forall f t n,
  (forall j, (j <= n)%nat -> 0 <= t j) ->
  0 <= weighted_sum_sq f t n.
Proof. exact weighted_sum_sq_nonneg. Qed.

(* ================================================================== *)
(*  GAUGE: String Tension                                              *)
(* ================================================================== *)

Theorem bundle_sigma : I1_partial 1 1 / I0_partial 1 1 == 9 # 20.
Proof. exact ratio_b1_M1. Qed.

(* ================================================================== *)
(*  ELECTROWEAK                                                        *)
(* ================================================================== *)

Theorem bundle_weinberg : sin2_weinberg r_physical == 3 # 13.
Proof. exact weinberg_physical. Qed.

(* ================================================================== *)
(*  E/R/R DERIVED                                                      *)
(* ================================================================== *)

Theorem bundle_err_derived : forall hp hi ha,
  let sys := err_from_principles hp hi ha in
  err_nsites sys = hp_nparts hp /\
  err_nroles sys = ha_naspects hp ha /\
  (0 < err_nsites sys)%nat /\
  (2 <= err_nroles sys)%nat.
Proof. exact err_is_derived. Qed.

(* ================================================================== *)
(*  FERMIONS                                                           *)
(* ================================================================== *)

Theorem bundle_pauli : forall sys i,
  is_fermionic sys -> (i < err_nsites sys)%nat -> err_rule sys i i == 0.
Proof. exact pauli_exclusion. Qed.

Theorem bundle_decomposition : forall sys i j,
  err_rule sys i j ==
  rule_symmetric sys i j + rule_antisymmetric sys i j.
Proof. exact rule_decomposition. Qed.

(* ================================================================== *)
(*  GRAVITY                                                            *)
(* ================================================================== *)

Theorem bundle_deficit_flat : deficit_angle 6 == 0.
Proof. exact deficit_flat. Qed.

Theorem bundle_curvature_nonneg : forall G, 0 <= total_curvature G.
Proof. exact curvature_nonneg. Qed.

(* ================================================================== *)
(*  SPACETIME + LORENTZIAN                                             *)
(* ================================================================== *)

(* spacetime_asymmetry is True — OPEN: multi-concept *)
(* Use concrete Lorentzian lemmas instead *)

Theorem bundle_space_reversible : space_reversible empty_stlattice.
Proof. exact empty_space_reversible. Qed.

Theorem bundle_time_irreversible : time_irreversible empty_stlattice.
Proof. exact empty_time_irreversible. Qed.

Definition bundle_count := 14%nat.
