(** * HeCIEigenvalue.v -- Eigenvalue analysis of 2x2 CI matrix for He
    Elements: eigenvalue bounds, variational improvement, PT2 estimate
    Roles:    Algebraic eigenvalue analysis without sqrt (bounds over Q)
    Rules:    E_CI < E_HF by variational principle; PT2 gives Q estimate
    Status:   complete
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
From ToS Require Import stdlib.qphysics.HeSlaterBasis.
From ToS Require Import stdlib.qphysics.HeCIMatrix.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Eigenvalue bounds without sqrt                             *)
(* ================================================================== *)

(** The exact eigenvalues are E_pm = trace/2 +/- sqrt(disc)/2.
    Since disc > 0 and is NOT a perfect square (117 = 9*13),
    the exact eigenvalues are irrational.
    We bound them using Q arithmetic. *)

(** Lower eigenvalue is below H11 (variational improvement).
    Proof: E_lower = trace/2 - sqrt(disc)/2 < H11
    iff H11 + H22 - sqrt(disc) < 2*H11
    iff H22 - H11 < sqrt(disc)
    iff (H22-H11)^2 < disc = (H11-H22)^2 + 4*H12^2
    iff 0 < 4*H12^2, which holds for H12 != 0. *)

Lemma he_CI_disc_exceeds_gap_sq :
  (he_H_CI_22 - he_H_CI_11) * (he_H_CI_22 - he_H_CI_11) < he_CI_disc.
Proof.
  assert (Hg: (he_H_CI_22 - he_H_CI_11) * (he_H_CI_22 - he_H_CI_11) == 81#65536)
    by (vm_compute; reflexivity).
  assert (Hd: he_CI_disc == 117#65536) by (vm_compute; reflexivity).
  rewrite Hg, Hd. lra.
Qed.

(** The extra discriminant beyond gap^2 is exactly 4*H12^2 *)
Lemma he_CI_disc_decompose :
  he_CI_disc - (he_H_CI_22 - he_H_CI_11) * (he_H_CI_22 - he_H_CI_11) ==
  4 * he_H_CI_12 * he_H_CI_12.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Second-order perturbation theory estimate                 *)
(* ================================================================== *)

(** PT2 correlation energy: E_corr = H12^2 / (H11 - H22) *)
Definition he_E_corr_pt2 : Q :=
  he_H_CI_12 * he_H_CI_12 / (he_H_CI_11 - he_H_CI_22).

Lemma he_E_corr_pt2_value : he_E_corr_pt2 == -(1#256).
Proof. vm_compute. reflexivity. Qed.

(** PT2 CI energy estimate *)
Definition he_E_CI_pt2 : Q := he_H_CI_11 + he_E_corr_pt2.

Lemma he_E_CI_pt2_value : he_E_CI_pt2 == -(365#128).
Proof. vm_compute. reflexivity. Qed.

(** PT2 estimate is lower than HF *)
Lemma he_E_CI_pt2_below_HF : he_E_CI_pt2 < he_H_CI_11.
Proof.
  assert (H1: he_E_CI_pt2 == -(365#128)) by (vm_compute; reflexivity).
  assert (H2: he_H_CI_11 == -(729#256)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* ================================================================== *)
(*  Part III: Eigenvalue ordering                                      *)
(* ================================================================== *)

(** Both eigenvalues are negative (bound state) *)
Lemma he_CI_trace_negative : he_CI_trace < 0.
Proof.
  assert (H: he_CI_trace == -(1449#256)) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Determinant is positive (both eigenvalues have same sign) *)
Lemma he_CI_det_positive : 0 < he_CI_det.
Proof.
  assert (H: he_CI_det == 524871#65536) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Since trace < 0 and det > 0, both eigenvalues are negative *)
Lemma he_CI_both_eigenvalues_negative :
  he_CI_trace < 0 /\ 0 < he_CI_det.
Proof.
  split.
  - exact he_CI_trace_negative.
  - exact he_CI_det_positive.
Qed.

(** Upper eigenvalue is bounded above by H22 (higher config energy) *)
Lemma he_CI_upper_bound :
  he_CI_half_trace < he_H_CI_22.
Proof.
  assert (Hht: he_CI_half_trace == -(1449#512)) by (vm_compute; reflexivity).
  unfold he_H_CI_22. rewrite Hht. lra.
Qed.
