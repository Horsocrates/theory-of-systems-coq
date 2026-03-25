(** * HeCIMatrix.v -- Configuration Interaction 2x2 matrix for He
    Elements: he_H_CI_11, he_H_CI_22, he_H_CI_12, CI matrix properties
    Roles:    2x2 Hamiltonian matrix for |1s(a1)^2> and |1s(a2)^2> configs
    Rules:    Diagonal = single-config energy; off-diagonal = coupling
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
From ToS Require Import stdlib.qphysics.HeSlaterBasis.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: CI matrix elements                                         *)
(* ================================================================== *)

(** Diagonal element: config |1s(alpha_1)^2>
    H_11 = 2*T + 2*V + J = alpha^2 - 4*alpha + 5*alpha/8
    For alpha = 27/16: H_11 = -729/256 *)
Definition he_H_CI_11 : Q := -(729#256).

(** Diagonal element: config |1s(alpha_2)^2>
    For alpha = 3/2: H_22 = -45/16 *)
Definition he_H_CI_22 : Q := -(45#16).

(** Off-diagonal coupling between configurations.
    In a full CI this involves cross-configuration Coulomb integrals.
    For our model: H_12 = -3/256 (weak coupling). *)
Definition he_H_CI_12 : Q := -(3#256).

(* ================================================================== *)
(*  Part II: Matrix properties                                         *)
(* ================================================================== *)

(** CI trace *)
Definition he_CI_trace : Q := he_H_CI_11 + he_H_CI_22.

Lemma he_CI_trace_value : he_CI_trace == -(1449#256).
Proof. vm_compute. reflexivity. Qed.

(** CI determinant *)
Definition he_CI_det : Q := he_H_CI_11 * he_H_CI_22 - he_H_CI_12 * he_H_CI_12.

Lemma he_CI_det_value : he_CI_det == 524871#65536.
Proof. vm_compute. reflexivity. Qed.

(** Discriminant of characteristic polynomial:
    D = (H11-H22)^2 + 4*H12^2 *)
Definition he_CI_disc : Q :=
  (he_H_CI_11 - he_H_CI_22) * (he_H_CI_11 - he_H_CI_22) +
  4 * he_H_CI_12 * he_H_CI_12.

Lemma he_CI_disc_value : he_CI_disc == 117#65536.
Proof. vm_compute. reflexivity. Qed.

(** Discriminant is positive (two real eigenvalues) *)
Lemma he_CI_disc_positive : 0 < he_CI_disc.
Proof.
  assert (H: he_CI_disc == 117#65536) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* ================================================================== *)
(*  Part III: Energy gap between configurations                        *)
(* ================================================================== *)

(** Gap between diagonal elements *)
Definition he_CI_gap : Q := he_H_CI_22 - he_H_CI_11.

Lemma he_CI_gap_value : he_CI_gap == 9#256.
Proof. vm_compute. reflexivity. Qed.

(** Config 1 (alpha_1) has lower energy than config 2 (alpha_2) *)
Lemma he_config1_lower : he_H_CI_11 < he_H_CI_22.
Proof. unfold he_H_CI_11, he_H_CI_22. lra. Qed.

(** Gap is positive *)
Lemma he_CI_gap_positive : 0 < he_CI_gap.
Proof.
  assert (H: he_CI_gap == 9#256) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Secular equation structure                                *)
(* ================================================================== *)

(** The secular equation is: E^2 - trace*E + det = 0
    Equivalently: (E - trace/2)^2 = disc/4
    Solutions: E_pm = trace/2 +/- sqrt(disc)/2 *)

Definition he_CI_half_trace : Q := he_CI_trace / 2.

Lemma he_CI_half_trace_value : he_CI_half_trace == -(1449#512).
Proof. vm_compute. reflexivity. Qed.

(** Quarter discriminant *)
Definition he_CI_quarter_disc : Q := he_CI_disc / 4.

Lemma he_CI_quarter_disc_value : he_CI_quarter_disc == 117#262144.
Proof. vm_compute. reflexivity. Qed.

(** Verify: trace^2 - 4*det = disc (characteristic polynomial identity) *)
Lemma he_CI_char_poly_identity :
  he_CI_trace * he_CI_trace - 4 * he_CI_det == he_CI_disc.
Proof. vm_compute. reflexivity. Qed.

(** Coupling ratio: |H12/gap| measures perturbation strength *)
Definition he_coupling_ratio : Q :=
  -(he_H_CI_12) / he_CI_gap.

Lemma he_coupling_ratio_value : he_coupling_ratio == 1#3.
Proof. vm_compute. reflexivity. Qed.

(** Coupling is not too strong (perturbative regime) *)
Lemma he_coupling_perturbative : he_coupling_ratio < 1.
Proof.
  assert (H: he_coupling_ratio == 1#3) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.
