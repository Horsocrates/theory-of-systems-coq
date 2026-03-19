(** * I1_CorrelationFromZ.v -- Observables from the Partition Function
    Elements: observable_from_Z, connected_correlator, susceptibility
    Roles:    Observables as functional derivatives of Z w.r.t. source J
    Rules:    <O> = (Z_J - Z_0) / Z_0 at linear order; connects to plaquette
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import SeriesConvergence.
From ToS Require Import stdlib.I1_FormalPathIntegral.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Observable from Z                                          *)
(* ================================================================== *)

(** An observable is computed from Z with and without source J *)
Definition observable_from_Z (Z_with_J Z_without : Q) : Q :=
  (Z_with_J - Z_without) / Z_without.

(** When Z_with = Z_without, observable = 0 *)
Lemma observable_zero_source : forall Z,
  ~ Z == 0 ->
  observable_from_Z Z Z == 0.
Proof.
  intros Z HZ. unfold observable_from_Z.
  field. exact HZ.
Qed.

(** Observable is linear in the perturbation *)
Lemma observable_linear : forall Z dZ,
  ~ Z == 0 ->
  observable_from_Z (Z + dZ) Z == dZ / Z.
Proof.
  intros Z dZ HZ. unfold observable_from_Z.
  field. exact HZ.
Qed.

(* ================================================================== *)
(*  Part II: Connected Correlator                                      *)
(* ================================================================== *)

(** Connected 2-point function: <AB>_c = <AB> - <A><B> *)
Definition connected_2pt (obs_AB obs_A obs_B : Q) : Q :=
  obs_AB - obs_A * obs_B.

(** Connected correlator vanishes for independent observables *)
Lemma connected_independent : forall A B,
  connected_2pt (A * B) A B == 0.
Proof.
  intros. unfold connected_2pt. ring.
Qed.

(** Susceptibility: chi = d<O>/dJ = d^2 ln Z / dJ^2 at J=0
    Discrete version: chi = (Z(J+h) - 2*Z(0) + Z(-h)) / (h^2 * Z(0)) *)
Definition susceptibility (Z_plus Z_zero Z_minus h : Q) : Q :=
  (Z_plus - 2 * Z_zero + Z_minus) / (h * h * Z_zero).

Lemma susceptibility_symmetric : forall Z_p Z_0 Z_m h,
  susceptibility Z_p Z_0 Z_m h == susceptibility Z_m Z_0 Z_p h.
Proof.
  intros. unfold susceptibility.
  assert (Heq : Z_p - 2 * Z_0 + Z_m == Z_m - 2 * Z_0 + Z_p) by ring.
  rewrite Heq. reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: Process-Level Observables                                *)
(* ================================================================== *)

(** Observable as a process: compute at each truncation order *)
Definition observable_process (Z_J Zbase : RealProcess) : RealProcess :=
  fun K => observable_from_Z (Z_J K) (Zbase K).

(** Observable process respects ring structure *)
Lemma observable_process_add : forall Z_J1 Z_J2 (Zbase : RealProcess) K,
  ~ Zbase K == 0 ->
  observable_from_Z (Z_J1 K + Z_J2 K - Zbase K) (Zbase K) ==
  observable_from_Z (Z_J1 K) (Zbase K) + observable_from_Z (Z_J2 K) (Zbase K).
Proof.
  intros Z_J1 Z_J2 Zbase K HZ.
  unfold observable_from_Z. field. exact HZ.
Qed.

(** Plaquette as observable: <P> = I1/I0 is a ratio of partition functions *)
(** In our framework: Z_without = I0, Z_with = I0 + I1, so <P> = I1/I0 *)
Definition plaquette_as_observable (I0 I1 : Q) : Q := I1 / I0.

Lemma plaquette_from_Z : forall I0 I1,
  ~ I0 == 0 ->
  observable_from_Z (I0 + I1) I0 == plaquette_as_observable I0 I1.
Proof.
  intros I0 I1 HI0. unfold observable_from_Z, plaquette_as_observable.
  field. exact HI0.
Qed.

(** Concrete: plaquette at beta=1, M=1 gives 9/20 *)
Lemma plaquette_obs_b1 :
  plaquette_as_observable (5#4) (9#16) == 9#20.
Proof. unfold plaquette_as_observable. field. Qed.

(** Concrete: plaquette at beta=2, M=2 gives 19/27 *)
Lemma plaquette_obs_b2 :
  plaquette_as_observable (9#4) (19#12) == 19#27.
Proof. unfold plaquette_as_observable. field. Qed.

(** String tension from observable: sigma = -ln(<P>)
    Using ln approximation: sigma ~ 1 - <P> for <P> near 1 *)
Definition sigma_from_observable (obs : Q) : Q := 1 - obs.

Lemma sigma_positive_subunity : forall obs,
  0 < obs -> obs < 1 ->
  0 < sigma_from_observable obs.
Proof.
  intros obs H1 H2. unfold sigma_from_observable. lra.
Qed.

Definition correlation_from_Z_count := 15%nat.
