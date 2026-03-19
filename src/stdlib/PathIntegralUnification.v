(* PathIntegralUnification.v — Partition functions = Z from I1 *)
From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import stdlib.I1_FormalPathIntegral.
From ToS Require Import stdlib.I1_CorrelationFromZ.
From ToS Require Import process.ProcessPlaquette.
From ToS Require Import process.ProcessPhysicalSigma.
From ToS Require Import gauge.CharacterTransfer.
Open Scope Q_scope.
Theorem sigma_from_Z : I1_partial 1 1 / I0_partial 1 1 == 9 # 20.
Proof. exact ratio_b1_M1. Qed.
Theorem plaquette_from_Z_instance :
  plaquette_as_observable (5#4) (9#16) == 9#20.
Proof. exact plaquette_obs_b1. Qed.
Theorem path_integral_bridge :
  I1_partial 1 1 / I0_partial 1 1 == 9 # 20 /\
  plaquette_as_observable (5#4) (9#16) == 9#20 /\
  plaquette 1 1 == 9 # 20.
Proof. split; [|split]; [exact sigma_from_Z | exact plaquette_from_Z_instance | exact plaquette_b1_M1]. Qed.
Definition pi_unification_count := 3%nat.
