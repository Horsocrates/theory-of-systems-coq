(* ProcessSpectralIndex.v — Cosmological observables *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
Open Scope Q_scope.

(** n_s = 1 - 2*epsilon where epsilon = slow-roll parameter *)
(** Our epsilon = 1/576 (from ProcessInflation at beta=2) *)
Definition spectral_index : Q := 1 - 2 * (1 # 576).

Lemma ns_value : spectral_index == 287 # 288.
Proof. unfold spectral_index. unfold Qeq; simpl; lia. Qed.

(** Observed: 0.9649 +/- 0.0042. Our: 0.99653 -> 3.3% off *)

Definition tensor_to_scalar : Q := 16 * (1 # 576).

Lemma r_value : tensor_to_scalar == 1 # 36.
Proof. unfold tensor_to_scalar. unfold Qeq; simpl; lia. Qed.

(** BICEP/Keck 2021 bound: r < 0.036 *)
(** Our: 1/36 = 0.0278 < 0.036 <- WITHIN BOUND! *)
Lemma r_within_bound : tensor_to_scalar < 36 # 1000.
Proof. rewrite r_value. unfold Qlt; simpl; lia. Qed.

Lemma r_positive : 0 < tensor_to_scalar.
Proof. rewrite r_value. unfold Qlt; simpl; lia. Qed.

Lemma ns_lt_1 : spectral_index < 1.
Proof. rewrite ns_value. unfold Qlt; simpl; lia. Qed.

Lemma ns_positive : 0 < spectral_index.
Proof. rewrite ns_value. unfold Qlt; simpl; lia. Qed.

Theorem cosmological_predictions :
  spectral_index == 287 # 288 /\
  tensor_to_scalar == 1 # 36 /\
  tensor_to_scalar < 36 # 1000.
Proof.
  split; [|split].
  - exact ns_value.
  - exact r_value.
  - exact r_within_bound.
Qed.

Definition spectral_count := 8%nat.
