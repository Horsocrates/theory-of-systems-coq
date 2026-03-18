(* ProcessPlaquetteFix.v — Error bounds on plaquette *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessPlaquette.
From ToS Require Import process.ProcessPlaquetteCurve.
From ToS Require Import process.ProcessBeta4.
From ToS Require Import process.ProcessPlaquetteExtended.

Open Scope Q_scope.

(** Error bound: |P_{M+1} - P_M| <= bessel_term(0,M+1) + bessel_term(1,M+1) *)
Definition bessel_error_bound (beta : Q) (M : nat) : Q :=
  bessel_term 0 (S M) beta + bessel_term 1 (S M) beta.

Lemma error_b1_M2 : bessel_error_bound 1 2 == (1 # 2304) + (1 # 18432).
Proof.
  unfold bessel_error_bound, bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qeq; simpl; lia.
Qed.

Lemma error_b1_M1 : bessel_error_bound 1 1 == (1 # 64) + (1 # 384).
Proof.
  unfold bessel_error_bound, bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qeq; simpl; lia.
Qed.

Lemma error_decreasing_b1 : bessel_error_bound 1 2 < bessel_error_bound 1 1.
Proof.
  rewrite error_b1_M2, error_b1_M1.
  unfold Qlt; simpl; lia.
Qed.

Lemma plaq_b5_M3_valid : plaquette 5 3 < 1.
Proof. exact plaquette_b5_M3_lt_1. Qed.

Lemma error_b1_M2_positive : 0 < bessel_error_bound 1 2.
Proof. rewrite error_b1_M2. unfold Qlt; simpl; lia. Qed.

(** Convergence: plaquette < 1 at sufficient M *)
Lemma plaq_b1_valid : plaquette 1 2 < 1.
Proof. rewrite plaquette_b1_M2. unfold Qlt; simpl; lia. Qed.

Lemma plaq_b2_valid : plaquette 2 2 < 1.
Proof. exact plaquette_b2_M2_lt_1. Qed.

Lemma plaq_b4_valid : plaquette 4 3 < 1.
Proof. exact plaquette_b4_M3_lt_1. Qed.

Theorem error_bounds_verified :
  0 < bessel_error_bound 1 2 /\
  bessel_error_bound 1 2 < bessel_error_bound 1 1 /\
  plaquette 5 3 < 1.
Proof.
  split; [|split].
  - exact error_b1_M2_positive.
  - exact error_decreasing_b1.
  - exact plaq_b5_M3_valid.
Qed.

Definition fix_count := 10%nat.
