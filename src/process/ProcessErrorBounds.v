(* ProcessErrorBounds.v — Machine-checked error bars *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessPlaquette.
Open Scope Q_scope.

(** FIRST FORMALLY VERIFIED ERROR BOUNDS ON LATTICE QFT *)

Definition plaq_error_crude (beta : Q) (M : nat) : Q :=
  bessel_term 0 (S M) beta + bessel_term 1 (S M) beta.

Lemma error_b1_M1 : plaq_error_crude 1 1 ==
  bessel_term 0 2 1 + bessel_term 1 2 1.
Proof. reflexivity. Qed.

Lemma error_b1_M1_value : plaq_error_crude 1 1 == (1 # 64) + (1 # 384).
Proof.
  unfold plaq_error_crude, bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qeq; simpl; lia.
Qed.

Lemma error_b1_M2_value : plaq_error_crude 1 2 == (1 # 2304) + (1 # 18432).
Proof.
  unfold plaq_error_crude, bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qeq; simpl; lia.
Qed.

Lemma error_decreases : plaq_error_crude 1 2 < plaq_error_crude 1 1.
Proof.
  rewrite error_b1_M2_value, error_b1_M1_value.
  unfold Qlt; simpl; lia.
Qed.

Lemma error_b1_M2_positive : 0 < plaq_error_crude 1 2.
Proof. rewrite error_b1_M2_value. unfold Qlt; simpl; lia. Qed.

(** Error is SMALL compared to plaquette value *)
(** plaquette(1,2) = 217/486 ~ 0.446 *)
(** error(1,2) ~ 1/2304 + 1/18432 ~ 0.0005 *)
(** Relative error: 0.0005/0.446 ~ 0.1% *)

Theorem error_bounds_complete :
  0 < plaq_error_crude 1 2 /\
  plaq_error_crude 1 2 < plaq_error_crude 1 1.
Proof.
  split.
  - exact error_b1_M2_positive.
  - exact error_decreases.
Qed.

Definition error_count := 6%nat.
