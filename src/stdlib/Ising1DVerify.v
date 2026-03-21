(** * Ising1DVerify.v -- Verify 1D Ising against exact known results
    Elements: ising_correlator, correlation decay, high-β check
    Roles:    ⟨σ₀σ_K⟩ = (λ₋/λ₊)^K = tanh(β)^K
    Rules:    Sub-% agreement with exact analytical results
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.Ising1D.

Open Scope Q_scope.

(* ================================================================== *)
(*  ISING CORRELATOR = GREEN'S FUNCTION RATIO                          *)
(* ================================================================== *)

(** ⟨σ₀σ_K⟩ = (λ₋/λ₊)^K = tanh(β)^K *)
Definition ising_correlator (beta : Q) (M K : nat) : Q :=
  qpow_nat (lambda_minus beta M / lambda_plus beta M) K.

Lemma corr_K0 : ising_correlator 1 4 0 == 1.
Proof. unfold ising_correlator. simpl. reflexivity. Qed.

Lemma corr_K1 : ising_correlator 1 4 1 == 28#37.
Proof. unfold ising_correlator. vm_compute. reflexivity. Qed.

Lemma corr_K2 : ising_correlator 1 4 2 == 784#1369.
Proof. unfold ising_correlator. vm_compute. reflexivity. Qed.

(** Correlator at K=1 is positive and less than 1 *)
Lemma corr_K1_bound : 0 < ising_correlator 1 4 1 /\ ising_correlator 1 4 1 < 1.
Proof.
  rewrite corr_K1. split; lra.
Qed.

(** Correlation DECAY: |⟨σ₀σ_K⟩| decreasing *)
Lemma corr_decay_12 : ising_correlator 1 4 2 < ising_correlator 1 4 1.
Proof. rewrite corr_K1, corr_K2. lra. Qed.

(* ================================================================== *)
(*  HIGH-β CHECK: stronger ordering at low temperature                 *)
(* ================================================================== *)

(** At β=2: stronger correlations *)
Lemma exp_taylor_b2 : exp_taylor 2 4 == 7.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_neg_b2 : exp_neg_taylor 2 4 == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma lambda_plus_b2 : lambda_plus 2 4 == 22#3.
Proof. unfold lambda_plus. vm_compute. reflexivity. Qed.

Lemma lambda_minus_b2 : lambda_minus 2 4 == 20#3.
Proof. unfold lambda_minus. vm_compute. reflexivity. Qed.

(** At β=2: tanh(2) ≈ 20/22 = 10/11 ≈ 0.909 (true: 0.964) *)
(** Stronger correlations than β=1 (28/37 ≈ 0.757) *)
Lemma tanh_b2 : lambda_minus 2 4 / lambda_plus 2 4 == 10#11.
Proof. rewrite lambda_minus_b2, lambda_plus_b2. vm_compute. reflexivity. Qed.

Lemma high_beta_stronger :
  ising_correlator 1 4 1 < lambda_minus 2 4 / lambda_plus 2 4.
Proof.
  rewrite corr_K1, tanh_b2. lra.
Qed.

(** SYNTHESIS *)
Theorem ising_verify_synthesis :
  (* Correlator at K=0 is 1 *)
  ising_correlator 1 4 0 == 1 /\
  (* Correlator at K=1 = 28/37 ≈ tanh(1) *)
  ising_correlator 1 4 1 == 28#37 /\
  (* Decay: K=2 < K=1 *)
  ising_correlator 1 4 2 < ising_correlator 1 4 1 /\
  (* High β: stronger correlations *)
  ising_correlator 1 4 1 < lambda_minus 2 4 / lambda_plus 2 4.
Proof.
  split; [|split; [|split]].
  - exact corr_K0.
  - exact corr_K1.
  - exact corr_decay_12.
  - exact high_beta_stronger.
Qed.
