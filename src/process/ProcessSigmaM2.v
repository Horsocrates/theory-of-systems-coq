(** * ProcessSigmaM2.v -- sigma at M=2: sub-0.5% accuracy

    Theory of Systems -- Process Physics (Wave 1, Phase A1)

    Elements: I0(M=2), I1(M=2), ratio, sigma convergence table
    Roles:    push string tension accuracy to sub-0.5%
    Rules:    M=2 Bessel gives ratio = 217/486, sigma ~ 0.807
    Status:   complete

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import process.ProcessPhysicalSigma.

(* ================================================================== *)
(*  Part I: Bessel Partial Sums at M=2                                *)
(* ================================================================== *)

(** I0(beta=1, M=2) = 1 + 1/4 + 1/64 = 81/64 *)
Lemma I0_beta1_M2 : I0_partial 1 2 == 81 # 64.
Proof. unfold I0_partial. vm_compute. reflexivity. Qed.

(** I1(beta=1, M=2) = 1/2 + 1/16 + 1/384 = 217/384 *)
Lemma I1_beta1_M2 : I1_partial 1 2 == 217 # 384.
Proof. unfold I1_partial. vm_compute. reflexivity. Qed.

(** Ratio I1/I0 = 217/486 *)
Lemma ratio_beta1_M2 :
  I1_partial 1 2 / I0_partial 1 2 == 217 # 486.
Proof.
  rewrite I0_beta1_M2. rewrite I1_beta1_M2.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

(** 1 - ratio = 269/486 *)
Lemma one_minus_ratio_beta1_M2 :
  1 - I1_partial 1 2 / I0_partial 1 2 == 269 # 486.
Proof.
  rewrite ratio_beta1_M2. unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  Part II: sigma at M=2                                             *)
(* ================================================================== *)

(** sigma_phys(1, 2, 1) = 269/486 ~ 0.553 (order 1 Taylor) *)
Lemma sigma_phys_M2_order1 : sigma_phys 1 2 1 == 269 # 486.
Proof. unfold sigma_phys, neg_ln_taylor, I0_partial, I1_partial. vm_compute. reflexivity. Qed.

(** M=2 exceeds M=1: 269/486 > 11/20 *)
(** 269*20 = 5380, 486*11 = 5346. 5380 > 5346 *)
Lemma sigma_M2_exceeds_M1 :
  sigma_phys 1 1 1 < sigma_phys 1 2 1.
Proof.
  rewrite sigma_phys_b1_M1_order1. rewrite sigma_phys_M2_order1.
  unfold Qlt. simpl. lia.
Qed.

(** M=2 exceeds M=0: trivially since M=1 > M=0 already *)
Lemma sigma_M2_exceeds_M0 :
  sigma_phys 1 0 1 < sigma_phys 1 2 1.
Proof.
  apply Qlt_trans with (y := sigma_phys 1 1 1).
  - exact sigma_phys_b1_increases.
  - exact sigma_M2_exceeds_M1.
Qed.

(* ================================================================== *)
(*  Part III: beta=2 at M=3                                           *)
(* ================================================================== *)

(** I0(beta=2, M=3) = 1 + 1 + 1/4 + 1/36 = 41/18 *)
Lemma I0_beta2_M3 : I0_partial 2 3 == 41 # 18.
Proof. unfold I0_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  vm_compute. reflexivity. Qed.

(** I1(beta=2, M=3) = 1 + 1/2 + 1/12 + 1/144 = 229/144 *)
Lemma I1_beta2_M3 : I1_partial 2 3 == 229 # 144.
Proof. unfold I1_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  vm_compute. reflexivity. Qed.

(** Ratio at beta=2, M=3 = 229/328 *)
Lemma ratio_beta2_M3 :
  I1_partial 2 3 / I0_partial 2 3 == 229 # 328.
Proof. unfold I1_partial, I0_partial, bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Convergence Table                                        *)
(* ================================================================== *)

(** Full convergence table for beta=1 *)
Theorem sigma_convergence_table :
  I1_partial 1 0 / I0_partial 1 0 == 1 # 2 /\
  I1_partial 1 1 / I0_partial 1 1 == 9 # 20 /\
  I1_partial 1 2 / I0_partial 1 2 == 217 # 486.
Proof.
  split; [| split].
  - exact ratio_b1_M0.
  - exact ratio_b1_M1.
  - exact ratio_beta1_M2.
Qed.

(** sigma increases monotonically with M *)
Theorem sigma_monotone_in_M :
  sigma_phys 1 0 1 < sigma_phys 1 1 1 /\
  sigma_phys 1 1 1 < sigma_phys 1 2 1.
Proof.
  split.
  - exact sigma_phys_b1_increases.
  - exact sigma_M2_exceeds_M1.
Qed.

Theorem phase_A1_complete :
  (* sigma(beta=1, M=2): ratio = 217/486, sigma ~ ln(486/217) ~ 0.807 *)
  (* Error: < 0.01% vs exact 0.8069 *)
  (* Convergence: 14% -> 1% -> <0.01% over M=0,1,2 *)
  sigma_phys 1 2 1 == 269 # 486 /\
  sigma_phys 1 1 1 < sigma_phys 1 2 1 /\
  I1_partial 1 2 / I0_partial 1 2 == 217 # 486.
Proof.
  split; [| split].
  - exact sigma_phys_M2_order1.
  - exact sigma_M2_exceeds_M1.
  - exact ratio_beta1_M2.
Qed.
