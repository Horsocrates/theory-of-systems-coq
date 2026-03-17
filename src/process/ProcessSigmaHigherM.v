(** * ProcessSigmaHigherM.v -- Sigma at Higher M: Bessel Truncation Effects
    Theory of Systems - Phase 50.5: Multi-Term Bessel Comparison

    Elements: eigenvalues at M=1 (two Bessel terms), sigma(M) process
    Roles:    M=1 adds correction terms to each eigenvalue
    Rules:    M=1 extends validity range
    Status:   complete

    Key finding: sigma(M=1) > sigma(M=0) at both beta=1,2.
    The partial Bessel sum approach changes eigenvalue RATIOS
    non-monotonically. Adding terms to numerator and denominator
    of t1/t0 does not guarantee monotone convergence of the ratio.

    M=1 DOES extend validity: t0(beta=3, M=0) = -1/8 < 0 but
    t0(beta=3, M=1) = 41/32 > 0. More Bessel terms = wider beta range.

    STATUS: ~30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.SpectralGapCorrect.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import process.ProcessSigmaCurve.
From ToS Require Import process.ProcessGlueballMass.

(* ================================================================== *)
(*  Part I: Eigenvalues at M=1 (~10 lemmas)                           *)
(* ================================================================== *)

(** Eigenvalue definitions at M=1 *)
Definition t0_M1 (beta : Q) : Q := transfer_eigenvalue 0 beta 1.
Definition t1_M1 (beta : Q) : Q := transfer_eigenvalue 1 beta 1.
Definition t2_M1 (beta : Q) : Q := transfer_eigenvalue 2 beta 1.

(** t0(beta=1, M=1) = 107/96 *)
Lemma t0_M1_beta_1 : t0_M1 1 == 107 # 96.
Proof.
  unfold t0_M1, transfer_eigenvalue.
  unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** t1(beta=1, M=1) = 1019/7680 *)
Lemma t1_M1_beta_1 : t1_M1 1 == 1019 # 7680.
Proof.
  unfold t1_M1, transfer_eigenvalue.
  unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** t0(beta=2, M=1) = 4/3 *)
Lemma t0_M1_beta_2 : t0_M1 2 == 4 # 3.
Proof.
  unfold t0_M1, transfer_eigenvalue.
  unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** t1(beta=2, M=1) = 37/60 *)
Lemma t1_M1_beta_2 : t1_M1 2 == 37 # 60.
Proof.
  unfold t1_M1, transfer_eigenvalue.
  unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

(** t0(beta=1, M=1) > 0 *)
Lemma t0_M1_positive_beta_1 : 0 < t0_M1 1.
Proof. rewrite t0_M1_beta_1. lra. Qed.

(** t0(beta=2, M=1) > 0 *)
Lemma t0_M1_positive_beta_2 : 0 < t0_M1 2.
Proof. rewrite t0_M1_beta_2. lra. Qed.

(** t0(beta=3, M=1) = 41/32 > 0.
    M=1 EXTENDS validity range.
    t0(beta=3, M=0) = -1/8 < 0 (invalid).
    With two Bessel terms the correction fixes the sign. *)
Lemma t0_M1_beta_3 : t0_M1 3 == 41 # 32.
Proof.
  unfold t0_M1, transfer_eigenvalue.
  unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qeq. simpl. lia.
Qed.

Lemma t0_M1_beta_3_positive : 0 < t0_M1 3.
Proof. rewrite t0_M1_beta_3. lra. Qed.

(** M=1 extends validity: beta=3 now valid (was invalid at M=0) *)
Theorem m1_extends_validity :
  t0_M0 3 < 0 /\ 0 < t0_M1 3.
Proof.
  split.
  - exact t0_beta_3_negative.
  - exact t0_M1_beta_3_positive.
Qed.

(* ================================================================== *)
(*  Part II: Sigma at M=1 (~10 lemmas)                                *)
(* ================================================================== *)

(** Gap at M=1 *)
Definition gap_M1 (beta : Q) : Q := t0_M1 beta - t1_M1 beta.

(** Relative gap at M=1 *)
Definition rel_gap_M1 (beta : Q) : Q := gap_M1 beta / t0_M1 beta.

(** Sigma at M=1 *)
Definition sigma_M1 (beta : Q) (order : nat) : Q :=
  neg_ln_taylor (rel_gap_M1 beta) order.

(** Gap at beta=1, M=1 *)
Lemma gap_M1_beta_1 : gap_M1 1 == 7541 # 7680.
Proof.
  unfold gap_M1.
  rewrite t0_M1_beta_1. rewrite t1_M1_beta_1.
  unfold Qeq. simpl. lia.
Qed.

(** Relative gap at beta=1, M=1 = 7541/8560 *)
Lemma rel_gap_M1_beta_1 : rel_gap_M1 1 == 7541 # 8560.
Proof.
  unfold rel_gap_M1.
  rewrite gap_M1_beta_1. rewrite t0_M1_beta_1.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

(** sigma(beta=1, M=1, order 1) = 7541/8560 ~ 0.881 *)
Lemma sigma_M1_beta_1_order_1 : sigma_M1 1 1 == 7541 # 8560.
Proof.
  unfold sigma_M1.
  assert (Hx : rel_gap_M1 1 == 7541 # 8560) by exact rel_gap_M1_beta_1.
  assert (Htlr := taylor_order_1 (rel_gap_M1 1)).
  lra.
Qed.

(** Gap at beta=2, M=1 *)
Lemma gap_M1_beta_2 : gap_M1 2 == 43 # 60.
Proof.
  unfold gap_M1.
  rewrite t0_M1_beta_2. rewrite t1_M1_beta_2.
  unfold Qeq. simpl. lia.
Qed.

(** Relative gap at beta=2, M=1 = 43/80 *)
Lemma rel_gap_M1_beta_2 : rel_gap_M1 2 == 43 # 80.
Proof.
  unfold rel_gap_M1.
  rewrite gap_M1_beta_2. rewrite t0_M1_beta_2.
  unfold Qdiv, Qeq. simpl. lia.
Qed.

(** sigma(beta=2, M=1, order 1) = 43/80 ~ 0.538 *)
Lemma sigma_M1_beta_2_order_1 : sigma_M1 2 1 == 43 # 80.
Proof.
  unfold sigma_M1.
  assert (Hx : rel_gap_M1 2 == 43 # 80) by exact rel_gap_M1_beta_2.
  assert (Htlr := taylor_order_1 (rel_gap_M1 2)).
  lra.
Qed.

(** rel_gap < 1 at both couplings (Taylor converges) *)
Lemma rel_gap_M1_lt_1 :
  rel_gap_M1 1 < 1 /\ rel_gap_M1 2 < 1.
Proof.
  split; [rewrite rel_gap_M1_beta_1 | rewrite rel_gap_M1_beta_2]; lra.
Qed.

(* ================================================================== *)
(*  Part III: M=0 vs M=1 Comparison (~5 lemmas)                       *)
(* ================================================================== *)

(** HONEST RESULT: sigma(M=1) > sigma(M=0) at beta=1
    M=0: 289/336 ~ 0.860, M=1: 7541/8560 ~ 0.881
    INCREASED, not decreased toward exact 0.764 *)
Theorem sigma_M1_gt_M0_beta_1 :
  string_tension 1 1 < sigma_M1 1 1.
Proof.
  rewrite sigma_order_1. rewrite sigma_M1_beta_1_order_1. lra.
Qed.

(** HONEST RESULT: sigma(M=1) > sigma(M=0) at beta=2
    M=0: 1/12 ~ 0.083, M=1: 43/80 ~ 0.538
    DRAMATICALLY increased, not toward exact 0.108 *)
Theorem sigma_M1_gt_M0_beta_2 :
  string_tension 2 1 < sigma_M1 2 1.
Proof.
  rewrite sigma_beta_2_order_1. rewrite sigma_M1_beta_2_order_1. lra.
Qed.

(** WHY sigma(M) does not converge monotonically toward physical sigma:
    Adding Bessel terms increases BOTH t0 and t1.
    - t0(M=0 to 1): 1/2 to 4/3 (x2.67 at beta=2)
    - t1(M=0 to 1): 11/24 to 37/60 (x1.35 at beta=2)
    - t0 grows FASTER, gap/t0 increases, sigma increases.
    The eigenvalue RATIO t1/t0 at M=0 was 11/12 ~ 0.917.
    At M=1: t1/t0 = 37/80 = 0.4625 (much smaller).
    So -ln(t1/t0) at M=1 is MUCH larger.

    Physical sigma requires the FULL Bessel function ratio,
    not partial sum differences. Our framework computes a
    partial-sum-based observable that is exact Q at each M. *)

(** Both sigma values are positive *)
Lemma sigma_M1_positive :
  0 < sigma_M1 1 1 /\ 0 < sigma_M1 2 1.
Proof.
  split.
  - assert (H := sigma_M1_gt_M0_beta_1).
    assert (Hp := sigma_order_1_positive). lra.
  - assert (H := sigma_M1_gt_M0_beta_2).
    assert (Hp := sigma_beta_2_positive). lra.
Qed.

(* ================================================================== *)
(*  Part IV: Sigma(M) Process and Validity (~7 lemmas)                *)
(* ================================================================== *)

(** Sigma as process in M *)
Definition sigma_M_process (beta : Q) (order : nat) : RealProcess :=
  fun M =>
    let t0 := transfer_eigenvalue 0 beta M in
    let t1 := transfer_eigenvalue 1 beta M in
    let rg := (t0 - t1) / t0 in
    neg_ln_taylor rg order.

(** sigma(M=0) matches string_tension *)
Lemma sigma_M_at_0 : forall beta order,
  sigma_M_process beta order 0%nat == string_tension beta order.
Proof. intros. unfold sigma_M_process, string_tension. reflexivity. Qed.

(** sigma(M=1) matches sigma_M1 *)
Lemma sigma_M_at_1 : forall beta order,
  sigma_M_process beta order 1%nat == sigma_M1 beta order.
Proof.
  intros. unfold sigma_M_process, sigma_M1, rel_gap_M1, gap_M1.
  reflexivity.
Qed.

(** Each point of sigma(M) is a definite Q number *)
Lemma sigma_M_is_Q : forall beta order M,
  exists q : Q, sigma_M_process beta order M == q.
Proof.
  intros. exists (sigma_M_process beta order M). reflexivity.
Qed.

(** The sigma(M) process at beta=1 *)
Lemma sigma_M_process_beta_1 :
  sigma_M_process 1 1 0%nat == 289 # 336 /\
  sigma_M_process 1 1 1%nat == 7541 # 8560.
Proof.
  split.
  - rewrite sigma_M_at_0. exact sigma_order_1.
  - rewrite sigma_M_at_1. exact sigma_M1_beta_1_order_1.
Qed.

(** The sigma(M) process at beta=2 *)
Lemma sigma_M_process_beta_2 :
  sigma_M_process 2 1 0%nat == 1 # 12 /\
  sigma_M_process 2 1 1%nat == 43 # 80.
Proof.
  split.
  - rewrite sigma_M_at_0. exact sigma_beta_2_order_1.
  - rewrite sigma_M_at_1. exact sigma_M1_beta_2_order_1.
Qed.

(** Validity range comparison *)
Theorem validity_comparison :
  (* M=0: valid for beta=1,2; invalid at beta=3 *)
  0 < t0_M0 1 /\ 0 < t0_M0 2 /\ t0_M0 3 < 0 /\
  (* M=1: valid for beta=1,2,3 *)
  0 < t0_M1 1 /\ 0 < t0_M1 2 /\ 0 < t0_M1 3.
Proof.
  split; [exact t0_beta_1_pos |
  split; [exact t0_beta_2_pos |
  split; [exact t0_beta_3_negative |
  split; [exact t0_M1_positive_beta_1 |
  split; [exact t0_M1_positive_beta_2 | exact t0_M1_beta_3_positive]]]]].
Qed.

(** Phase 50.5 summary *)
Theorem phase_50_5_complete :
  (* Eigenvalues at M=1: t0,t1 computed at beta=1,2,3 *)
  (* M=1 extends validity: t0(beta=3) > 0 (was < 0 at M=0) *)
  (* sigma(M=1) > sigma(M=0) at both beta=1,2 *)
  (* Reason: partial Bessel sums change eigenvalue ratios non-monotonically *)
  (* The sigma(M) process exists: each M gives exact Q *)
  (* Physical sigma requires full Bessel functions, not partial sums *)
  True.
Proof. exact I. Qed.
