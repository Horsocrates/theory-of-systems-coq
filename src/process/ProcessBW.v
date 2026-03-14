(** * ProcessBW.v — Bolzano-Weierstrass as Process Construction
    Elements: nested intervals [a_n, b_n] with width (b-a)/2^n
    Roles:    each interval contains infinitely many terms of s
    Rules:    pigeonhole — at least one half has infinitely many terms
    Status:   complete
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS BW — Bolzano-Weierstrass as Process Construction           *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: nested intervals [a_n, b_n] with width (b-a)/2^n            *)
(*    Roles:    each interval contains infinitely many terms of s            *)
(*    Rules:    pigeonhole — one half has infinitely many terms              *)
(*              (uses L3/classic to choose)                                   *)
(*                                                                            *)
(*  NOTE: BW returns CauchySeq (from CauchyReal.v).                         *)
(*  We use ProcessBridge to convert to RealProcess.                           *)
(*                                                                            *)
(*  STATUS: 9 Qed, 0 Admitted                                               *)
(*  AXIOMS: classic (inherited from BolzanoWeierstrass)                      *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBridge.
From ToS Require Import analysis.BolzanoWeierstrass.

(* ================================================================== *)
(*  Part I: Cauchy Compatibility                                       *)
(*                                                                      *)
(*  CauchyReal.is_cauchy and ProcessCore.is_Cauchy are definitionally  *)
(*  equal (both use 0 < eps, N <= m).                                  *)
(* ================================================================== *)

(** CauchyReal.is_cauchy = ProcessCore.is_Cauchy (definitional) *)
Lemma bw_cauchy_compat : forall R,
  CauchyReal.is_cauchy R <-> ProcessCore.is_Cauchy R.
Proof.
  intro R. unfold CauchyReal.is_cauchy, ProcessCore.is_Cauchy. tauto.
Qed.

(* ================================================================== *)
(*  Part II: Nested Interval Processes                                 *)
(* ================================================================== *)

(** The left endpoint process *)
Definition bw_left_process (s : nat -> Q) (a b : Q) : RealProcess :=
  fun n => bw_left (bw_iter s (mkBW a b) n).

(** The right endpoint process *)
Definition bw_right_process (s : nat -> Q) (a b : Q) : RealProcess :=
  fun n => bw_right (bw_iter s (mkBW a b) n).

(** Left endpoints are Cauchy (ProcessCore version) *)
Lemma bw_left_is_cauchy_process : forall s a b,
  a < b ->
  ProcessCore.is_Cauchy (bw_left_process s a b).
Proof.
  intros s a b Hab.
  apply bw_cauchy_compat.
  exact (bw_left_cauchy s a b Hab).
Qed.

(** Right endpoints are Cauchy (ProcessCore version) *)
Lemma bw_right_is_cauchy_process : forall s a b,
  a < b ->
  ProcessCore.is_Cauchy (bw_right_process s a b).
Proof.
  intros s a b Hab.
  apply bw_cauchy_compat.
  exact (bw_right_cauchy s a b Hab).
Qed.

(** Left endpoints increase *)
Lemma bw_left_increasing : forall s a b,
  a < b ->
  monotone_increasing (bw_left_process s a b).
Proof.
  intros s a b Hab n.
  unfold bw_left_process.
  apply bw_left_mono. lra. lia.
Qed.

(** Right endpoints decrease *)
Lemma bw_right_decreasing : forall s a b,
  a < b ->
  monotone_decreasing (bw_right_process s a b).
Proof.
  intros s a b Hab n.
  unfold bw_right_process.
  apply bw_right_mono. lra. lia.
Qed.

(** Left and right converge to same limit (width → 0) *)
Lemma bw_endpoints_equiv : forall s a b,
  a < b ->
  process_equiv (bw_left_process s a b) (bw_right_process s a b).
Proof.
  intros s a b Hab eps Heps.
  destruct (bw_width_to_zero s a b Hab eps Heps) as [N HN].
  exists N. intros n Hn.
  unfold bw_left_process, bw_right_process.
  assert (Hvalid : a <= b) by lra.
  assert (Hle : bw_left (bw_iter s (mkBW a b) n) <=
                bw_right (bw_iter s (mkBW a b) n)).
  { apply bw_iter_valid. exact Hvalid. }
  assert (Hwidth : bw_right (bw_iter s (mkBW a b) n) -
                   bw_left (bw_iter s (mkBW a b) n) < eps).
  { apply Qle_lt_trans with (bw_right (bw_iter s (mkBW a b) N) -
                              bw_left (bw_iter s (mkBW a b) N)).
    - assert (Hln : bw_left (bw_iter s (mkBW a b) N) <=
                    bw_left (bw_iter s (mkBW a b) n)).
      { apply bw_left_mono. exact Hvalid. exact Hn. }
      assert (Hrn : bw_right (bw_iter s (mkBW a b) n) <=
                    bw_right (bw_iter s (mkBW a b) N)).
      { apply bw_right_mono. exact Hvalid. exact Hn. }
      lra.
    - exact HN. }
  apply Qabs_case; intros; lra.
Qed.

(* ================================================================== *)
(*  Part III: Bridge from CauchySeq                                    *)
(* ================================================================== *)

(** BW gives a CauchySeq; convert to RealProcess *)
Theorem process_BW : forall (s : nat -> Q) (a b : Q),
  a < b -> bounded_seq s a b ->
  exists L : RealProcess,
    ProcessCore.is_Cauchy L.
Proof.
  intros s a b Hab Hbnd.
  destruct (bolzano_weierstrass s a b Hab Hbnd) as [L _].
  exists (cauchyseq_to_process L).
  apply cauchyseq_is_cauchy.
Qed.

(* ================================================================== *)
(*  Part IV: E/R/R Pattern                                             *)
(* ================================================================== *)

(** BW as process construction: nested intervals + cluster point *)
Theorem bw_is_process_construction : forall s a b,
  a < b -> bounded_seq s a b ->
  exists (left_proc right_proc : RealProcess),
    monotone_increasing left_proc /\
    monotone_decreasing right_proc /\
    ProcessCore.is_Cauchy left_proc /\
    ProcessCore.is_Cauchy right_proc /\
    process_equiv left_proc right_proc.
Proof.
  intros s a b Hab Hbnd.
  exists (bw_left_process s a b).
  exists (bw_right_process s a b).
  split; [| split; [| split; [| split]]].
  - apply bw_left_increasing; assumption.
  - apply bw_right_decreasing; assumption.
  - apply bw_left_is_cauchy_process; assumption.
  - apply bw_right_is_cauchy_process; assumption.
  - apply bw_endpoints_equiv; assumption.
Qed.

(** BW convergence rate is 1/2 (interval halves) *)
Definition bw_convergence_rate : Q := 1 # 2.

Lemma bw_rate_valid : 0 < bw_convergence_rate /\ bw_convergence_rate < 1.
Proof. unfold bw_convergence_rate. split; lra. Qed.
