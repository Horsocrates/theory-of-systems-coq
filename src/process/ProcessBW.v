(** * ProcessBW.v — Bolzano-Weierstrass as Process Construction
    Elements: nested intervals [a_n, b_n] with width (b-a)/2^n
    Roles:    each interval contains infinitely many terms of s
    Rules:    pigeonhole — at least one half has infinitely many terms
    Status:   complete
    STATUS: 10 Qed, 0 Admitted, 0 axioms
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
(*  STATUS: 10 Qed, 0 Admitted                                              *)
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

(** Bolzano-Weierstrass in process language: a Cauchy process L inside [a,b]
    such that every far stage of L is approached, within eps, by terms of s
    with arbitrarily large indices (a cluster point).  Witness: the process
    of left endpoints of the bisection.
    Until Nov 2026 the conclusion was only [exists L, is_Cauchy L]: it did
    not mention s and held for the zero process. *)
Theorem process_BW : forall (s : nat -> Q) (a b : Q),
  a < b -> bounded_seq s a b ->
  exists L : RealProcess,
    ProcessCore.is_Cauchy L /\
    ProcessCore.in_interval a b L /\
    forall eps : Q, 0 < eps ->
      exists M0 : nat, forall M : nat, (M0 <= M)%nat ->
        forall N : nat, exists k : nat, (N <= k)%nat /\ Qabs (L M - s k) < eps.
Proof.
  intros s a b Hab Hbnd.
  assert (Hvalid : a <= b) by lra.
  exists (bw_left_process s a b). split; [| split].
  - apply bw_left_is_cauchy_process; assumption.
  - intro n. unfold bw_left_process.
    pose proof (bw_left_mono s a b Hvalid 0%nat n ltac:(lia)) as H1.
    pose proof (bw_right_mono s a b Hvalid 0%nat n ltac:(lia)) as H3.
    assert (H2 : bw_left (bw_iter s (mkBW a b) n) <= bw_right (bw_iter s (mkBW a b) n)).
    { apply bw_iter_valid. exact Hvalid. }
    simpl in H1, H3. split; lra.
  - intros eps Heps.
    destruct (bw_width_to_zero s a b Hab eps Heps) as [M0 HM0].
    exists M0. intros M HM N.
    destruct (bw_infinitely_many s a b M0 Hvalid Hbnd N) as [k [HkN [Hklo Hkhi]]].
    exists k. split; [exact HkN|].
    unfold bw_left_process.
    pose proof (bw_left_mono s a b Hvalid M0 M HM) as H1.
    pose proof (bw_right_mono s a b Hvalid M0 M HM) as H3.
    assert (H2 : bw_left (bw_iter s (mkBW a b) M) <= bw_right (bw_iter s (mkBW a b) M)).
    { apply bw_iter_valid. exact Hvalid. }
    apply Qabs_case; intros; lra.
Qed.

(* ================================================================== *)
(*  Part IV: E/R/R Pattern                                             *)
(* ================================================================== *)

(** BW as process construction: the two processes of bisection endpoints,
    BY NAME, and the role of every stage -- the interval between them holds
    terms of s with arbitrarily large indices.
    Until Nov 2026 the two processes stood under [exists] and were not tied
    to s: the conclusion held for a pair of zero processes. *)
Theorem bw_is_process_construction : forall s a b,
  a < b -> bounded_seq s a b ->
    monotone_increasing (bw_left_process s a b) /\
    monotone_decreasing (bw_right_process s a b) /\
    ProcessCore.is_Cauchy (bw_left_process s a b) /\
    ProcessCore.is_Cauchy (bw_right_process s a b) /\
    process_equiv (bw_left_process s a b) (bw_right_process s a b) /\
    (forall n, infinitely_many_in s (bw_left_process s a b n) (bw_right_process s a b n)).
Proof.
  intros s a b Hab Hbnd.
  split; [| split; [| split; [| split; [| split]]]].
  - apply bw_left_increasing; assumption.
  - apply bw_right_decreasing; assumption.
  - apply bw_left_is_cauchy_process; assumption.
  - apply bw_right_is_cauchy_process; assumption.
  - apply bw_endpoints_equiv; assumption.
  - intro n. unfold bw_left_process, bw_right_process.
    apply bw_infinitely_many; [lra | exact Hbnd].
Qed.

(** BW convergence rate is 1/2 (interval halves) *)
Definition bw_convergence_rate : Q := 1 # 2.

Lemma bw_rate_valid : 0 < bw_convergence_rate /\ bw_convergence_rate < 1.
Proof. unfold bw_convergence_rate. split; lra. Qed.

(** The number is tied to the process: the width of the bisection interval
    at stage n+1 is the width at stage n times the rate (Nov 2026). *)
Lemma bw_rate_is_width_ratio : forall s a b n,
  bw_right_process s a b (S n) - bw_left_process s a b (S n) ==
  bw_convergence_rate * (bw_right_process s a b n - bw_left_process s a b n).
Proof.
  intros s a b n. unfold bw_right_process, bw_left_process. simpl bw_iter.
  rewrite bw_step_width. unfold bw_convergence_rate. field.
Qed.
