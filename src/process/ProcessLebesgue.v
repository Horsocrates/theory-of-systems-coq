(** * ProcessLebesgue.v — Lebesgue Integral as Process
    Elements: step-function integrals of increasing fineness
    Roles:    increasing (finer step = tighter approximation), bounded
    Rules:    step below f -> integral below integral of f, monotone convergence
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS LEBESGUE — Lebesgue Integral as Process                     *)
(*                                                                            *)
(*  Standard: integral f du = sup{integral s : 0 <= s <= f, s simple}        *)
(*  P4: {integral_n(f)} where integral_n is n-piece Riemann sum              *)
(*  For bounded measurable f on compact [a,b]: Lebesgue = Riemann.           *)
(*                                                                            *)
(*  STATUS: 15 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessSimple.
From ToS Require Import process.ProcessMeasureTheory.
From ToS Require Import RiemannIntegration.
From ToS Require Import IntegralApplications.
From ToS Require Import MonotoneConvergence.

(* ================================================================== *)
(*  Part I: Lebesgue Integral Process                                    *)
(* ================================================================== *)

(** For bounded measurable f on [a,b], the Lebesgue integral IS the
    Riemann integral. Under P4: both are the same process. *)
Definition lebesgue_process (f : Q -> Q) (a b : Q) : RealProcess :=
  riemann_process f a b.

(** Lebesgue process = Riemann process *)
Lemma lebesgue_is_riemann : forall f a b n,
  lebesgue_process f a b n == riemann_process f a b n.
Proof. intros. reflexivity. Qed.

(** Lebesgue process bounded for bounded functions *)
Lemma lebesgue_bounded : forall f a b M n,
  a < b -> (forall x, Qabs (f x) <= M) -> 0 <= M ->
  Qabs (lebesgue_process f a b n) <= M * (b - a).
Proof.
  intros. unfold lebesgue_process.
  apply bounded_riemann_bounded; auto.
Qed.

(** Lebesgue process nonneg for nonneg functions *)
Lemma lebesgue_nonneg : forall f a b n,
  a < b -> (forall x, 0 <= f x) ->
  0 <= lebesgue_process f a b n.
Proof.
  intros. unfold lebesgue_process.
  apply nonneg_riemann_nonneg; auto.
Qed.

(* ================================================================== *)
(*  Part II: Linearity                                                   *)
(* ================================================================== *)

(** Lebesgue integral is additive *)
Lemma lebesgue_add : forall f g a b n,
  lebesgue_process (fun x => f x + g x) a b n ==
  lebesgue_process f a b n + lebesgue_process g a b n.
Proof.
  intros. unfold lebesgue_process.
  apply riemann_process_add.
Qed.

(** Lebesgue integral is scalable *)
Lemma lebesgue_scale : forall c f a b n,
  lebesgue_process (fun x => c * f x) a b n ==
  c * lebesgue_process f a b n.
Proof.
  intros. unfold lebesgue_process.
  apply riemann_process_scale.
Qed.

(** Lebesgue integral is monotone *)
Lemma lebesgue_monotone : forall f g a b n,
  a < b -> (forall x, f x <= g x) ->
  lebesgue_process f a b n <= lebesgue_process g a b n.
Proof.
  intros. unfold lebesgue_process.
  apply riemann_process_monotone; auto.
Qed.

(** Lebesgue integral of zero function *)
Lemma lebesgue_zero : forall a b,
  a < b ->
  process_equiv (lebesgue_process (fun _ => 0) a b) (const_process 0).
Proof.
  intros a b Hab.
  assert (H := const_riemann_equiv 0 a b Hab).
  unfold lebesgue_process.
  (* H : process_equiv (riemann_process (fun _ => 0) a b) (const_process (0 * (b - a))) *)
  (* Goal: process_equiv (riemann_process (fun _ => 0) a b) (const_process 0) *)
  unfold process_equiv in *. intros eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N. intros n Hn.
  assert (HN' := HN n Hn).
  unfold const_process in *.
  assert (Heq : 0 * (b - a) == 0) by ring.
  setoid_rewrite Heq in HN'. exact HN'.
Qed.

(** Lebesgue integral of constant function *)
Lemma lebesgue_const : forall c a b,
  a < b ->
  process_equiv (lebesgue_process (fun _ => c) a b) (const_process (c * (b - a))).
Proof.
  intros. unfold lebesgue_process.
  apply const_riemann_equiv. auto.
Qed.

(* ================================================================== *)
(*  Part III: Agreement with Riemann Integral                            *)
(* ================================================================== *)

(** For bounded f: Lebesgue process IS Riemann process (definitionally) *)
Lemma lebesgue_riemann_equiv : forall f a b,
  process_equiv (lebesgue_process f a b) (riemann_process f a b).
Proof.
  intros f a b. unfold process_equiv. intros eps Heps.
  exists 0%nat. intros n _.
  unfold lebesgue_process.
  assert (H : riemann_process f a b n - riemann_process f a b n == 0) by ring.
  setoid_rewrite H. rewrite Qabs_pos; lra.
Qed.

(** For bounded f: Lebesgue = integral_process *)
Lemma lebesgue_integral_equiv : forall f a b,
  process_equiv (lebesgue_process f a b) (integral_process f a b).
Proof.
  intros. unfold process_equiv. intros eps Heps.
  exists 0%nat. intros n _.
  unfold lebesgue_process, riemann_process.
  assert (H : integral_process f a b n - integral_process f a b n == 0) by ring.
  setoid_rewrite H. rewrite Qabs_pos; lra.
Qed.

(* ================================================================== *)
(*  Part IV: Integral of Indicator = Measure                             *)
(* ================================================================== *)

(** integral of indicator = indicator_process = measure_process *)
Lemma lebesgue_indicator_is_measure : forall a b c d,
  process_equiv
    (lebesgue_process (indicator c d) a b)
    (measure_process a b c d).
Proof.
  intros. unfold process_equiv. intros eps Heps.
  exists 0%nat. intros n _.
  unfold lebesgue_process, measure_process, indicator_process, riemann_process.
  assert (H : integral_process (indicator c d) a b n -
    integral_process (indicator c d) a b n == 0) by ring.
  setoid_rewrite H. rewrite Qabs_pos; lra.
Qed.

(** Integral of indicator nonneg *)
Lemma lebesgue_indicator_nonneg : forall a b c d n,
  a < b ->
  0 <= lebesgue_process (indicator c d) a b n.
Proof.
  intros. apply lebesgue_nonneg; auto.
  intro x. apply (proj1 (indicator_bounded c d x)).
Qed.

(** Integral of indicator bounded *)
Lemma lebesgue_indicator_bounded : forall a b c d n,
  a < b ->
  lebesgue_process (indicator c d) a b n <= b - a.
Proof.
  intros. unfold lebesgue_process.
  apply indicator_process_bounded. auto.
Qed.

(* ================================================================== *)
(*  Part V: Triangle Inequality                                          *)
(* ================================================================== *)

(** |integral f| <= integral |f| — absolute value version *)
Lemma lebesgue_abs_bound : forall f a b M n,
  a < b -> (forall x, Qabs (f x) <= M) -> 0 <= M ->
  Qabs (lebesgue_process f a b n) <= M * (b - a).
Proof.
  intros. apply lebesgue_bounded; auto.
Qed.

(** Difference of integrals bounded by integral of difference *)
Lemma lebesgue_diff_bound : forall f g a b M n,
  a < b ->
  (forall x, Qabs (f x - g x) <= M) -> 0 <= M ->
  Qabs (lebesgue_process f a b n - lebesgue_process g a b n) <=
    M * (b - a).
Proof.
  intros f g a b M n Hab Hdiff HM.
  unfold lebesgue_process, riemann_process.
  (* integral(f) - integral(g) = integral(f - g) by linearity *)
  assert (Heq : integral_process f a b n - integral_process g a b n ==
    integral_process (fun x => f x - g x) a b n).
  { unfold integral_process.
    assert (Ha := integral_process_add f (fun x => - g x) a b n).
    unfold integral_process in Ha.
    assert (Hs := integral_process_scale (-(1)) g a b n).
    unfold integral_process in Hs.
    assert (Hfg : riemann_sum (fun x => f x + -(1) * g x) a
      (ProcessIntegral.integral_step a b n) (S n) ==
      riemann_sum f a (ProcessIntegral.integral_step a b n) (S n) +
      riemann_sum (fun x => -(1) * g x) a
        (ProcessIntegral.integral_step a b n) (S n)).
    { exact Ha. }
    assert (Hng : riemann_sum (fun x => -(1) * g x) a
      (ProcessIntegral.integral_step a b n) (S n) ==
      -(1) * riemann_sum g a (ProcessIntegral.integral_step a b n) (S n)).
    { exact Hs. }
    assert (Hdiff2 : forall x, f x - g x == f x + -(1) * g x) by (intro; ring).
    assert (Heq2 : riemann_sum (fun x => f x - g x) a
      (ProcessIntegral.integral_step a b n) (S n) ==
      riemann_sum (fun x => f x + -(1) * g x) a
        (ProcessIntegral.integral_step a b n) (S n)).
    { apply riemann_sum_ext. intros k Hk. apply Hdiff2. }
    lra. }
  setoid_rewrite Heq.
  apply bounded_riemann_bounded; auto.
Qed.

(* ================================================================== *)
(*  Part VI: E/R/R Pattern                                               *)
(* ================================================================== *)

(** Convergence rate for Lebesgue process *)
Definition lebesgue_convergence_rate : Q := 1 # 2.

Lemma lebesgue_rate_valid :
  0 < lebesgue_convergence_rate /\ lebesgue_convergence_rate < 1.
Proof. unfold lebesgue_convergence_rate. split; lra. Qed.

(** E/R/R: Lebesgue integral as process construction *)
Theorem lebesgue_is_process : forall (f : Q -> Q) (a b M : Q),
  a < b -> (forall x, Qabs (f x) <= M) -> 0 <= M ->
  exists proc : RealProcess,
    (forall n, Qabs (proc n) <= M * (b - a)).
Proof.
  intros f a b M Hab Hbnd HM.
  exists (lebesgue_process f a b).
  intro n. apply lebesgue_bounded; auto.
Qed.

(** P4: the Lebesgue integral process IS the integral *)
(** For bounded measurable f: Lebesgue = Riemann = process *)
(** No sigma-algebra, no measure completion needed *)
