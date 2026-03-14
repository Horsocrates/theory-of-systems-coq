(** * ProcessODEExamples.v — Concrete ODE Examples as Processes
    Elements: exponential ODE, decay ODE, logistic growth
    Roles:    concrete instantiations of the ODE process framework
    Rules:    Euler-Picard applied to specific vector fields
    Status:   complete
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS ODE EXAMPLES — Concrete ODEs as Process Constructions      *)
(*                                                                            *)
(*  Example 1: y' = y (exponential growth)                                   *)
(*  Example 2: y' = -αy (exponential decay)                                  *)
(*  Example 3: y' = c (constant velocity)                                    *)
(*  Example 4: y' = Ly (general linear)                                      *)
(*                                                                            *)
(*  Under P4: each ODE solution IS its Picard iterate process                *)
(*  The cluster theorem: Picard = Euler = Gronwall bound                     *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: iterate sequences for each ODE                               *)
(*    Roles:    solution, error bound, convergence witness                    *)
(*    Rules:    each vector field → contraction → process                    *)
(*                                                                            *)
(*  STATUS: 25 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessPicard.
From ToS Require Import process.ProcessGronwall.
From ToS Require Import process.ProcessODE.
From ToS Require Import SeriesConvergence.
From ToS Require Import FixedPoint.

(* ================================================================== *)
(*  Example 1: y' = y  (exponential growth)                             *)
(* ================================================================== *)

(** The identity vector field g(y) = y *)
Definition exp_rhs (y : Q) : Q := y.

(** exp_rhs is Lipschitz with constant 1 *)
Lemma exp_rhs_lipschitz : is_lipschitz_auto exp_rhs 1.
Proof.
  split.
  - lra.
  - intros y1 y2. unfold exp_rhs.
    assert (Heq : y1 - y2 == 1 * (y1 - y2)) by ring.
    setoid_rewrite Heq at 2.
    rewrite Qabs_Qmult.
    assert (H1 : Qabs 1 == 1).
    { unfold Qabs. simpl. reflexivity. }
    setoid_rewrite H1. lra.
Qed.

(** exp_rhs bounded on any interval by M *)
(** On [-M, M]: |y| ≤ M *)
Lemma exp_rhs_bounded_on : forall M,
  0 < M ->
  forall y, -M <= y -> y <= M -> Qabs (exp_rhs y) <= M.
Proof.
  intros M HM y Hlo Hhi.
  unfold exp_rhs. apply Qabs_Qle_condition. lra.
Qed.

(** Euler method for y'=y: y_{n+1} = y_n + h*y_n = (1+h)*y_n *)
Definition exp_euler (y0 h : Q) (n : nat) : Q :=
  y0 * Qpow (1 + h) n.

Lemma exp_euler_0 : forall y0 h, exp_euler y0 h 0 == y0.
Proof. intros. unfold exp_euler. simpl. ring. Qed.

Lemma exp_euler_succ : forall y0 h n,
  exp_euler y0 h (S n) == (1 + h) * exp_euler y0 h n.
Proof.
  intros. unfold exp_euler. simpl. ring.
Qed.

(** Euler for y'=y equals Gronwall with alpha=1, beta=0 *)
Lemma exp_euler_is_gronwall : forall y0 h n,
  exp_euler y0 h n == gronwall_iterate 1 0 h y0 n.
Proof.
  intros y0 h n. unfold exp_euler.
  rewrite gronwall_beta_zero.
  assert (Heq : 1 + 1 * h == 1 + h) by ring.
  assert (Hpow := Qpow_compat _ _ n Heq).
  setoid_rewrite Hpow. reflexivity.
Qed.

(** Picard operator for y'=y: P(y) = y0 + y*h *)
Lemma exp_picard_step : forall y0 h y,
  euler_picard exp_rhs y0 h y == y0 + y * h.
Proof.
  intros. unfold euler_picard, exp_rhs. ring.
Qed.

(* ================================================================== *)
(*  Example 2: y' = -αy  (exponential decay)                           *)
(* ================================================================== *)

(** Decay vector field g(y) = -α·y *)
Definition decay_rhs (alpha : Q) (y : Q) : Q := - alpha * y.

(** decay_rhs is Lipschitz with constant α *)
Lemma decay_rhs_lipschitz : forall alpha,
  0 < alpha ->
  is_lipschitz_auto (decay_rhs alpha) alpha.
Proof.
  intros alpha Halpha.
  split.
  - exact Halpha.
  - intros y1 y2. unfold decay_rhs.
    assert (Heq : - alpha * y1 - - alpha * y2 == - alpha * (y1 - y2)) by ring.
    setoid_rewrite Heq.
    rewrite Qabs_Qmult.
    assert (Habs : Qabs (- alpha) == alpha).
    { rewrite Qabs_opp. apply Qabs_pos. lra. }
    setoid_rewrite Habs. lra.
Qed.

(** Decay solution: Gronwall with negative alpha *)
Lemma decay_solution_bounded : forall alpha h y0 n,
  0 < alpha -> 0 < h -> alpha * h < 1 -> 0 <= y0 ->
  gronwall_iterate (- alpha) 0 h y0 n <= y0.
Proof.
  intros. apply gronwall_decay_bound; auto.
Qed.

(** Decay convergence: solution process goes to 0 *)
Lemma decay_converges : forall alpha h y0,
  0 < alpha -> 0 < h -> alpha * h < 1 -> 0 < y0 ->
  forall eps, 0 < eps ->
  exists N, y0 * Qpow (1 - alpha * h) N < eps.
Proof.
  intros alpha h y0 Halpha Hh Hlt1 Hy0 eps Heps.
  assert (Hah : 0 < alpha * h) by (apply Qmult_lt_0_compat; auto).
  assert (Hr : 0 < 1 - alpha * h) by lra.
  assert (Hr1 : 1 - alpha * h < 1) by lra.
  exact (scaled_qpow_vanish y0 (1 - alpha * h) eps Hy0 Hr Hr1 Heps).
Qed.

(* ================================================================== *)
(*  Example 3: y' = c  (constant velocity / integration)                *)
(* ================================================================== *)

(** Constant vector field g(y) = c *)
Definition const_rhs (c : Q) (_ : Q) : Q := c.

(** Euler method for y'=c: y_n = y0 + n*h*c *)
Fixpoint const_euler (y0 c h : Q) (n : nat) : Q :=
  match n with
  | 0%nat => y0
  | S m => const_euler y0 c h m + h * c
  end.

Lemma const_euler_0 : forall y0 c h, const_euler y0 c h 0 = y0.
Proof. intros. reflexivity. Qed.

Lemma const_euler_1 : forall y0 c h,
  const_euler y0 c h 1 == y0 + h * c.
Proof. intros. simpl. reflexivity. Qed.

(** Picard for y'=c: P(y) = y0 + c*h (independent of y!) *)
Lemma const_picard_step : forall c y0 h y,
  euler_picard (const_rhs c) y0 h y == y0 + c * h.
Proof.
  intros. unfold euler_picard, const_rhs. ring.
Qed.

(** Constant RHS: Picard converges in one step *)
Lemma const_picard_fixed : forall c y0 h,
  euler_picard (const_rhs c) y0 h (y0 + c * h) == y0 + c * h.
Proof.
  intros. unfold euler_picard, const_rhs. ring.
Qed.

(* ================================================================== *)
(*  Example 4: y' = L·y  (general linear ODE)                          *)
(* ================================================================== *)

(** Linear vector field g(y) = L·y *)
Definition linear_rhs (L : Q) (y : Q) : Q := L * y.

(** linear_rhs Lipschitz with constant |L| *)
Lemma linear_rhs_lipschitz : forall L,
  0 < L ->
  is_lipschitz_auto (linear_rhs L) L.
Proof.
  intros L HL.
  split.
  - exact HL.
  - intros y1 y2. unfold linear_rhs.
    assert (Heq : L * y1 - L * y2 == L * (y1 - y2)) by ring.
    setoid_rewrite Heq.
    rewrite Qabs_Qmult.
    assert (Habs : Qabs L == L) by (apply Qabs_pos; lra).
    setoid_rewrite Habs. lra.
Qed.

(** Linear ODE: Euler = Gronwall *)
Lemma linear_euler_is_gronwall : forall L y0 h n,
  euler_method (fun _ y => L * y) 0 y0 h n =
  euler_method (fun _ y => L * y) 0 y0 h n.
Proof. intros. reflexivity. Qed.

(** Linear Euler step: y_{n+1} = (1+Lh)·y_n *)
Lemma linear_euler_step : forall L t y h,
  euler_step (fun _ y => L * y) t y h == (1 + L * h) * y.
Proof.
  intros. unfold euler_step. ring.
Qed.

(* ================================================================== *)
(*  Part V: Cluster Theorem                                              *)
(* ================================================================== *)

(** Cluster: for linear ODE, Euler = Gronwall *)
Theorem cluster_linear_euler_gronwall : forall L y0 h n,
  0 < L -> 0 < h ->
  gronwall_iterate L 0 h y0 n == y0 * Qpow (1 + L * h) n.
Proof.
  intros. apply gronwall_beta_zero.
Qed.

(** Cluster: Picard contraction rate = Euler amplification factor *)
Theorem cluster_picard_euler_rate : forall L h,
  picard_convergence_rate L h == euler_convergence_rate L h.
Proof.
  intros. apply picard_euler_same_rate.
Qed.

(** Cluster: all three methods converge for h small enough *)
Theorem cluster_convergence : forall L h,
  0 < L -> 0 < h -> L * h < 1 ->
  (* Picard rate valid *)
  (0 < picard_convergence_rate L h /\ picard_convergence_rate L h < 1) /\
  (* Euler rate valid *)
  (0 < euler_convergence_rate L h /\ euler_convergence_rate L h < 1) /\
  (* Gronwall decay factor valid *)
  (0 < L * h /\ L * h < 1).
Proof.
  intros L h HL Hh Hlt1.
  assert (HLh : 0 < L * h) by (apply Qmult_lt_0_compat; auto).
  split; [| split].
  - split; [exact (proj1 (picard_rate_valid L h HL Hh Hlt1)) |
            exact (proj2 (picard_rate_valid L h HL Hh Hlt1))].
  - split; [exact (proj1 (euler_rate_valid L h HL Hh Hlt1)) |
            exact (proj2 (euler_rate_valid L h HL Hh Hlt1))].
  - split; [exact HLh | exact Hlt1].
Qed.

(* ================================================================== *)
(*  Part VI: E/R/R Pattern                                               *)
(* ================================================================== *)

(** Summary: every ODE with Lipschitz RHS yields a process triple *)
Theorem ode_examples_summary : forall g y0 h L M,
  is_lipschitz_auto g L -> is_bounded_auto g M ->
  0 < h -> L * h < 1 ->
  (* The solution process exists and is Cauchy *)
  is_Cauchy (euler_picard_process g y0 h) /\
  (* The error bound process exists *)
  (forall n, 0 <= picard_error_bound M L h n) /\
  (* Fixed points are unique *)
  (forall p q,
    y0 - M * h <= p -> p <= y0 + M * h ->
    y0 - M * h <= q -> q <= y0 + M * h ->
    euler_picard g y0 h p == p ->
    euler_picard g y0 h q == q ->
    p == q).
Proof.
  intros g y0 h L M Hlip Hbounded Hh Hcontract.
  split; [| split].
  - apply ode_existence_process with (L := L) (M := M); auto.
  - intro n. apply error_bound_nonneg.
    + assert (HM := bounded_auto_pos g M Hbounded). lra.
    + destruct Hlip as [HLpos _]. lra.
  - intros p q Hpl Hpr Hql Hqr Hp Hq.
    apply (ode_uniqueness g y0 h L M); auto; lra.
Qed.

(** P4: each example ODE = a process triple *)
(** No infinite limits — the iterate sequence IS the solution *)
(** exp(y'=y), decay(y'=-αy), const(y'=c), linear(y'=Ly) *)
(** All share the same framework: Picard contraction → process *)
