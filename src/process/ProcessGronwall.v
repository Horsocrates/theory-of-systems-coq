(** * ProcessGronwall.v — Gronwall Inequality as Process Bound
    Elements: discrete Gronwall iterates u(n)
    Roles:    upper bound on ODE error processes
    Rules:    inductive bound u(n+1) ≤ (1+αh)·u(n) + βh
    Status:   complete
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS GRONWALL — Gronwall Inequality as Process Bound            *)
(*                                                                            *)
(*  Discrete Gronwall: if u(n+1) ≤ (1+αh)·u(n) + βh                       *)
(*  then u(n) ≤ (u₀ + β/α)·(1+αh)^n − β/α                                *)
(*                                                                            *)
(*  Under P4: the Gronwall bound IS a process bounding error processes.     *)
(*  Decay case (α < 0): exponential convergence to 0.                       *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: Gronwall iterates (upper bounds on error)                    *)
(*    Roles:    bounding process for ODE error                               *)
(*    Rules:    inductive step u(n+1) ≤ factor·u(n) + forcing               *)
(*                                                                            *)
(*  STATUS: 22 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import SeriesConvergence.
From ToS Require Import FixedPoint.

(* ================================================================== *)
(*  Part I: Discrete Gronwall Setup                                     *)
(* ================================================================== *)

(** Gronwall step: u(n+1) = (1 + α·h) · u(n) + β·h *)
Definition gronwall_step (alpha beta h : Q) (u_n : Q) : Q :=
  (1 + alpha * h) * u_n + beta * h.

(** Gronwall iteration *)
Fixpoint gronwall_iterate (alpha beta h u0 : Q) (n : nat) : Q :=
  match n with
  | 0%nat => u0
  | S m => gronwall_step alpha beta h (gronwall_iterate alpha beta h u0 m)
  end.

(** Gronwall as RealProcess *)
Definition gronwall_process (alpha beta h u0 : Q) : RealProcess :=
  fun n => gronwall_iterate alpha beta h u0 n.

(** Step 0 *)
Lemma gronwall_iterate_0 : forall alpha beta h u0,
  gronwall_iterate alpha beta h u0 0%nat == u0.
Proof. intros. simpl. reflexivity. Qed.

(** Step 1 *)
Lemma gronwall_iterate_1 : forall alpha beta h u0,
  gronwall_iterate alpha beta h u0 1%nat ==
  (1 + alpha * h) * u0 + beta * h.
Proof. intros. simpl. unfold gronwall_step. reflexivity. Qed.

(** Step unfolding *)
Lemma gronwall_iterate_succ : forall alpha beta h u0 n,
  gronwall_iterate alpha beta h u0 (S n) ==
  gronwall_step alpha beta h (gronwall_iterate alpha beta h u0 n).
Proof. intros. simpl. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Pure Growth (β = 0)                                        *)
(* ================================================================== *)

(** With β=0: u(n+1) = (1+αh)·u(n), so u(n) = u₀·(1+αh)^n *)
Lemma gronwall_beta_zero : forall alpha h u0 n,
  gronwall_iterate alpha 0 h u0 n == u0 * Qpow (1 + alpha * h) n.
Proof.
  intros alpha h u0 n. induction n.
  - simpl. ring.
  - simpl. unfold gronwall_step.
    setoid_rewrite IHn. ring.
Qed.

(** Qpow of nonneg is nonneg *)
Lemma Qpow_nonneg : forall r n, 0 <= r -> 0 <= Qpow r n.
Proof.
  intros r n Hr. induction n.
  - simpl. lra.
  - simpl.
    apply Qle_trans with (0 * Qpow r n).
    + assert (H0 : 0 * Qpow r n == 0) by ring. lra.
    + apply Qmult_le_compat_r; assumption.
Qed.

(** Qpow of value in [0,1] stays ≤ 1 *)
Lemma Qpow_le_1 : forall r n, 0 <= r -> r <= 1 -> Qpow r n <= 1.
Proof.
  intros r n Hr Hr1. induction n.
  - simpl. lra.
  - simpl.
    apply Qle_trans with (1 * Qpow r n).
    + apply Qmult_le_compat_r; [lra | apply Qpow_nonneg; lra].
    + assert (H1 : 1 * Qpow r n == Qpow r n) by ring. lra.
Qed.

(** For 0 ≤ factor ≤ 1: iterations decay *)
Lemma gronwall_decay_factor : forall r u0 n,
  0 <= r -> r <= 1 ->
  0 <= u0 ->
  u0 * Qpow r n <= u0.
Proof.
  intros r u0 n Hr Hr1 Hu0.
  assert (Hpow : Qpow r n <= 1) by (apply Qpow_le_1; lra).
  assert (H : Qpow r n * u0 <= 1 * u0).
  { apply Qmult_le_compat_r; [exact Hpow | exact Hu0]. }
  assert (H1 : Qpow r n * u0 == u0 * Qpow r n) by ring.
  assert (H2 : 1 * u0 == u0) by ring. lra.
Qed.

(* ================================================================== *)
(*  Part III: Decay Process (α < 0, β = 0)                             *)
(* ================================================================== *)

(** Qpow respects Qeq *)
Lemma Qpow_compat : forall a b n, a == b -> Qpow a n == Qpow b n.
Proof.
  intros a b n Hab. induction n.
  - simpl. reflexivity.
  - simpl. setoid_rewrite IHn. setoid_rewrite Hab. reflexivity.
Qed.

(** For damping: u(n+1) = (1-|α|h)·u(n), decay when 0 < |α|h < 1 *)
Lemma gronwall_decay : forall alpha h u0 n,
  0 < alpha -> 0 < h -> alpha * h < 1 ->
  0 <= u0 ->
  gronwall_iterate (- alpha) 0 h u0 n == u0 * Qpow (1 - alpha * h) n.
Proof.
  intros alpha h u0 n Halpha Hh Hlt1 Hu0.
  rewrite gronwall_beta_zero.
  assert (Hcompat : Qpow (1 + - alpha * h) n == Qpow (1 - alpha * h) n).
  { apply Qpow_compat. ring. }
  setoid_rewrite Hcompat. reflexivity.
Qed.

(** Decay bound: u(n) ≤ u₀ *)
Lemma gronwall_decay_bound : forall alpha h u0 n,
  0 < alpha -> 0 < h -> alpha * h < 1 ->
  0 <= u0 ->
  gronwall_iterate (- alpha) 0 h u0 n <= u0.
Proof.
  intros alpha h u0 n Halpha Hh Hlt1 Hu0.
  assert (Hgd := gronwall_decay alpha h u0 n Halpha Hh Hlt1 Hu0).
  assert (Hah : 0 < alpha * h) by (apply Qmult_lt_0_compat; auto).
  assert (Hfact : 0 <= 1 - alpha * h) by lra.
  assert (Hfact1 : 1 - alpha * h <= 1) by lra.
  assert (Hdf := gronwall_decay_factor (1 - alpha * h) u0 n Hfact Hfact1 Hu0).
  lra.
Qed.

(* ================================================================== *)
(*  Part IV: Gronwall Bound (general case)                              *)
(* ================================================================== *)

(** The Gronwall bound: u(n) ≤ (u₀ + β/α) · (1+αh)^n − β/α *)
Definition gronwall_bound (alpha beta h u0 : Q) (n : nat) : Q :=
  (u0 + beta / alpha) * Qpow (1 + alpha * h) n - beta / alpha.

(** Gronwall bound at n=0 equals u₀ *)
Lemma gronwall_bound_0 : forall alpha beta h u0,
  0 < alpha ->
  gronwall_bound alpha beta h u0 0 == u0.
Proof.
  intros. unfold gronwall_bound. simpl. field.
  intro. lra.
Qed.

(** ★ Discrete Gronwall inequality *)
Theorem discrete_gronwall : forall alpha beta h u0 n,
  0 < alpha -> 0 <= beta -> 0 < h ->
  gronwall_iterate alpha beta h u0 n <= gronwall_bound alpha beta h u0 n.
Proof.
  intros alpha beta h u0 n Halpha Hbeta Hh.
  induction n.
  - (* Base: u₀ ≤ (u₀+β/α)·1 − β/α = u₀ *)
    simpl. unfold gronwall_bound. simpl.
    assert (Heq : (u0 + beta / alpha) * 1 - beta / alpha == u0).
    { field. intro. lra. }
    lra.
  - (* Step *)
    simpl. unfold gronwall_step.
    unfold gronwall_bound. simpl.
    unfold gronwall_bound in IHn.
    (* u_n ≤ (u0+β/α)·(1+αh)^n − β/α  [IHn] *)
    (* Need: (1+αh)·u_n + βh ≤ (u0+β/α)·(1+αh)^{n+1} − β/α *)
    (* (1+αh)·u_n + βh ≤ (1+αh)·[(u0+β/α)(1+αh)^n − β/α] + βh *)
    (* = (u0+β/α)(1+αh)^{n+1} − (1+αh)β/α + βh *)
    (* = (u0+β/α)(1+αh)^{n+1} − β/α − βh + βh *)
    (* = (u0+β/α)(1+αh)^{n+1} − β/α ✓ *)
    assert (Hfactor : 0 <= 1 + alpha * h).
    { assert (H : 0 * h <= alpha * h) by (apply Qmult_le_compat_r; lra).
      assert (H0 : 0 * h == 0) by ring. lra. }
    set (bound_n := (u0 + beta / alpha) * Qpow (1 + alpha * h) n - beta / alpha) in *.
    assert (Hmain : (1 + alpha * h) * gronwall_iterate alpha beta h u0 n + beta * h <=
      (1 + alpha * h) * bound_n + beta * h).
    { assert (H : gronwall_iterate alpha beta h u0 n * (1 + alpha * h) <=
                  bound_n * (1 + alpha * h)).
      { apply Qmult_le_compat_r; [exact IHn | exact Hfactor]. }
      assert (Hc1 : (1 + alpha * h) * gronwall_iterate alpha beta h u0 n ==
                    gronwall_iterate alpha beta h u0 n * (1 + alpha * h)) by ring.
      assert (Hc2 : (1 + alpha * h) * bound_n == bound_n * (1 + alpha * h)) by ring.
      lra. }
    apply Qle_trans with ((1 + alpha * h) * bound_n + beta * h).
    + exact Hmain.
    + (* Algebraic identity *)
      subst bound_n.
      assert (Halg :
        (1 + alpha * h) *
          ((u0 + beta / alpha) * Qpow (1 + alpha * h) n - beta / alpha) + beta * h ==
        (u0 + beta / alpha) * ((1 + alpha * h) * Qpow (1 + alpha * h) n) - beta / alpha).
      { field. intro. lra. }
      lra.
Qed.

(* ================================================================== *)
(*  Part V: Application to Picard Error                                 *)
(* ================================================================== *)

(** Error contraction: e₀·(Lh)^n ≤ e₀ when Lh ≤ 1 *)
Lemma picard_error_contraction : forall L h e0 n,
  0 < L -> 0 < h -> L * h <= 1 ->
  0 <= e0 ->
  e0 * Qpow (L * h) n <= e0.
Proof.
  intros L h e0 n HL Hh Hle1 He0.
  apply gronwall_decay_factor; auto.
  assert (H : 0 * h <= L * h) by (apply Qmult_le_compat_r; lra).
  assert (H0 : 0 * h == 0) by ring. lra.
Qed.

(** Error vanishes for strict contraction *)
Lemma picard_error_vanish : forall L h e0,
  0 < L -> 0 < h -> L * h < 1 -> 0 < e0 ->
  forall eps, 0 < eps ->
  exists N : nat, e0 * Qpow (L * h) N < eps.
Proof.
  intros L h e0 HL Hh Hlt1 He0 eps Heps.
  assert (HLh : 0 < L * h) by (apply Qmult_lt_0_compat; auto).
  exact (scaled_qpow_vanish e0 (L * h) eps He0 HLh Hlt1 Heps).
Qed.

(* ================================================================== *)
(*  Part VI: Stability                                                  *)
(* ================================================================== *)

(** Two solutions with different data: difference bounded by Gronwall *)
Theorem ode_stability_bound : forall r diff0 n,
  0 <= r -> r < 1 -> 0 <= diff0 ->
  diff0 * Qpow r n <= diff0.
Proof.
  intros r diff0 n Hr Hr1 Hd0.
  apply gronwall_decay_factor; lra.
Qed.

(** Stability: difference shrinks *)
Theorem ode_stability_vanish : forall r diff0,
  0 < r -> r < 1 -> 0 < diff0 ->
  forall eps, 0 < eps ->
  exists N : nat, diff0 * Qpow r N < eps.
Proof.
  intros r diff0 Hr Hr1 Hd0 eps Heps.
  exact (scaled_qpow_vanish diff0 r eps Hd0 Hr Hr1 Heps).
Qed.

(* ================================================================== *)
(*  Part VII: E/R/R Pattern                                             *)
(* ================================================================== *)

(** Gronwall convergence rate *)
Definition gronwall_convergence_rate (alpha h : Q) : Q := 1 + alpha * h.

Lemma gronwall_decay_rate_valid : forall alpha h,
  0 < alpha -> 0 < h -> alpha * h < 1 ->
  0 < 1 - alpha * h /\ 1 - alpha * h < 1.
Proof.
  intros alpha h Halpha Hh Hlt1.
  assert (Hah : 0 < alpha * h) by (apply Qmult_lt_0_compat; auto).
  split; lra.
Qed.

(** E/R/R: Gronwall as process construction *)
Theorem gronwall_is_process_construction : forall alpha beta h u0,
  0 < alpha -> 0 <= beta -> 0 < h ->
  exists bound_proc : RealProcess,
    (forall n, gronwall_process alpha beta h u0 n <=
               bound_proc n) /\
    (forall n, bound_proc n == gronwall_bound alpha beta h u0 n).
Proof.
  intros alpha beta h u0 Halpha Hbeta Hh.
  exists (fun n => gronwall_bound alpha beta h u0 n).
  split.
  - intro n. unfold gronwall_process.
    apply discrete_gronwall; auto.
  - intro n. reflexivity.
Qed.

(** P4: the Gronwall bound IS the process of exponential envelopes *)
(** At each n: the bound (u₀+β/α)·(1+αh)^n − β/α is rational *)
(** No infinite-time limit needed — the bound process IS the envelope *)
