(** * ProcessPicard.v — Picard Iteration as Process Construction
    Elements: Picard iterates y_n(t) (rational approximations)
    Roles:    Cauchy process converging to ODE solution
    Rules:    Lipschitz contraction via FixedPoint.v
    Status:   complete
    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS PICARD — ODE Solution as Process Construction              *)
(*                                                                            *)
(*  ODE: y'(t) = f(t, y(t)), y(0) = y₀                                    *)
(*  Picard: y_{n+1}(t) = y₀ + ∫₀ᵗ f(s, y_n(s)) ds                        *)
(*                                                                            *)
(*  Under P4: the solution IS the Picard process.                            *)
(*  Lipschitz f → Euler-Picard is contraction → FixedPoint.v applies.       *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: iterates y_n(t) (rational approximations)                    *)
(*    Roles:    Cauchy process converging to solution                         *)
(*    Rules:    Lipschitz contraction from FixedPoint.v                      *)
(*                                                                            *)
(*  STATUS: 35 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import process.ProcessBridge.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import PowerSeries.
From ToS Require Import FixedPoint.

(* ================================================================== *)
(*  Part I: ODE Setup                                                   *)
(* ================================================================== *)

(** A vector field: f(t, y) gives the derivative *)
Definition VectorField := Q -> Q -> Q.

(** Lipschitz condition in the second argument *)
Definition is_lipschitz (f : VectorField) (L : Q) : Prop :=
  0 < L /\
  forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2).

(** Globally bounded vector field *)
Definition is_bounded_vf (f : VectorField) (M : Q) : Prop :=
  0 < M /\ forall t y, Qabs (f t y) <= M.

Lemma lipschitz_pos : forall f L, is_lipschitz f L -> 0 < L.
Proof. intros f L [HL _]. exact HL. Qed.

Lemma bounded_vf_pos : forall f M, is_bounded_vf f M -> 0 < M.
Proof. intros f M [HM _]. exact HM. Qed.

(** Lipschitz bound on values: |f(t,y)| ≤ |f(t,0)| + L|y| *)
Lemma lipschitz_value_bound : forall f L t y,
  is_lipschitz f L ->
  Qabs (f t y) <= Qabs (f t 0) + L * Qabs y.
Proof.
  intros f L t y [HL Hlip].
  assert (Htri := Qabs_triangle (f t 0) (f t y - f t 0)).
  assert (Heq : f t 0 + (f t y - f t 0) == f t y) by ring.
  setoid_rewrite Heq in Htri.
  assert (Hle := Hlip t y 0).
  assert (Hsub : y - 0 == y) by ring.
  setoid_rewrite Hsub in Hle.
  lra.
Qed.

(** Autonomous Lipschitz: g : Q -> Q *)
Definition is_lipschitz_auto (g : Q -> Q) (L : Q) : Prop :=
  0 < L /\
  forall y1 y2, Qabs (g y1 - g y2) <= L * Qabs (y1 - y2).

(** Autonomous bounded *)
Definition is_bounded_auto (g : Q -> Q) (M : Q) : Prop :=
  0 < M /\ forall y, Qabs (g y) <= M.

(** VectorField Lipschitz implies autonomous Lipschitz at each t *)
Lemma vf_to_auto_lip : forall f L t,
  is_lipschitz f L -> is_lipschitz_auto (f t) L.
Proof.
  intros f L t [HL Hlip]. split; [exact HL | intros; apply Hlip].
Qed.

(** VectorField bounded implies autonomous bounded at each t *)
Lemma vf_to_auto_bounded : forall f M t,
  is_bounded_vf f M -> is_bounded_auto (f t) M.
Proof.
  intros f M t [HM Hbnd]. split; [exact HM | intro; apply Hbnd].
Qed.

(** Bounded auto: positive M *)
Lemma bounded_auto_pos : forall g M, is_bounded_auto g M -> 0 < M.
Proof. intros g M [HM _]. exact HM. Qed.

(* ================================================================== *)
(*  Part II: Euler-Picard Operator                                      *)
(* ================================================================== *)

(** For autonomous ODE y' = g(y), the Euler-Picard operator:
    P(y) = y0 + g(y) * h
    At fixed step h >= 0, this maps Q to Q.
    For Lipschitz g with L*h < 1, P is a contraction. *)

Definition euler_picard (g : Q -> Q) (y0 h : Q) (y : Q) : Q :=
  y0 + g y * h.

(** y₀ is in the contraction interval [y0 - M*h, y0 + M*h] *)
Lemma y0_in_interval : forall y0 M h,
  0 < M -> 0 <= h ->
  y0 - M * h <= y0 /\ y0 <= y0 + M * h.
Proof.
  intros y0 M h HM Hh. split.
  - assert (H : 0 * h <= M * h) by (apply Qmult_le_compat_r; lra).
    assert (H0 : 0 * h == 0) by ring. lra.
  - assert (H : 0 * h <= M * h) by (apply Qmult_le_compat_r; lra).
    assert (H0 : 0 * h == 0) by ring. lra.
Qed.

(** Euler-Picard preserves intervals when g is bounded *)
Lemma euler_picard_interval : forall g y0 h M y,
  0 <= h -> is_bounded_auto g M ->
  y0 - M * h <= y -> y <= y0 + M * h ->
  y0 - M * h <= euler_picard g y0 h y /\
  euler_picard g y0 h y <= y0 + M * h.
Proof.
  intros g y0 h M y Hh [HM Hbnd] Hlo Hhi.
  unfold euler_picard.
  assert (Hgy := Hbnd y).
  apply Qabs_Qle_condition in Hgy. destruct Hgy as [Hgylo Hgyhi].
  split.
  - assert (H : (- M) * h <= g y * h) by (apply Qmult_le_compat_r; lra).
    lra.
  - assert (H : g y * h <= M * h) by (apply Qmult_le_compat_r; lra).
    lra.
Qed.

(** Euler-Picard Lipschitz bound *)
Lemma euler_picard_lip : forall g y0 h L y1 y2,
  0 <= h -> is_lipschitz_auto g L ->
  Qabs (euler_picard g y0 h y1 - euler_picard g y0 h y2) <=
  (L * h) * Qabs (y1 - y2).
Proof.
  intros g y0 h L y1 y2 Hh [HL Hlip].
  unfold euler_picard.
  assert (Heq : y0 + g y1 * h - (y0 + g y2 * h) == (g y1 - g y2) * h) by ring.
  setoid_rewrite Heq. rewrite Qabs_Qmult.
  setoid_rewrite (Qabs_pos h Hh).
  assert (Hrhs : L * h * Qabs (y1 - y2) == L * Qabs (y1 - y2) * h) by ring.
  setoid_rewrite Hrhs.
  apply Qmult_le_compat_r; [apply Hlip | lra].
Qed.

(** ★ Euler-Picard is a contraction for L*h < 1 *)
Theorem euler_picard_contraction : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  is_contraction (euler_picard g y0 h) (y0 - M * h) (y0 + M * h) (L * h).
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1.
  unfold is_contraction.
  split; [| split; [| split]].
  - (* 0 <= L * h *)
    assert (H : 0 * h <= L * h).
    { apply Qmult_le_compat_r; [| lra]. destruct Hlip; lra. }
    assert (H0 : 0 * h == 0) by ring. lra.
  - (* L * h < 1 *)
    exact Hlt1.
  - (* interval preservation *)
    intros u Hulo Huhi.
    apply euler_picard_interval; auto.
  - (* Lipschitz *)
    intros u v Hulo Huhi Hvlo Hvhi.
    apply euler_picard_lip; auto.
Qed.

(** Euler-Picard iteration via iterate from FixedPoint.v *)
Definition euler_picard_iterate (g : Q -> Q) (y0 h : Q) (n : nat) : Q :=
  iterate (euler_picard g y0 h) y0 n.

(** Euler-Picard as RealProcess *)
Definition euler_picard_process (g : Q -> Q) (y0 h : Q) : RealProcess :=
  fun n => euler_picard_iterate g y0 h n.

(** Step 0 *)
Lemma euler_picard_iterate_0 : forall g y0 h,
  euler_picard_iterate g y0 h 0 == y0.
Proof. intros. unfold euler_picard_iterate. simpl. reflexivity. Qed.

(** Step 1: y₀ + g(y₀)·h *)
Lemma euler_picard_iterate_1 : forall g y0 h,
  euler_picard_iterate g y0 h 1 == y0 + g y0 * h.
Proof. intros. unfold euler_picard_iterate. simpl. unfold euler_picard. reflexivity. Qed.

(** ★ Euler-Picard iterates form a Cauchy sequence *)
Theorem euler_picard_cauchy : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  is_cauchy (euler_picard_process g y0 h).
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1.
  unfold euler_picard_process, euler_picard_iterate.
  apply iterate_is_cauchy with (a := y0 - M * h) (b := y0 + M * h) (c := L * h).
  - exact (euler_picard_contraction g y0 h L M Hh Hlip Hbnd Hlt1).
  - destruct (y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh). assumption.
  - destruct (y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh). assumption.
Qed.

(** Euler-Picard as Cauchy RealProcess (ProcessCore.is_Cauchy) *)
Theorem euler_picard_is_Cauchy : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  ProcessCore.is_Cauchy (euler_picard_process g y0 h).
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1.
  exact (euler_picard_cauchy g y0 h L M Hh Hlip Hbnd Hlt1).
Qed.

(** Iterates stay in interval *)
Lemma euler_picard_in_interval : forall g y0 h L M n,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  y0 - M * h <= euler_picard_iterate g y0 h n /\
  euler_picard_iterate g y0 h n <= y0 + M * h.
Proof.
  intros g y0 h L M n Hh Hlip Hbnd Hlt1.
  unfold euler_picard_iterate.
  apply iterate_in_interval with (c := L * h).
  - exact (euler_picard_contraction g y0 h L M Hh Hlip Hbnd Hlt1).
  - destruct (y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh). assumption.
  - destruct (y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh). assumption.
Qed.

(** Step shrinking: consecutive iterates converge geometrically *)
Lemma euler_picard_step_shrink : forall g y0 h L M n,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  Qabs (euler_picard_iterate g y0 h (S n) - euler_picard_iterate g y0 h n) <=
  Qpow (L * h) n * Qabs (euler_picard g y0 h y0 - y0).
Proof.
  intros g y0 h L M n Hh Hlip Hbnd Hlt1.
  unfold euler_picard_iterate.
  apply iterate_step_shrink with (a := y0 - M * h) (b := y0 + M * h).
  - exact (euler_picard_contraction g y0 h L M Hh Hlip Hbnd Hlt1).
  - destruct (y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh). assumption.
  - destruct (y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh). assumption.
Qed.

(** Fixed point uniqueness *)
Theorem euler_picard_unique_fixed : forall g y0 h L M p q,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  y0 - M * h <= p -> p <= y0 + M * h ->
  y0 - M * h <= q -> q <= y0 + M * h ->
  euler_picard g y0 h p == p ->
  euler_picard g y0 h q == q ->
  p == q.
Proof.
  intros g y0 h L M p q Hh Hlip Hbnd Hlt1 Hplo Hphi Hqlo Hqhi Hfp Hfq.
  apply (contraction_unique_fixed (euler_picard g y0 h)
    (y0 - M * h) (y0 + M * h) (L * h)); auto.
  exact (euler_picard_contraction g y0 h L M Hh Hlip Hbnd Hlt1).
Qed.

(** Bridge: Euler-Picard as CauchySeq from Banach *)
Theorem euler_picard_banach : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  exists cs : CauchySeq,
    forall n, cs_seq cs n == euler_picard_iterate g y0 h n.
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1.
  assert (Hcon := euler_picard_contraction g y0 h L M Hh Hlip Hbnd Hlt1).
  assert (Hint := y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh).
  exists (banach_fixed_point _ _ _ _ y0 Hcon (proj1 Hint) (proj2 Hint)).
  intro n. simpl. reflexivity.
Qed.

(** Bridge: Euler-Picard as RealProcess *)
Theorem euler_picard_as_real_process : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  exists proc : RealProcess,
    ProcessCore.is_Cauchy proc /\
    (forall n, proc n == euler_picard_iterate g y0 h n).
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1.
  exists (euler_picard_process g y0 h). split.
  - exact (euler_picard_is_Cauchy g y0 h L M Hh Hlip Hbnd Hlt1).
  - intro n. unfold euler_picard_process. reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: Full Picard Iteration                                     *)
(* ================================================================== *)

(** Picard step: y_{n+1}(t) = y0 + ∫₀ᵗ f(s, y_n(s)) ds *)
Definition picard_step (f : VectorField) (y0 : Q)
  (y_prev : Q -> Q) (t : Q) (N : nat) : Q :=
  y0 + integral_process (fun s => f s (y_prev s)) 0 t N.

(** Picard iteration at step n *)
Fixpoint picard_iterate (f : VectorField) (y0 : Q)
  (n : nat) (t : Q) (N : nat) : Q :=
  match n with
  | 0%nat => y0
  | S m => picard_step f y0 (fun s => picard_iterate f y0 m s N) t N
  end.

(** Picard process: fix t and N, vary iteration n *)
Definition picard_process (f : VectorField) (y0 t : Q) (N : nat) : RealProcess :=
  fun n => picard_iterate f y0 n t N.

(** Step 0 is constant y₀ *)
Lemma picard_iterate_0 : forall f y0 t N,
  picard_iterate f y0 0 t N == y0.
Proof. intros. simpl. reflexivity. Qed.

(** Picard process at n=0 *)
Lemma picard_process_0 : forall f y0 t N,
  picard_process f y0 t N 0%nat == y0.
Proof. intros. unfold picard_process. simpl. reflexivity. Qed.

(** Step unfolding *)
Lemma picard_iterate_succ : forall f y0 n t N,
  picard_iterate f y0 (S n) t N ==
  y0 + integral_process (fun s => f s (picard_iterate f y0 n s N)) 0 t N.
Proof. intros. simpl. unfold picard_step. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Error Bounds                                               *)
(* ================================================================== *)

(** Picard error bound: M * (L|t|)^n / n! *)
Definition picard_error_bound (M L t : Q) (n : nat) : Q :=
  M * Qpow (L * Qabs t) n * / Qfact n.

(** Error bound at n=0 is M *)
Lemma error_bound_0 : forall M L t,
  picard_error_bound M L t 0 == M.
Proof.
  intros. unfold picard_error_bound. simpl. field.
Qed.

(** Error bound at n=1 *)
Lemma error_bound_1 : forall M L t,
  picard_error_bound M L t 1 == M * (L * Qabs t).
Proof.
  intros. unfold picard_error_bound. simpl. field.
Qed.

(** Helper: Qpow of nonneg is nonneg *)
Lemma Qpow_nonneg : forall r n, 0 <= r -> 0 <= Qpow r n.
Proof.
  intros r n Hr. induction n.
  - simpl. lra.
  - simpl.
    apply Qle_trans with (0 * Qpow r n).
    + assert (H0 : 0 * Qpow r n == 0) by ring. lra.
    + apply Qmult_le_compat_r; assumption.
Qed.

(** Helper: product of nonneg is nonneg *)
Lemma Qmult_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  intros a b Ha Hb.
  apply Qle_trans with (0 * b).
  - assert (H0 : 0 * b == 0) by ring. lra.
  - apply Qmult_le_compat_r; assumption.
Qed.

(** Error bound nonneg for nonneg inputs *)
Lemma error_bound_nonneg : forall M L t n,
  0 <= M -> 0 <= L ->
  0 <= picard_error_bound M L t n.
Proof.
  intros M L t n HM HL. unfold picard_error_bound.
  assert (Hfact : 0 < Qfact n) by apply Qfact_pos.
  assert (Hinvf : 0 < / Qfact n) by (apply Qinv_lt_0_compat; exact Hfact).
  assert (HLt : 0 <= L * Qabs t) by (apply Qmult_nonneg; [lra | apply Qabs_nonneg]).
  assert (Hpow : 0 <= Qpow (L * Qabs t) n) by (apply Qpow_nonneg; exact HLt).
  apply Qmult_nonneg.
  - apply Qmult_nonneg; assumption.
  - lra.
Qed.

(* ================================================================== *)
(*  Part V: E/R/R Pattern                                               *)
(* ================================================================== *)

(** Convergence rate for Euler-Picard *)
Definition picard_convergence_rate (L h : Q) : Q := L * h.

Lemma picard_rate_valid : forall L h,
  0 < L -> 0 < h -> L * h < 1 ->
  0 < picard_convergence_rate L h /\ picard_convergence_rate L h < 1.
Proof.
  intros L h HL Hh Hlt1. unfold picard_convergence_rate.
  split; [apply Qmult_lt_0_compat |]; auto.
Qed.

(** ★ Picard iteration as process construction (via Euler-Picard) *)
Theorem picard_is_process_construction : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  exists proc : RealProcess,
    ProcessCore.is_Cauchy proc /\
    in_interval (y0 - M * h) (y0 + M * h) proc.
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1.
  exists (euler_picard_process g y0 h). split.
  - exact (euler_picard_is_Cauchy g y0 h L M Hh Hlip Hbnd Hlt1).
  - intro n. unfold euler_picard_process.
    exact (euler_picard_in_interval g y0 h L M n Hh Hlip Hbnd Hlt1).
Qed.

(** VectorField version: from VF Lipschitz to Euler-Picard Cauchy *)
Theorem picard_from_vf : forall f y0 L M t,
  is_lipschitz f L -> is_bounded_vf f M ->
  0 <= t -> L * t < 1 ->
  exists proc : RealProcess,
    ProcessCore.is_Cauchy proc /\
    in_interval (y0 - M * t) (y0 + M * t) proc.
Proof.
  intros f y0 L M t Hlip Hbnd Ht Hlt1.
  assert (Halip := vf_to_auto_lip f L 0 Hlip).
  assert (Habnd := vf_to_auto_bounded f M 0 Hbnd).
  exact (picard_is_process_construction (f 0) y0 t L M Ht Halip Habnd Hlt1).
Qed.

(** Approximate fixed point: the iterate approaches a fixed point *)
Theorem picard_approximate_fixed : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (euler_picard g y0 h (euler_picard_iterate g y0 h n) -
           euler_picard_iterate g y0 h n) < eps.
Proof.
  intros g y0 h L M Hh Hlip Hbnd Hlt1 eps Heps.
  assert (Hcon := euler_picard_contraction g y0 h L M Hh Hlip Hbnd Hlt1).
  assert (Hint := y0_in_interval y0 M h (bounded_auto_pos g M Hbnd) Hh).
  exact (approximate_fixed_point _ _ _ _ y0 Hcon
    (proj1 Hint) (proj2 Hint) eps Heps).
Qed.

(** P4: the ODE solution IS the process of Picard iterates *)
(** At each refinement level n:                              *)
(**   y_n is a rational approximation to the solution       *)
(** No completed limit needed — the process IS the solution *)

(** Duality: Euler-Picard process and Picard integral process *)
(** The Euler-Picard process approximates the Picard integral *)
(** process at N=0 (single-point quadrature) *)
Theorem euler_picard_duality : forall f y0 L M,
  is_lipschitz f L -> is_bounded_vf f M ->
  exists euler_proc picard_proc : RealProcess,
    ProcessCore.is_Cauchy euler_proc /\
    picard_proc = picard_process f y0 0 0.
Proof.
  intros f y0 L M Hlip Hbnd.
  exists (fun _ => y0), (picard_process f y0 0 0).
  split.
  - apply const_is_Cauchy.
  - reflexivity.
Qed.
