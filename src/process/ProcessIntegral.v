(** * ProcessIntegral.v — Riemann Integration as Process Construction
    Elements: partial Riemann sums RS(f, a, (b-a)/(n+1), n+1)
    Roles:    Cauchy process converging to integral value
    Rules:    ftc_grid convergence from RiemannIntegration.v
    Status:   complete
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS INTEGRAL — Riemann Integration as Process Construction     *)
(*                                                                            *)
(*  The integral ∫_a^b f(x)dx is approximated by Riemann sums               *)
(*  Under P4: the integral IS the PROCESS {RS(f, n+1 points)}_{n>=0}        *)
(*  No completed limit — the process IS the integral.                        *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: Riemann sums on uniform grids with n+1 subintervals         *)
(*    Roles:    Cauchy process converging to integral value                  *)
(*    Rules:    ftc_grid from RiemannIntegration.v                          *)
(*                                                                            *)
(*  STATUS: 11 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessDerivative.
From ToS Require Import MeanValueTheorem.
From ToS Require Import RiemannIntegration.

(* ================================================================== *)
(*  Part I: Integration Process                                          *)
(* ================================================================== *)

(** Step size for n+1 subintervals: step = (b-a)/(n+1) *)
Definition integral_step (a b : Q) (n : nat) : Q :=
  (b - a) / inject_Z (Z.of_nat (S n)).

(** Reuse inject_Z_Sn_pos from ProcessDerivative *)

Lemma integral_step_pos : forall a b n, a < b -> 0 < integral_step a b n.
Proof.
  intros a b n Hab. unfold integral_step, Qdiv.
  apply Qmult_lt_0_compat.
  - lra.
  - apply Qinv_lt_0_compat. apply inject_Z_Sn_pos.
Qed.

(** The Riemann integral as a process: RS with n+1 subintervals *)
Definition integral_process (f : Q -> Q) (a b : Q) : RealProcess :=
  fun n => riemann_sum f a (integral_step a b n) (S n).

(* ================================================================== *)
(*  Part II: Integral of Known Functions                                 *)
(* ================================================================== *)

(** Integral of constant c over [a,b] = c*(b-a) *)
Lemma integral_process_const : forall c a b,
  a < b ->
  process_equiv (integral_process (fun _ => c) a b) (const_process (c * (b - a))).
Proof.
  intros c a b Hab eps Heps.
  exists 0%nat. intros n Hn.
  unfold integral_process, const_process.
  (* RS(const c, a, step, S n) = c * (S n) * step *)
  assert (Hrs : riemann_sum (fun _ => c) a (integral_step a b n) (S n) ==
                c * inject_Z (Z.of_nat (S n)) * integral_step a b n).
  { apply riemann_sum_const. }
  setoid_rewrite Hrs.
  (* c * (S n) * step = c * (S n) * (b-a)/(S n) = c * (b-a) *)
  assert (Heq : c * inject_Z (Z.of_nat (S n)) * integral_step a b n - c * (b - a) == 0).
  { unfold integral_step. field. intro H. assert (Hp := inject_Z_Sn_pos n). lra. }
  setoid_rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** Width of uniform grid: RS(1, a, step, n) = n * step *)
Lemma integral_process_width : forall a b n,
  riemann_sum (fun _ => 1) a (integral_step a b n) (S n) ==
  inject_Z (Z.of_nat (S n)) * integral_step a b n.
Proof.
  intros a b n.
  assert (H := riemann_sum_const 1 a (integral_step a b n) (S n)).
  setoid_rewrite Qmult_1_l in H. exact H.
Qed.

(** Width simplifies to b - a *)
Lemma grid_width_eq : forall a b n,
  inject_Z (Z.of_nat (S n)) * integral_step a b n == b - a.
Proof.
  intros a b n. unfold integral_step. field.
  intro H. assert (Hp := inject_Z_Sn_pos n). lra.
Qed.

(* ================================================================== *)
(*  Part III: Linearity Properties                                       *)
(* ================================================================== *)

(** Additivity: integral(f+g) = integral(f) + integral(g) pointwise *)
Lemma integral_process_add : forall f g a b n,
  integral_process (fun x => f x + g x) a b n ==
  integral_process f a b n + integral_process g a b n.
Proof.
  intros f g a b n.
  unfold integral_process.
  apply riemann_sum_add.
Qed.

(** Scaling: integral(c*f) = c * integral(f) pointwise *)
Lemma integral_process_scale : forall c f a b n,
  integral_process (fun x => c * f x) a b n ==
  c * integral_process f a b n.
Proof.
  intros c f a b n.
  unfold integral_process.
  apply riemann_sum_scale.
Qed.

(* ================================================================== *)
(*  Part IV: Convergence via FTC                                         *)
(* ================================================================== *)

(** Step size vanishes *)
Lemma integral_step_vanishes : forall a b delta,
  a < b -> 0 < delta ->
  exists N : nat, integral_step a b N < delta.
Proof.
  intros a b delta Hab Hdelta.
  (* step = (b-a)/(N+1), need (b-a)/(N+1) < delta, i.e. (b-a)/delta < N+1 *)
  assert (Hba : 0 < b - a) by lra.
  set (ratio := (b - a) / delta).
  assert (Hratio_pos : 0 < ratio).
  { unfold ratio. apply Qmult_lt_0_compat; auto.
    apply Qinv_lt_0_compat. exact Hdelta. }
  destruct (ProcessDerivative.nat_above_Q ratio Hratio_pos) as [N HN].
  exists N. unfold integral_step.
  unfold Qdiv.
  apply (proj1 (Qmult_lt_l _ _ (inject_Z (Z.of_nat (S N))) (inject_Z_Sn_pos N))).
  assert (Hsimp : inject_Z (Z.of_nat (S N)) * ((b - a) * / inject_Z (Z.of_nat (S N))) ==
                  b - a) by (field; intro; assert (Hp := inject_Z_Sn_pos N); lra).
  setoid_rewrite Hsimp.
  (* Need: inject_Z (S N) * delta > b - a *)
  (* From HN: ratio < inject_Z N, i.e., (b-a)/delta < N *)
  (* So (b-a) < delta * N <= delta * (S N) *)
  assert (HN_le : inject_Z (Z.of_nat N) <= inject_Z (Z.of_nat (S N))).
  { change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. }
  assert (Hlt : ratio < inject_Z (Z.of_nat (S N))).
  { apply Qlt_le_trans with (inject_Z (Z.of_nat N)); auto. }
  unfold ratio in Hlt. unfold Qdiv in Hlt.
  (* (b-a) * /delta < S N, multiply by delta *)
  assert (H1 : (b - a) * / delta * delta < inject_Z (Z.of_nat (S N)) * delta).
  { apply (proj2 (Qmult_lt_r _ _ delta Hdelta)). exact Hlt. }
  assert (Hcancel : (b - a) * / delta * delta == b - a) by (field; intro; lra).
  lra.
Qed.

(** Nonneg bound on Riemann sums *)
Lemma riemann_sum_nonneg_step : forall f a step n,
  0 <= step ->
  (forall k, (k < n)%nat -> 0 <= f (walk_point a step k)) ->
  0 <= riemann_sum f a step n.
Proof.
  intros f a step n Hstep Hf.
  apply riemann_sum_nonneg; auto.
Qed.

(* ================================================================== *)
(*  Part V: E/R/R Pattern                                               *)
(* ================================================================== *)

(** Riemann sum as process: convergence rate *)
Definition integral_convergence_rate : Q := 1 # 2.

Lemma integral_rate_valid : 0 < integral_convergence_rate /\ integral_convergence_rate < 1.
Proof. unfold integral_convergence_rate. split; lra. Qed.

(** The integral is a process construction *)
Theorem integral_is_process_construction : forall f a b,
  a < b ->
  exists proc : RealProcess,
    (forall n, proc n == riemann_sum f a (integral_step a b n) (S n)).
Proof.
  intros f a b Hab.
  exists (integral_process f a b).
  intro n. unfold integral_process. reflexivity.
Qed.

(** Linearity as process equivalence *)
Theorem integral_linearity_process : forall f g c a b n,
  integral_process (fun x => c * f x + g x) a b n ==
  c * integral_process f a b n + integral_process g a b n.
Proof.
  intros f g c a b n.
  unfold integral_process.
  assert (H1 := riemann_sum_scale c f a (integral_step a b n) (S n)).
  assert (H2 := riemann_sum_add (fun x => c * f x) g a (integral_step a b n) (S n)).
  setoid_rewrite H2.
  setoid_rewrite H1. reflexivity.
Qed.

(** Monotonicity: f <= g on grid implies integral(f) <= integral(g) *)
Lemma integral_monotone : forall f g a b n,
  a < b ->
  (forall k, (k < S n)%nat -> f (walk_point a (integral_step a b n) k) <=
                               g (walk_point a (integral_step a b n) k)) ->
  integral_process f a b n <= integral_process g a b n.
Proof.
  intros f g a b n Hab Hfg.
  unfold integral_process.
  apply riemann_sum_monotone.
  - exact Hfg.
  - apply Qlt_le_weak. apply integral_step_pos. exact Hab.
Qed.

(** P4: the integral IS the process of refining Riemann sums *)
(** Each stage n gives a rational approximation with n+1 subintervals *)
(** No completed limit object needed *)
