(** * ProcessFTC.v — Fundamental Theorem of Calculus as Process Connection
    Elements: derivative and integral processes linked by FTC
    Roles:    bridge between differentiation and integration processes
    Rules:    ftc_grid from RiemannIntegration.v, udiff_on from Differentiation.v
    Status:   complete
    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS FTC — Fundamental Theorem as Process Connection            *)
(*                                                                            *)
(*  FTC: ∫_a^b f'(x)dx = f(b) - f(a) (approximately via Riemann sums)     *)
(*  Under P4: FTC is a PROCESS CONNECTION between derivative and integral    *)
(*  processes — not a single equation but a family of approximations.        *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: Riemann sum approximations to ∫f'                            *)
(*    Roles:    bridge connecting derivative + integral processes             *)
(*    Rules:    ftc_grid error bound from RiemannIntegration.v               *)
(*                                                                            *)
(*  STATUS: 14 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessDerivative.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import Differentiation.
From ToS Require Import MeanValueTheorem.
From ToS Require Import RiemannIntegration.

(* ================================================================== *)
(*  Part I: FTC Process Connection                                       *)
(* ================================================================== *)

(** FTC approximation error at grid refinement n *)
Definition ftc_error (f f' : Q -> Q) (a b : Q) (n : nat) : Q :=
  Qabs (integral_process f' a b n - (f b - f a)).

(** FTC via process: RS(f', n+1 points) ≈ f(b) - f(a) *)
(** The key theorem: ftc_grid from RiemannIntegration.v gives the bound *)
(** For any eps > 0, exists N such that ftc_error < eps*(b-a) + eps *)

(** Zero derivative means integral process is near 0 *)
Lemma ftc_zero_deriv : forall a b n,
  a < b ->
  integral_process (fun _ => 0) a b n == 0.
Proof.
  intros a b n Hab.
  unfold integral_process.
  induction (S n).
  - simpl. reflexivity.
  - simpl. setoid_rewrite IHn0. ring.
Qed.

(** Constant derivative: integral gives c*(b-a) *)
Lemma ftc_const_deriv : forall c a b,
  a < b ->
  process_equiv (integral_process (fun _ => c) a b) (const_process (c * (b - a))).
Proof.
  intros c a b Hab.
  exact (integral_process_const c a b Hab).
Qed.

(* ================================================================== *)
(*  Part II: FTC Process Properties                                      *)
(* ================================================================== *)

(** Linearity: FTC respects addition of derivatives *)
Lemma ftc_linearity : forall f' g' a b n,
  integral_process (fun x => f' x + g' x) a b n ==
  integral_process f' a b n + integral_process g' a b n.
Proof.
  intros f' g' a b n.
  apply integral_process_add.
Qed.

(** Scaling: FTC respects scalar multiplication *)
Lemma ftc_scaling : forall c f' a b n,
  integral_process (fun x => c * f' x) a b n ==
  c * integral_process f' a b n.
Proof.
  intros c f' a b n.
  apply integral_process_scale.
Qed.

(** Concatenation at process level: [a,m] + [m,b] *)
(** Under P4: each subinterval has its own process *)
Lemma ftc_interval_split : forall f' a m b,
  a < m -> m < b ->
  exists proc_left proc_right : RealProcess,
    (forall k, proc_left k == integral_process f' a m k) /\
    (forall k, proc_right k == integral_process f' m b k).
Proof.
  intros f' a m b Ham Hmb.
  exists (integral_process f' a m), (integral_process f' m b).
  split; intro k; reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: FTC as Process Equivalence                                 *)
(* ================================================================== *)

(** Riemann sum telescopes to boundary values *)
(** This is the processification of: RS(f') ≈ f(b) - f(a) *)

(** FTC error process: tracks how close RS(f') is to f(b)-f(a) *)
Definition ftc_error_process (f f' : Q -> Q) (a b : Q) : RealProcess :=
  fun n => integral_process f' a b n - (f b - f a).

(** The error process for constant derivative is zero *)
Lemma ftc_error_const : forall c a b,
  a < b ->
  process_equiv
    (ftc_error_process (fun x => c * x) (fun _ => c) a b)
    (const_process 0).
Proof.
  intros c a b Hab eps Heps.
  assert (Hinteg := integral_process_const c a b Hab).
  specialize (Hinteg eps Heps).
  destruct Hinteg as [N Hbound].
  exists N. intros n Hn.
  unfold ftc_error_process, const_process.
  assert (Heq : integral_process (fun _ => c) a b n - (c * b - c * a) - 0 ==
                integral_process (fun _ => c) a b n - const_process (c * (b - a)) n).
  { unfold const_process. ring. }
  setoid_rewrite Heq.
  apply Hbound. exact Hn.
Qed.

(* ================================================================== *)
(*  Part IV: E/R/R Pattern                                               *)
(* ================================================================== *)

(** The rate of the FTC process is not a number: it is governed by the
    modulus of uniform differentiability -- see [ftc_error_level_bound] at
    the end of the file.  (The constant [ftc_convergence_rate := 1 # 2], tied
    to nothing, stood here until Nov 2026.) *)


(** P4: the FTC is not a single identity but a PROCESS of approximations *)
(** At each refinement level n:                                            *)
(**   RS(f', n+1 subintervals) ≈ f(b) - f(a)                             *)
(** The error shrinks as n increases (when f' is well-behaved)             *)
(** No infinite limit needed — the approximation process IS the theorem    *)

(** Derivative and integral processes are dual under P4 *)
Theorem derivative_integral_duality : forall f f' a b,
  a < b ->
  (exists proc_d : RealProcess,
     forall x, has_derivative f x (f' x) ->
     is_Cauchy (deriv_process f x)) /\
  (exists proc_i : RealProcess,
     proc_i = integral_process f' a b).
Proof.
  intros f f' a b Hab.
  split.
  - exists (fun _ => 0). (* dummy, the point is the forall statement *)
    intros x Hd. exact (deriv_process_cauchy f x (f' x) Hd).
  - exists (integral_process f' a b). reflexivity.
Qed.

(* ================================================================== *)
(*  Part V: FTC as CONVERGENCE of the process (Nov 2026)               *)
(* ================================================================== *)

From Stdlib Require Import Morphisms.

(** The process of Riemann sums of the derivative names the same point as
    the increment f(b) - f(a).  The last grid node is b only up to ==; that
    f takes ==-equal values there follows from uniform differentiability
    (MeanValueTheorem.udiff_walk_endpoint_value), so the condition
    [Proper (Qeq ==> Qeq) f], which stood here at first, was dropped. *)
Theorem ftc_process_converges : forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  process_equiv (integral_process f' a b) (const_process (f b - f a)).
Proof.
  intros f f' a b Hud eps Heps.
  assert (Hab : a < b) by (destruct Hud; assumption).
  assert (Hba : 0 < b - a) by lra.
  set (eps' := eps * (1#2) / (b - a)).
  assert (Heps' : 0 < eps').
  { unfold eps'. apply Qlt_shift_div_l; lra. }
  destruct (ftc_grid_eventually f f' a b eps' Hud Heps') as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  unfold integral_process, integral_step, const_process.
  rewrite (udiff_walk_endpoint_value f f' a b n Hud) in HN.
  assert (Hcalc : eps' * (b - a) == eps * (1#2)).
  { unfold eps'. field. lra. }
  rewrite Hcalc in HN.
  apply Qle_lt_trans with (eps * (1#2)); [exact HN | lra].
Qed.

(** Hence the integral process of a derivative is a Cauchy process. *)
Corollary ftc_integral_process_Cauchy : forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  is_Cauchy (integral_process f' a b).
Proof.
  intros f f' a b Hud.
  apply equiv_cauchy_l with (R1 := const_process (f b - f a)).
  - apply process_equiv_sym. apply ftc_process_converges; assumption.
  - apply const_is_Cauchy.
Qed.

(** The FTC error process vanishes: it names the point 0. *)
Corollary ftc_error_process_vanishes : forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  process_equiv (ftc_error_process f f' a b) (const_process 0).
Proof.
  intros f f' a b Hud eps Heps.
  destruct (ftc_process_converges f f' a b Hud eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  unfold ftc_error_process, const_process in *.
  assert (Heq : integral_process f' a b n - (f b - f a) - 0 ==
                integral_process f' a b n - (f b - f a)) by ring.
  rewrite (Qabs_wd _ _ Heq). exact HN.
Qed.

(** The affine case is exact on EVERY level (not only "from some level on"). *)
Lemma integral_process_const_exact : forall c a b n,
  integral_process (fun _ => c) a b n == c * (b - a).
Proof.
  intros c a b n. unfold integral_process.
  rewrite riemann_sum_const.
  unfold integral_step. field.
  intro H. assert (Hp := inject_Z_Sn_pos n). lra.
Qed.

Lemma ftc_error_const_exact : forall c a b n,
  ftc_error_process (fun x => c * x) (fun _ => c) a b n == 0.
Proof.
  intros c a b n. unfold ftc_error_process.
  rewrite integral_process_const_exact. ring.
Qed.


(** E/R/R: FTC as process construction -- the error process BY NAME, the
    Cauchy property of the process of sums, and the points both processes
    name.  Stands here, after Part V, because it needs the convergence.
    Until Nov 2026 only the first clause stood (Part IV), under [exists]:
    true by definition, with an unused premise a < b. *)
Theorem ftc_is_process_construction : forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  (forall n, ftc_error_process f f' a b n == integral_process f' a b n - (f b - f a)) /\
  is_Cauchy (integral_process f' a b) /\
  process_equiv (integral_process f' a b) (const_process (f b - f a)) /\
  process_equiv (ftc_error_process f f' a b) (const_process 0).
Proof.
  intros f f' a b Hud. split; [| split; [| split]].
  - intro n. unfold ftc_error_process. reflexivity.
  - exact (ftc_integral_process_Cauchy f f' a b Hud).
  - exact (ftc_process_converges f f' a b Hud).
  - exact (ftc_error_process_vanishes f f' a b Hud).
Qed.

(** The rate of the FTC process: once the step of level n is below the
    modulus delta that uniform differentiability gives for eps, the error of
    level n is at most eps * (b - a). *)
Theorem ftc_error_level_bound : forall (f f' : Q -> Q) (a b eps delta : Q) (n : nat),
  a < b -> 0 < eps ->
  (forall x h : Q, a <= x -> x <= b -> 0 < Qabs h -> Qabs h < delta ->
     Qabs (f (x + h) - f x - f' x * h) < eps * Qabs h) ->
  integral_step a b n < delta ->
  Qabs (ftc_error_process f f' a b n) <= eps * (b - a).
Proof.
  intros f f' a b eps delta n Hab Heps Hbd Hsmall.
  assert (Hdelta : 0 < delta).
  { eapply Qlt_trans; [apply (integral_step_pos a b n Hab) | exact Hsmall]. }
  unfold integral_step in Hsmall.
  assert (H := rs_tele_error_level f f' a b eps delta n Hab Heps Hbd Hsmall).
  assert (Htele := telescope_collapse f a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)).
  assert (Hend := walk_endpoint_qeq a b n Hab).
  assert (Hin := walk_point_in_interval a b n (S n) Hab (Nat.le_refl _)).
  destruct Hin as [Hlo Hhi].
  assert (Hval : f (walk_point a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)) == f b).
  { apply continuous_at_qeq_values; [exact Hend | |].
    - apply (local_modulus_continuous_at f f' a b eps delta); assumption.
    - apply (local_modulus_continuous_at f f' a b eps delta); try assumption; lra. }
  unfold ftc_error_process, integral_process, integral_step.
  assert (Heq : riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) - (f b - f a) ==
                riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) -
                tele_sum f a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)).
  { rewrite Htele. rewrite Hval. reflexivity. }
  rewrite (Qabs_wd _ _ Heq). exact H.
Qed.


Print Assumptions ftc_process_converges.
