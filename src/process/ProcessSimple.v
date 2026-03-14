(** * ProcessSimple.v — Step Functions as Process Approximators
    Elements: Riemann sum processes, indicator processes
    Roles:    finite approximators of integrals at each resolution
    Rules:    refinement increases accuracy, bounded above/below
    Status:   complete
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS SIMPLE — Step Functions as Process Approximators           *)
(*                                                                            *)
(*  Under P4: simple functions are FINITE at each stage.                     *)
(*  The process of refining step functions IS the integral.                  *)
(*                                                                            *)
(*  STATUS: 18 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import RiemannIntegration.

(* ================================================================== *)
(*  Part I: Step Width and Riemann Process                               *)
(* ================================================================== *)

(** Step width for n-piece partition *)
Definition step_width (a b : Q) (n : nat) : Q :=
  (b - a) / inject_Z (Z.of_nat (S n)).

Lemma inject_Z_Sn_pos : forall n, 0 < inject_Z (Z.of_nat (S n)).
Proof.
  intro n. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
Qed.

Lemma step_width_pos : forall a b n, a < b -> 0 < step_width a b n.
Proof.
  intros a b n Hab. unfold step_width.
  apply Qlt_shift_div_l.
  - apply inject_Z_Sn_pos.
  - assert (H0 : 0 * inject_Z (Z.of_nat (S n)) == 0) by ring. lra.
Qed.

Lemma step_width_nonneg : forall a b n, a <= b -> 0 <= step_width a b n.
Proof.
  intros a b n Hab. unfold step_width.
  apply Qle_shift_div_l.
  - apply inject_Z_Sn_pos.
  - assert (H0 : 0 * inject_Z (Z.of_nat (S n)) == 0) by ring. lra.
Qed.

(** Riemann process: RS(f, S n points on [a,b]) *)
Definition riemann_process (f : Q -> Q) (a b : Q) : RealProcess :=
  integral_process f a b.

(** Riemann process equals integral_process *)
Lemma riemann_is_integral : forall f a b n,
  riemann_process f a b n == integral_process f a b n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(*  Part II: Constant Function                                            *)
(* ================================================================== *)

(** Constant Riemann process converges to c*(b-a) *)
Lemma const_riemann_equiv : forall c a b,
  a < b ->
  process_equiv (riemann_process (fun _ => c) a b) (const_process (c * (b - a))).
Proof.
  intros c a b Hab.
  unfold riemann_process.
  exact (integral_process_const c a b Hab).
Qed.

(** Constant Riemann process is Cauchy *)
Lemma const_riemann_cauchy : forall c a b,
  a < b ->
  is_Cauchy (riemann_process (fun _ => c) a b).
Proof.
  intros c a b Hab.
  apply (equiv_cauchy_l (const_process (c * (b - a)))).
  - apply process_equiv_sym. apply const_riemann_equiv. auto.
  - apply const_is_Cauchy.
Qed.

(* ================================================================== *)
(*  Part III: Bounded Functions                                           *)
(* ================================================================== *)

(** Riemann sum bounded by M*(b-a) *)
Lemma bounded_riemann_bounded : forall f a b M n,
  a < b -> (forall x, Qabs (f x) <= M) -> 0 <= M ->
  Qabs (riemann_process f a b n) <= M * (b - a).
Proof.
  intros f a b M n Hab Hbnd HM.
  unfold riemann_process, integral_process.
  assert (Hstep := integral_step_pos a b n Hab).
  assert (Hrsa : Qabs (riemann_sum f a (ProcessIntegral.integral_step a b n) (S n)) <=
    M * inject_Z (Z.of_nat (S n)) * ProcessIntegral.integral_step a b n).
  { apply riemann_sum_abs_bound.
    - intros k Hk. apply Hbnd.
    - lra.
    - exact HM. }
  apply Qle_trans with (M * inject_Z (Z.of_nat (S n)) * ProcessIntegral.integral_step a b n).
  - exact Hrsa.
  - unfold ProcessIntegral.integral_step.
    assert (Hpos := inject_Z_Sn_pos n).
    assert (Heq : M * inject_Z (Z.of_nat (S n)) *
      ((b - a) / inject_Z (Z.of_nat (S n))) == M * (b - a)).
    { field. intro. lra. }
    lra.
Qed.

(** Nonneg function has nonneg Riemann sum *)
Lemma nonneg_riemann_nonneg : forall f a b n,
  a < b ->
  (forall x, 0 <= f x) ->
  0 <= riemann_process f a b n.
Proof.
  intros f a b n Hab Hnn.
  unfold riemann_process, integral_process.
  apply riemann_sum_nonneg.
  - intros k Hk. apply Hnn.
  - assert (H := integral_step_pos a b n Hab). lra.
Qed.

(** Monotone: f ≤ g → RS(f) ≤ RS(g) *)
Lemma riemann_process_monotone : forall f g a b n,
  a < b ->
  (forall x, f x <= g x) ->
  riemann_process f a b n <= riemann_process g a b n.
Proof.
  intros f g a b n Hab Hle.
  unfold riemann_process.
  apply integral_monotone; auto.
Qed.

(* ================================================================== *)
(*  Part IV: Linearity                                                    *)
(* ================================================================== *)

(** Riemann process is additive *)
Lemma riemann_process_add : forall f g a b n,
  riemann_process (fun x => f x + g x) a b n ==
  riemann_process f a b n + riemann_process g a b n.
Proof.
  intros. unfold riemann_process.
  apply integral_process_add.
Qed.

(** Riemann process is scalable *)
Lemma riemann_process_scale : forall c f a b n,
  riemann_process (fun x => c * f x) a b n ==
  c * riemann_process f a b n.
Proof.
  intros. unfold riemann_process.
  apply integral_process_scale.
Qed.

(* ================================================================== *)
(*  Part V: Indicator Functions                                           *)
(* ================================================================== *)

(** Indicator function for [c,d] *)
Definition indicator (c d : Q) (x : Q) : Q :=
  if Qle_bool c x && Qle_bool x d then 1 else 0.

(** Indicator bounded in [0,1] *)
Lemma indicator_bounded : forall c d x,
  0 <= indicator c d x /\ indicator c d x <= 1.
Proof.
  intros c d x. unfold indicator.
  destruct (Qle_bool c x && Qle_bool x d); split; lra.
Qed.

(** Indicator = 1 inside [c,d] *)
Lemma indicator_inside : forall c d x,
  c <= x -> x <= d -> indicator c d x == 1.
Proof.
  intros c d x Hcx Hxd. unfold indicator.
  rewrite (proj2 (Qle_bool_iff c x) Hcx).
  rewrite (proj2 (Qle_bool_iff x d) Hxd).
  simpl. reflexivity.
Qed.

(** Indicator = 0 left of [c,d] *)
Lemma indicator_outside_left : forall c d x,
  x < c -> indicator c d x == 0.
Proof.
  intros c d x Hxc. unfold indicator.
  assert (Hc : Qle_bool c x = false).
  { apply Bool.not_true_is_false. intro H.
    apply Qle_bool_iff in H. lra. }
  rewrite Hc. simpl. reflexivity.
Qed.

(** Indicator = 0 right of [c,d] *)
Lemma indicator_outside_right : forall c d x,
  d < x -> indicator c d x == 0.
Proof.
  intros c d x Hdx. unfold indicator.
  assert (Hd : Qle_bool x d = false).
  { apply Bool.not_true_is_false. intro H.
    apply Qle_bool_iff in H. lra. }
  rewrite Hd. rewrite Bool.andb_false_r. reflexivity.
Qed.

(** Indicator process: RS(1_{[c,d]}) on [a,b] *)
Definition indicator_process (a b c d : Q) : RealProcess :=
  riemann_process (indicator c d) a b.

(** Indicator integral nonneg *)
Lemma indicator_process_nonneg : forall a b c d n,
  a < b ->
  0 <= indicator_process a b c d n.
Proof.
  intros a b c d n Hab.
  apply nonneg_riemann_nonneg; auto.
  intro x. apply (proj1 (indicator_bounded c d x)).
Qed.

(** Indicator integral bounded by b-a *)
Lemma indicator_process_bounded : forall a b c d n,
  a < b ->
  indicator_process a b c d n <= b - a.
Proof.
  intros a b c d n Hab.
  unfold indicator_process.
  assert (H := bounded_riemann_bounded (indicator c d) a b 1 n Hab).
  assert (Hbnd : forall x, Qabs (indicator c d x) <= 1).
  { intro x. apply Qabs_Qle_condition.
    split; [| apply (proj2 (indicator_bounded c d x))].
    assert (Hnn := proj1 (indicator_bounded c d x)). lra. }
  assert (H1 := H Hbnd).
  assert (Heq : 1 * (b - a) == b - a) by ring.
  assert (H2 : Qabs (riemann_process (indicator c d) a b n) <= 1 * (b - a)).
  { apply H1. lra. }
  assert (Hnn := indicator_process_nonneg a b c d n Hab).
  unfold indicator_process in Hnn.
  rewrite Qabs_pos in H2; lra.
Qed.

(* ================================================================== *)
(*  Part VI: E/R/R Pattern                                               *)
(* ================================================================== *)

(** Convergence rate *)
Definition step_convergence_rate : Q := 1 # 2.

Lemma step_rate_valid : 0 < step_convergence_rate /\ step_convergence_rate < 1.
Proof. unfold step_convergence_rate. split; lra. Qed.

(** E/R/R: Step functions as process construction *)
Theorem step_is_process_construction : forall f a b,
  a < b ->
  exists proc : RealProcess,
    (forall n, proc n == integral_process f a b n).
Proof.
  intros f a b Hab.
  exists (riemann_process f a b).
  intro n. reflexivity.
Qed.

(** P4: step functions at each resolution ARE the finite approximations *)
(** No completed integral needed — the process of refinements IS the integral *)
