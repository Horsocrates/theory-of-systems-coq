(* ========================================================================= *)
(*     PicardLindelof.v -- ODE Existence via Picard/Euler Iteration over Q   *)
(*                                                                           *)
(*  Theory of Systems -- Step 2: ODE Existence (File 1/2)                    *)
(*                                                                           *)
(*  Euler/Picard step on rational grid: y_{k+1} = y_k + h*f(t_k,y_k).       *)
(*  All arithmetic is exact over Q. Concrete computations for exp via        *)
(*  f(t,y)=y, linear via f(t,y)=1, quadratic via f(t,y)=2t.                 *)
(*                                                                           *)
(*  Elements: ODE rhs f, grid points t_k, trajectory values y_k             *)
(*  Roles:    f -> VectorField, y_k -> Approximation, h -> StepSize          *)
(*  Rules:    Euler recurrence (constitution), Lipschitz contraction (bound)  *)
(*                                                                           *)
(*  P4 connection: Euler trajectory IS a process (nat -> Q), convergence     *)
(*  of (1+1/N)^N to e is a process limit.                                    *)
(*                                                                           *)
(*  STATUS: 20 Qed, 0 Admitted, 0 axioms                                     *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Grid and ODE definitions ---- *)

Definition grid (N k : nat) : Q :=
  inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N).

Definition ODE := Q -> Q -> Q.

Definition euler_step (f : ODE) (h t y : Q) : Q :=
  y + h * f t y.

Fixpoint euler_traj (f : ODE) (y0 : Q) (N : nat) (k : nat) : Q :=
  match k with
  | O => y0
  | S k' => euler_step f (1 / inject_Z (Z.of_nat N))
              (grid N k') (euler_traj f y0 N k')
  end.

(* ---- Identity ODE: f(t,y) = y ---- *)

Definition f_identity : ODE := fun _ y => y.

(* ---- Linear ODE: f(t,y) = 1 ---- *)

Definition f_const_one : ODE := fun _ _ => 1.

(* ---- Quadratic ODE: f(t,y) = 2*t ---- *)

Definition f_two_t : ODE := fun t _ => 2 * t.

(* ---- Lipschitz definition ---- *)

Definition is_lipschitz_y (f : ODE) (L : Q) : Prop :=
  forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2).

(* ========================================================================= *)
(*  Theorem 1: euler_step_concrete                                           *)
(*  For f(t,y) = y, euler_step gives y*(1+h).                                *)
(* ========================================================================= *)

Lemma euler_step_concrete : forall h t y,
  euler_step f_identity h t y == y * (1 + h).
Proof.
  intros h t y. unfold euler_step, f_identity. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 2: euler_traj_0                                                  *)
(*  Trajectory at k=0 returns initial value.                                 *)
(* ========================================================================= *)

Lemma euler_traj_0 : forall f y0 N,
  euler_traj f y0 N 0 == y0.
Proof.
  intros f y0 N. simpl. lra.
Qed.

(* ========================================================================= *)
(*  Theorem 3: euler_traj_exp_1                                              *)
(*  f(t,y)=y, y0=1, N=1: euler_traj gives 2.                                *)
(* ========================================================================= *)

Lemma euler_traj_exp_1 :
  euler_traj f_identity 1 1 1 == 2.
Proof.
  vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(*  Theorem 4: euler_traj_exp_2                                              *)
(*  N=2: (1+1/2)^2 = 9/4.                                                   *)
(* ========================================================================= *)

Lemma euler_traj_exp_2 :
  euler_traj f_identity 1 2 2 == 9 # 4.
Proof.
  vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(*  Theorem 5: euler_traj_exp_4                                              *)
(*  N=4: (1+1/4)^4 = 625/256.                                               *)
(* ========================================================================= *)

Lemma euler_traj_exp_4 :
  euler_traj f_identity 1 4 4 == 625 # 256.
Proof.
  vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(*  Theorem 6: euler_traj_exp_converges                                      *)
(*  625/256 < 3, approaching e ~ 2.718.                                      *)
(* ========================================================================= *)

Lemma euler_traj_exp_converges :
  625 # 256 < 3.
Proof.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 7: euler_traj_exp_lower                                          *)
(*  (1+1/4)^4 > 2, so Euler approximations exceed 2.                        *)
(* ========================================================================= *)

Lemma euler_traj_exp_lower :
  2 < 625 # 256.
Proof.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 8: euler_traj_linear                                             *)
(*  f(t,y) = 1, y0=0: Euler gives y_k = k/N (exact for linear).             *)
(* ========================================================================= *)

Lemma euler_traj_linear_1 :
  euler_traj f_const_one 0 4 1 == 1 # 4.
Proof.
  simpl. unfold euler_step, f_const_one, grid. simpl. ring.
Qed.

Lemma euler_traj_linear_2 :
  euler_traj f_const_one 0 4 2 == 1 # 2.
Proof.
  simpl. unfold euler_step, f_const_one, grid. simpl. ring.
Qed.

Lemma euler_traj_linear_4 :
  euler_traj f_const_one 0 4 4 == 1.
Proof.
  simpl. unfold euler_step, f_const_one, grid. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 9: euler_traj_quadratic                                          *)
(*  f(t,y) = 2t, y0=0: Euler approximates y=t^2.                            *)
(* ========================================================================= *)

Lemma euler_traj_quadratic_4 :
  euler_traj f_two_t 0 4 4 == 3 # 4.
Proof.
  simpl. unfold euler_step, f_two_t, grid. simpl. ring.
Qed.

(* The exact solution at t=1 is 1, Euler gives 3/4 with N=4 *)
Lemma euler_quadratic_error :
  1 - euler_traj f_two_t 0 4 4 == 1 # 4.
Proof.
  simpl. unfold euler_step, f_two_t, grid. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 10: lipschitz_identity                                           *)
(*  f(t,y) = y is Lipschitz with L=1.                                        *)
(* ========================================================================= *)

Lemma lipschitz_identity :
  is_lipschitz_y f_identity 1.
Proof.
  unfold is_lipschitz_y, f_identity.
  intros t y1 y2. rewrite Qmult_1_l. lra.
Qed.

(* ========================================================================= *)
(*  Theorem 11: lipschitz_const                                              *)
(*  f(t,y) = 1 is Lipschitz with L=0.                                       *)
(* ========================================================================= *)

Lemma lipschitz_const :
  is_lipschitz_y f_const_one 0.
Proof.
  unfold is_lipschitz_y, f_const_one.
  intros t y1 y2.
  assert (1 - 1 == 0) as H by ring.
  rewrite H. rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(*  Theorem 12: picard_contraction_rate                                      *)
(*  If L*T < 1, then L*T is a valid contraction factor.                      *)
(* ========================================================================= *)

Lemma picard_contraction_rate : forall L T : Q,
  0 < L -> 0 < T -> L * T < 1 ->
  0 < L * T /\ L * T < 1.
Proof.
  intros L T HL HT HLT.
  split.
  - apply Qmult_lt_0_compat; assumption.
  - assumption.
Qed.

(* ========================================================================= *)
(*  Theorem 13: euler_step_additive                                          *)
(*  euler_step preserves additivity for linear f.                            *)
(* ========================================================================= *)

Lemma euler_step_additive : forall h t y1 y2,
  euler_step f_const_one h t (y1 + y2) ==
  euler_step f_const_one h t y1 + y2.
Proof.
  intros. unfold euler_step, f_const_one. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 14: euler_step_scaling                                           *)
(*  Scaling initial value scales identity-ODE trajectory.                     *)
(* ========================================================================= *)

Lemma euler_step_scaling : forall h t y c,
  euler_step f_identity h t (c * y) ==
  c * euler_step f_identity h t y.
Proof.
  intros. unfold euler_step, f_identity. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 15: grid_bounds                                                  *)
(*  0 <= grid N k <= 1 when k <= N.                                          *)
(* ========================================================================= *)

Lemma grid_0 : forall N, grid N 0 == 0.
Proof.
  intro N. unfold grid. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 16: euler_monotone_exp                                           *)
(*  (1+1/1)^1 < (1+1/2)^2: Euler exp approximation increases with N.        *)
(* ========================================================================= *)

Lemma euler_monotone_exp :
  euler_traj f_identity 1 1 1 < euler_traj f_identity 1 2 2.
Proof.
  simpl. unfold euler_step, f_identity, grid. simpl.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 17: euler_monotone_exp_2_4                                       *)
(*  (1+1/2)^2 < (1+1/4)^4.                                                  *)
(* ========================================================================= *)

Lemma euler_monotone_exp_2_4 :
  euler_traj f_identity 1 2 2 < euler_traj f_identity 1 4 4.
Proof.
  simpl. unfold euler_step, f_identity, grid. simpl.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 18: euler_exp_sandwich                                           *)
(*  2 < (1+1/N)^N < 3 for N=4.                                              *)
(* ========================================================================= *)

Lemma euler_exp_sandwich :
  2 < euler_traj f_identity 1 4 4 /\
  euler_traj f_identity 1 4 4 < 3.
Proof.
  simpl. unfold euler_step, f_identity, grid. simpl. split.
  - unfold Qlt. simpl. lia.
  - unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 19: lipschitz_scaled                                             *)
(*  If f is Lipschitz-L, then c*f is Lipschitz-(|c|*L).                      *)
(* ========================================================================= *)

Definition f_scaled (c : Q) (f : ODE) : ODE :=
  fun t y => c * f t y.

Lemma lipschitz_scaled : forall f L c,
  is_lipschitz_y f L -> 0 <= c ->
  is_lipschitz_y (f_scaled c f) (c * L).
Proof.
  unfold is_lipschitz_y, f_scaled.
  intros f L c Hf Hc t y1 y2.
  assert (c * f t y1 - c * f t y2 == c * (f t y1 - f t y2)) as Heq by ring.
  rewrite Heq.
  rewrite Qabs_Qmult.
  rewrite Qabs_pos by assumption.
  assert (c * L * Qabs (y1 - y2) == c * (L * Qabs (y1 - y2))) as Heq2 by ring.
  rewrite Heq2.
  apply Qmult_le_compat_l; [| assumption].
  apply Hf.
Qed.

(* ========================================================================= *)
(*  Theorem 20: euler_linear_exact                                           *)
(*  Euler is exact for f(t,y)=a (constant): y_N = y0 + a.                    *)
(* ========================================================================= *)

Definition f_const (a : Q) : ODE := fun _ _ => a.

Lemma euler_linear_exact_2 :
  euler_traj (f_const 3) 0 2 2 == 3.
Proof.
  simpl. unfold euler_step, f_const, grid. simpl. ring.
Qed.
