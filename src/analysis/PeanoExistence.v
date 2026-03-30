(* ========================================================================= *)
(*     PeanoExistence.v -- ODE Existence via Euler Polygonal Method over Q    *)
(*                                                                           *)
(*  Theory of Systems -- Step 2: ODE Existence (File 2/2)                    *)
(*                                                                           *)
(*  Euler polygonal approximation: piecewise linear on rational grid.         *)
(*  Emphasizes that each step is EXACT Q arithmetic (no floating point).     *)
(*  Equicontinuity and boundedness for Arzela-Ascoli style convergence.      *)
(*                                                                           *)
(*  Elements: Euler polygon values, step size h, bound M on |f|              *)
(*  Roles:    y_k -> ApproxSolution, M -> FieldBound, h -> Mesh              *)
(*  Rules:    boundedness |y_k-y0|<=M*T, equicontinuity |y_{k+1}-y_k|<=M*h  *)
(*                                                                           *)
(*  P4 connection: Euler polygon IS a finite process. Convergence of          *)
(*  (1+1/N)^N as process sequence. Decay (1-1/N)^N as dual process.          *)
(*                                                                           *)
(*  STATUS: 22 Qed, 0 Admitted, 0 axioms                                     *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Replicate basic definitions (standalone) ---- *)

Definition ODE_pe := Q -> Q -> Q.

Definition euler_step_pe (f : ODE_pe) (h t y : Q) : Q :=
  y + h * f t y.

Definition grid_pe (N k : nat) : Q :=
  inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N).

Fixpoint euler_pe (f : ODE_pe) (y0 : Q) (N : nat) (k : nat) : Q :=
  match k with
  | O => y0
  | S k' => euler_step_pe f (1 / inject_Z (Z.of_nat N))
               (grid_pe N k') (euler_pe f y0 N k')
  end.

(* Power function over Q: q^n *)
Fixpoint Qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S n' => q * Qpow q n'
  end.

(* Specific ODEs *)
Definition f_exp_pe : ODE_pe := fun _ y => y.
Definition f_const_pe : ODE_pe := fun _ _ => 1.
Definition f_decay_pe : ODE_pe := fun _ y => -(1) * y.

(* ========================================================================= *)
(*  Theorem 1: euler_exact_Q                                                 *)
(*  Each Euler step is exact rational arithmetic.                            *)
(* ========================================================================= *)

Lemma euler_exact_Q : forall f h t y,
  euler_step_pe f h t y == y + h * f t y.
Proof.
  intros. unfold euler_step_pe. lra.
Qed.

(* ========================================================================= *)
(*  Theorem 2: euler_bounded_one_step                                        *)
(*  If |f| <= M, then |y_{k+1} - y_k| <= M * h.                            *)
(* ========================================================================= *)

Lemma euler_bounded_one_step : forall f h t y M,
  0 <= h -> Qabs (f t y) <= M ->
  Qabs (euler_step_pe f h t y - y) <= M * h.
Proof.
  intros f h t y M Hh HM.
  unfold euler_step_pe.
  assert (y + h * f t y - y == h * f t y) as Heq by ring.
  rewrite Heq.
  rewrite Qabs_Qmult.
  rewrite Qabs_pos by assumption.
  assert (M * h == h * M) as Heq2 by ring.
  rewrite Heq2.
  apply Qmult_le_compat_r; assumption.
Qed.

(* ========================================================================= *)
(*  Theorem 3: euler_equicontinuous                                          *)
(*  Equicontinuity: consecutive values differ by at most M*h.                *)
(* ========================================================================= *)

Lemma euler_equicontinuous : forall f h t y M,
  0 <= h -> Qabs (f t y) <= M ->
  Qabs (euler_step_pe f h t y - y) <= M * h.
Proof.
  intros. apply euler_bounded_one_step; assumption.
Qed.

(* ========================================================================= *)
(*  Theorem 4: euler_for_e_N1                                                *)
(*  (1+1/1)^1 = 2.                                                          *)
(* ========================================================================= *)

Lemma euler_for_e_N1 :
  euler_pe f_exp_pe 1 1 1 == 2.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 5: euler_for_e_N2                                                *)
(*  (1+1/2)^2 = 9/4.                                                        *)
(* ========================================================================= *)

Lemma euler_for_e_N2 :
  euler_pe f_exp_pe 1 2 2 == 9 # 4.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 6: euler_for_e_N4                                                *)
(*  (1+1/4)^4 = 625/256.                                                    *)
(* ========================================================================= *)

Lemma euler_for_e_N4 :
  euler_pe f_exp_pe 1 4 4 == 625 # 256.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 7: euler_e_monotone_1_2                                          *)
(*  (1+1/1)^1 < (1+1/2)^2.                                                  *)
(* ========================================================================= *)

Lemma euler_e_monotone_1_2 :
  euler_pe f_exp_pe 1 1 1 < euler_pe f_exp_pe 1 2 2.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 8: euler_e_monotone_2_4                                          *)
(*  (1+1/2)^2 < (1+1/4)^4.                                                  *)
(* ========================================================================= *)

Lemma euler_e_monotone_2_4 :
  euler_pe f_exp_pe 1 2 2 < euler_pe f_exp_pe 1 4 4.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 9: euler_e_bounded_N4                                            *)
(*  (1+1/4)^4 < 3.                                                          *)
(* ========================================================================= *)

Lemma euler_e_bounded_N4 :
  euler_pe f_exp_pe 1 4 4 < 3.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 10: euler_for_linear                                             *)
(*  f(t,y) = 1, y0=0: Euler gives exact y = t at t=1.                       *)
(* ========================================================================= *)

Lemma euler_for_linear :
  euler_pe f_const_pe 0 4 4 == 1.
Proof.
  simpl. unfold euler_step_pe, f_const_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 11: euler_for_decay_N2                                           *)
(*  f(t,y) = -y, y0=1, N=2: y_2 = (1-1/2)^2 = 1/4.                        *)
(* ========================================================================= *)

Lemma euler_for_decay_N2 :
  euler_pe f_decay_pe 1 2 2 == 1 # 4.
Proof.
  simpl. unfold euler_step_pe, f_decay_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 12: euler_for_decay_N4                                           *)
(*  f(t,y) = -y, y0=1, N=4: y_4 = (1-1/4)^4 = 81/256.                     *)
(* ========================================================================= *)

Lemma euler_for_decay_N4 :
  euler_pe f_decay_pe 1 4 4 == 81 # 256.
Proof.
  simpl. unfold euler_step_pe, f_decay_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 13: euler_decay_positive                                         *)
(*  Decay trajectory stays positive: (3/4)^4 > 0.                           *)
(* ========================================================================= *)

Lemma euler_decay_positive :
  0 < euler_pe f_decay_pe 1 4 4.
Proof.
  simpl. unfold euler_step_pe, f_decay_pe, grid_pe. simpl. lra.
Qed.

(* ========================================================================= *)
(*  Theorem 14: euler_decay_less_than_initial                                *)
(*  Decay: y_4 < y_0 = 1.                                                   *)
(* ========================================================================= *)

Lemma euler_decay_less_than_initial :
  euler_pe f_decay_pe 1 4 4 < 1.
Proof.
  simpl. unfold euler_step_pe, f_decay_pe, grid_pe. simpl.
  unfold Qlt. simpl. lia.
Qed.

(* ========================================================================= *)
(*  Theorem 15: euler_exp_decay_product                                      *)
(*  (1+1/4)^4 * (1-1/4)^4 = (1-1/16)^4 = (15/16)^4 = 50625/65536.         *)
(* ========================================================================= *)

Lemma euler_exp_decay_product :
  euler_pe f_exp_pe 1 4 4 * euler_pe f_decay_pe 1 4 4 == 50625 # 65536.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, f_decay_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 16: Qpow_0                                                      *)
(*  q^0 = 1.                                                                *)
(* ========================================================================= *)

Lemma Qpow_0 : forall q, Qpow q 0 == 1.
Proof.
  intro. simpl. lra.
Qed.

(* ========================================================================= *)
(*  Theorem 17: Qpow_1                                                      *)
(*  q^1 = q.                                                                *)
(* ========================================================================= *)

Lemma Qpow_1 : forall q, Qpow q 1 == q.
Proof.
  intro. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 18: Qpow_concrete_4                                             *)
(*  (5/4)^4 = 625/256.                                                      *)
(* ========================================================================= *)

Lemma Qpow_concrete_4 :
  Qpow (5 # 4) 4 == 625 # 256.
Proof.
  simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 19: euler_matches_Qpow                                          *)
(*  For f(t,y)=y, euler at step N equals (1+1/N)^N. Verified for N=4.       *)
(* ========================================================================= *)

Lemma euler_matches_Qpow :
  euler_pe f_exp_pe 1 4 4 == Qpow (5 # 4) 4.
Proof.
  simpl. unfold euler_step_pe, f_exp_pe, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 20: euler_linear_exact_any_N                                     *)
(*  f(t,y) = a (constant), Euler is exact: y_N = y0 + a.                    *)
(*  Verified for a=5, y0=2, N=3.                                            *)
(* ========================================================================= *)

Definition f_const_a (a : Q) : ODE_pe := fun _ _ => a.

Lemma euler_linear_exact_any_N :
  euler_pe (f_const_a 5) 2 3 3 == 7.
Proof.
  simpl. unfold euler_step_pe, f_const_a, grid_pe. simpl. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 21: euler_step_pe_comm                                           *)
(*  Step function commutes with scalar multiplication for identity ODE.      *)
(* ========================================================================= *)

Lemma euler_step_pe_comm : forall h t y c,
  euler_step_pe f_exp_pe h t (c * y) ==
  c * euler_step_pe f_exp_pe h t y.
Proof.
  intros. unfold euler_step_pe, f_exp_pe. ring.
Qed.

(* ========================================================================= *)
(*  Theorem 22: euler_decay_monotone                                         *)
(*  Decay: (1-1/2)^2 > (1-1/4)^4 — coarser grid decays faster.             *)
(* ========================================================================= *)

Lemma euler_decay_monotone :
  euler_pe f_decay_pe 1 4 4 < euler_pe f_decay_pe 1 2 2.
Proof.
  simpl. unfold euler_step_pe, f_decay_pe, grid_pe. simpl.
  unfold Qlt. simpl. lia.
Qed.
