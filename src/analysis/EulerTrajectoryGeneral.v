(** * EulerTrajectoryGeneral.v -- The Euler trajectory on the rational grid in general form: every grid, every node, as a ToS System

    Elements: the grid nodes [grid N k] = k/N; the values [euler_traj f y0 N k]
              of the Euler trajectory (both defined in PicardLindelof.v); the
              natural numbers N (resolution) and k (stage).
    Roles:    N -- role-resolution; k -- role-stage; h = 1/N -- role-increment;
              t_k h -- role-defect of the method for y' = 2t; the stage
              [euler_traj f_identity 1 (S N) (S N)] = (1 + 1/(N+1))^(N+1) --
              role-approximation on the ladder to e.
    Rules:    y_(k+1) = y_k + h f(t_k, y_k), h = 1/N. For a constant right-hand
              side the step is exact; for f = 2t the trajectory has the closed
              form t_k^2 - t_k h; for f = y the step multiplies by 1 + h.

    Proved (no axioms):
      - [euler_traj_const_exact]: for every constant right-hand side a, every
        initial value, every grid and every node, y_k = y0 + a t_k;
      - [euler_traj_quadratic_closed]: for y' = 2t, y(0) = 0, on every grid
        y_k = t_k^2 - t_k h; [euler_quadratic_error_general]: at t = 1 the
        error equals 1/N; it is positive and decreases as N grows;
      - [euler_traj_exp_closed]: for y' = y, y_k = y0 (1 + 1/N)^k;
        [exp1_is_euler_traj]: the e-ladder of ProcessExpProcess.v is this
        trajectory at k = N;
      - [euler_traj_exp_sandwich_all], [euler_traj_exp_increasing]: on the
        trajectory, 2 <= (1 + 1/N)^N < 3 and growth, for every N >= 1;
      - [euler_exp_ladder_modulus], [euler_exp_ladder_is_Cauchy]: the stages
        of the trajectory at t = 1 form a Cauchy process, with the modulus
        3/(N0+1).

    P4 diagnostic: all statements are about finite grids and finite stages;
      the two indices N and k stay separate arguments. Refinement of the grid
      is a direction of the process; no limit N -> infinity is built.

    NOT claimed:
      - convergence of the Euler trajectory to a solution for a general
        right-hand side, or any notion of a solution as a function with a
        derivative;
      - the number e as a completed object;
      - an error bound for a general right-hand side.

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import analysis.PicardLindelof.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessExpProcess.
From ToS Require Import process.ProcessExpLadder.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The grid                                                           *)
(* ===================================================================== *)

Lemma grid_NN : forall N : nat, (0 < N)%nat -> grid N N == 1.
Proof.
  intros N HN. unfold grid. pose proof (inj_pos N HN) as Hp.
  field. intro Hc. rewrite Hc in Hp. apply (Qlt_irrefl 0). exact Hp.
Qed.

(** N = 0: the step 1/0 over Q is zero and the trajectory stands still. *)
Lemma traj_N0_constant : forall (f : ODE) (y0 : Q) (k : nat),
  euler_traj f y0 0 k == y0.
Proof.
  intros f y0 k. induction k as [|k IH].
  - cbn [euler_traj]. reflexivity.
  - cbn [euler_traj]. unfold euler_step.
    change (1 / inject_Z (Z.of_nat 0)) with 0.
    transitivity (euler_traj f y0 0 k); [ ring | exact IH ].
Qed.

(* ===================================================================== *)
(*  2. Constant right-hand side: the method is exact                     *)
(* ===================================================================== *)

(** Every constant right-hand side, every initial value, every grid, every
    node: y_k = y0 + a t_k. *)
Theorem euler_traj_const_exact : forall (a y0 : Q) (N k : nat),
  euler_traj (f_const a) y0 N k == y0 + a * grid N k.
Proof.
  intros a y0 N k. induction k as [|k IH].
  - cbn [euler_traj]. rewrite grid_0. ring.
  - cbn [euler_traj]. unfold euler_step, f_const. rewrite IH.
    unfold grid. rewrite (inj_S k). unfold Qdiv. ring.
Qed.

(** y' = 1, y(0) = 0: the trajectory coincides with y(t) = t at every node. *)
Corollary euler_traj_linear_exact : forall N k : nat,
  euler_traj f_const_one 0 N k == grid N k.
Proof.
  intros N k. change f_const_one with (f_const 1).
  rewrite euler_traj_const_exact. ring.
Qed.

Corollary euler_traj_linear_end : forall N : nat, (0 < N)%nat ->
  euler_traj f_const_one 0 N N == 1.
Proof. intros N HN. rewrite euler_traj_linear_exact. apply grid_NN. exact HN. Qed.

(* ===================================================================== *)
(*  3. y' = 2t: the closed form and the error on every grid              *)
(* ===================================================================== *)

(** y_k = t_k^2 - t_k h, h = 1/N. *)
Theorem euler_traj_quadratic_closed : forall N k : nat,
  euler_traj f_two_t 0 N k ==
  grid N k * grid N k - grid N k * (1 / inject_Z (Z.of_nat N)).
Proof.
  intros N k. induction k as [|k IH].
  - cbn [euler_traj]. rewrite grid_0. ring.
  - cbn [euler_traj]. unfold euler_step, f_two_t. rewrite IH.
    unfold grid. rewrite (inj_S k). unfold Qdiv. ring.
Qed.

(** The defect at the node k equals t_k h. *)
Corollary euler_quadratic_defect : forall N k : nat,
  grid N k * grid N k - euler_traj f_two_t 0 N k ==
  grid N k * (1 / inject_Z (Z.of_nat N)).
Proof. intros N k. rewrite euler_traj_quadratic_closed. ring. Qed.

(** At the final moment t = 1 the error equals the step of the grid. *)
Corollary euler_quadratic_error_general : forall N : nat, (0 < N)%nat ->
  1 - euler_traj f_two_t 0 N N == 1 / inject_Z (Z.of_nat N).
Proof.
  intros N HN. rewrite euler_traj_quadratic_closed, (grid_NN N HN). ring.
Qed.

(** The method underestimates: the error at t = 1 is positive. *)
Corollary euler_quadratic_underestimates : forall N : nat, (0 < N)%nat ->
  euler_traj f_two_t 0 N N < 1.
Proof.
  intros N HN. pose proof (euler_quadratic_error_general N HN) as He.
  pose proof (inj_pos N HN) as Hp.
  assert (Hq : 0 < 1 / inject_Z (Z.of_nat N)).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hp. }
  lra.
Qed.

(** Refining the grid decreases the error: 1/(N+1) < 1/N. *)
Corollary euler_quadratic_error_decreases : forall N : nat, (0 < N)%nat ->
  1 - euler_traj f_two_t 0 (S N) (S N) < 1 - euler_traj f_two_t 0 N N.
Proof.
  intros N HN.
  rewrite (euler_quadratic_error_general N HN).
  rewrite (euler_quadratic_error_general (S N)) by lia.
  rewrite (inj_S N). pose proof (inj_pos N HN) as Hp.
  set (n := inject_Z (Z.of_nat N)) in *.
  assert (Hd : 1 / n - 1 / (n + 1) == 1 / (n * (n + 1))) by (field; split; lra).
  assert (Hpos : 0 < 1 / (n * (n + 1))).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat; lra. }
  lra.
Qed.

(* ===================================================================== *)
(*  4. y' = y: the closed form and the link to the e-ladder              *)
(* ===================================================================== *)

Theorem euler_traj_exp_closed : forall (y0 : Q) (N k : nat),
  euler_traj f_identity y0 N k == y0 * qpow (1 + 1 / inject_Z (Z.of_nat N)) k.
Proof.
  intros y0 N k. induction k as [|k IH].
  - cbn [euler_traj qpow]. ring.
  - cbn [euler_traj qpow]. rewrite euler_step_concrete, IH. ring.
Qed.

(** The trajectory of PicardLindelof.v and the local recursion of
    ProcessExpProcess.v are one and the same. *)
Theorem euler_traj_is_euler_yeqy : forall (y0 : Q) (N k : nat),
  euler_traj f_identity y0 N k == euler_yeqy (1 / inject_Z (Z.of_nat N)) y0 k.
Proof.
  intros y0 N k. rewrite euler_traj_exp_closed, euler_yeqy_closed. reflexivity.
Qed.

(** The e-ladder is the trajectory [euler_traj] at k = N. *)
Theorem exp1_is_euler_traj : forall N : nat,
  exp1_process N == euler_traj f_identity 1 (S N) (S N).
Proof.
  intro N. rewrite euler_traj_exp_closed. unfold exp1_process. ring.
Qed.

(* ===================================================================== *)
(*  5. The ladder (1 + 1/N)^N on the trajectory: bounds, growth, Cauchy  *)
(* ===================================================================== *)

Corollary euler_traj_exp_lower_all : forall N : nat,
  2 <= euler_traj f_identity 1 (S N) (S N).
Proof. intro N. rewrite <- exp1_is_euler_traj. apply exp1_lower. Qed.

(** 2 <= (1 + 1/N)^N < 3 for every N >= 1. *)
Corollary euler_traj_exp_sandwich_all : forall N : nat,
  2 <= euler_traj f_identity 1 (S N) (S N) /\
  euler_traj f_identity 1 (S N) (S N) < 3.
Proof.
  intro N. rewrite <- exp1_is_euler_traj.
  split; [ apply exp1_lower | apply exp1_upper ].
Qed.

(** (1 + 1/N)^N grows with N. *)
Corollary euler_traj_exp_increasing : forall N : nat,
  euler_traj f_identity 1 (S N) (S N) < euler_traj f_identity 1 (S (S N)) (S (S N)).
Proof.
  intro N. rewrite <- !exp1_is_euler_traj. apply exp1_increasing.
Qed.

(** The stages of the trajectory of y' = y at t = 1, by resolution. *)
Definition euler_exp_ladder (N : nat) : Q := euler_traj f_identity 1 (S N) (S N).

(** Beyond the resolution N0 any two stages differ by less than 3/(N0+1). *)
Theorem euler_exp_ladder_modulus : forall N0 m n : nat, (N0 <= m)%nat -> (N0 <= n)%nat ->
  Qabs (euler_exp_ladder m - euler_exp_ladder n) < 3 / inject_Z (Z.of_nat (S N0)).
Proof.
  intros N0 m n Hm Hn. unfold euler_exp_ladder.
  rewrite <- !exp1_is_euler_traj. apply exp1_modulus; assumption.
Qed.

Theorem euler_exp_ladder_is_Cauchy : is_Cauchy euler_exp_ladder.
Proof.
  intros eps Heps.
  destruct (exp1_is_Cauchy eps Heps) as [K HK].
  exists K. intros m n Hm Hn. unfold euler_exp_ladder.
  rewrite <- !exp1_is_euler_traj. apply HK; assumption.
Qed.
