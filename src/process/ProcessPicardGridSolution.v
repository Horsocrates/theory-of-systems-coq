(** * ProcessPicardGridSolution.v -- The Picard operator on a grid: its fixed point exists, is unique at every rate and is the Euler polygon, as a ToS System

    Elements: grid functions y : nat -> Q read at the nodes k <= N; the
              iterates [picard_iter f h y0 n] of the Picard operator
              (ProcessPicardOperator.v); the natural numbers n (iteration),
              k (node), N (number of steps of the grid).
    Roles:    [picard_fix f h y0 N] = the (N+1)-th iterate -- role-solution
              on the grid; n -- role-stage of the iteration process;
              L * T -- role-rate of the contraction estimate; the number M of
              the convergence theorems -- role-modulus, one for all grids of
              the interval.
    Rules:    Phi(y)_k = y0 + h * sum_{j<k} f(t_j, y_j) reads only the nodes
              to the left of k: the operator is strictly triangular. Hence the
              iterates stop changing node after node, and a fixed point is
              determined node after node.

    Proved (no axioms):
      - [picard_iter_eventually_constant], [picard_fix_is_fixed],
        [picard_fixed_exists]: for every right-hand side f, every step h and
        every N the iterates coincide from the number N + 1 on, and the
        (N+1)-th iterate is a fixed point (Leibniz equalities; neither a
        Lipschitz condition nor L * T < 1 is used);
      - [picard_unique_any_rate], [picard_grid_exists_unique]: for a
        Lipschitz right-hand side the fixed point on the grid is unique at
        every value of L * T;
      - [picard_fixed_is_euler], [picard_fixed_eq_euler],
        [picard_fix_eq_euler_traj]: every fixed point satisfies the Euler
        recursion, i.e. it is the Euler polygon of the same grid (bridges to
        ProcessODEStability.euler and to PicardLindelof.euler_traj);
      - [picard_iter_sup_cauchy]: for L * T < 1 the iterates are eps-close
        from some number on, uniformly over the nodes -- through the gap
        [picard_iter_gap] and [Qpow_vanish];
      - [picard_iter_modulus_uniform], [picard_iter_modulus_grid_free]: that
        number depends on the rate, on the bound of the first gap and on eps
        only; on an interval of length T with L * T < 1 it is one and the
        same for all grids;
      - [picard_op_contraction_sup], [picard_iter_gap_sup]: the contraction
        and the gap written through the maximum over the nodes;
      - [rate_attained], [fix_lin_values], [fix_lin_unique]: outside the
        regime (L * T = 3) the coefficient L * T is attained, while the
        fixed point exists and is unique.

    P4 diagnostic: every statement is about finitely many rational values on
      a finite grid. "The limit of the iterates on the grid" is a finite grid
      function reached after N + 1 steps, not a completed infinite object.
      The refinement of the grid is a direction of the process; no limit over
      refinement is built here.

    NOT claimed:
      - a solution function on the interval as a limit over grid refinement
        (over Q its values need not be rational);
      - anything for a right-hand side that is Lipschitz only locally;
      - global continuation, blow-up, the maximal interval of existence;
      - that the Euler polygons of different grids draw together (see
        ProcessEulerRefinement.v).

    STATUS: 44 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import SeriesConvergence FixedPoint.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessMCT.   (* q_sum *)
From ToS Require Import process.ProcessPicardOperator.
(* files with declarations of the same names (euler_step, grid, qpow ...): no Import *)
From ToS Require analysis.PicardLindelof process.ProcessODEStability.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. Helpers                                                            *)
(* ===================================================================== *)

Lemma q_sum_ext_eq : forall (a b : nat -> Q) (k : nat),
  (forall j, (j < k)%nat -> a j = b j) -> q_sum a k = q_sum b k.
Proof.
  intros a b k. induction k as [|k IH]; intro H; cbn [q_sum].
  - reflexivity.
  - rewrite IH by (intros j Hj; apply H; lia).
    rewrite (H k) by lia. reflexivity.
Qed.

Lemma q_sum_ext_Qeq : forall (a b : nat -> Q) (k : nat),
  (forall j, (j < k)%nat -> a j == b j) -> q_sum a k == q_sum b k.
Proof.
  intros a b k. induction k as [|k IH]; intro H; cbn [q_sum].
  - reflexivity.
  - apply Qplus_comp.
    + apply IH. intros j Hj. apply H. lia.
    + apply H. lia.
Qed.

Lemma Qle_of_Qeq : forall a b : Q, a == b -> a <= b.
Proof. intros a b E. rewrite E. apply Qle_refl. Qed.

Lemma lt_of_scaled : forall a X eps B : Q,
  0 < a -> a * X <= B -> B < eps * a -> X < eps.
Proof.
  intros a X eps B Ha H1 H2.
  destruct (Qlt_le_dec X eps) as [Hlt|Hge]; [ exact Hlt | exfalso ].
  assert (H3 : a * eps <= a * X).
  { rewrite (Qmult_comm a eps), (Qmult_comm a X).
    apply Qmult_le_compat_r; lra. }
  lra.
Qed.

Lemma nat_Q_S : forall n : nat,
  inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity.
Qed.

Lemma nat_Q_pos : forall n : nat, (0 < n)%nat -> 0 < inject_Z (Z.of_nat n).
Proof. intros n Hn. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. Qed.

Lemma nat_Q_le : forall m n : nat, (m <= n)%nat ->
  inject_Z (Z.of_nat m) <= inject_Z (Z.of_nat n).
Proof. intros m n H. rewrite <- Zle_Qle. lia. Qed.

(** A finite sum of terms bounded by F is bounded by (number of terms) * F. *)
Lemma q_sum_abs_bound : forall (a : nat -> Q) (F : Q) (k : nat),
  (forall j, (j < k)%nat -> Qabs (a j) <= F) ->
  Qabs (q_sum a k) <= inject_Z (Z.of_nat k) * F.
Proof.
  intros a F k. induction k as [|k IH]; intro H.
  - cbn [q_sum]. change (inject_Z (Z.of_nat 0)) with 0.
    assert (E : 0 * F == 0) by ring. rewrite E.
    unfold Qle. simpl. lia.
  - cbn [q_sum]. rewrite nat_Q_S.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    assert (H1 : Qabs (q_sum a k) <= inject_Z (Z.of_nat k) * F)
      by (apply IH; intros j Hj; apply H; lia).
    assert (H2 : Qabs (a k) <= F) by (apply H; lia).
    assert (E : (inject_Z (Z.of_nat k) + 1) * F
                == inject_Z (Z.of_nat k) * F + F) by ring.
    rewrite E. apply Qplus_le_compat; assumption.
Qed.

Lemma Qpow_le_base : forall (a b : Q) (n : nat),
  0 <= a -> a <= b -> Qpow a n <= Qpow b n.
Proof.
  intros a b n Ha Hab. induction n as [|n IH]; cbn [Qpow]; [ apply Qle_refl | ].
  apply Qle_trans with (a * Qpow b n).
  - rewrite (Qmult_comm a (Qpow a n)), (Qmult_comm a (Qpow b n)).
    apply Qmult_le_compat_r; assumption.
  - apply Qmult_le_compat_r; [ exact Hab | ].
    apply SeriesConvergence.Qpow_nonneg. lra.
Qed.

(* ===================================================================== *)
(*  1. The operator is strictly triangular: the iterates stop changing,   *)
(*     the fixed point on the grid exists and is the Euler polygon.       *)
(*     Neither a Lipschitz condition nor L * T < 1 is needed.             *)
(* ===================================================================== *)

Section Triangular.

Variable f : Q -> Q -> Q.
Variable h y0 : Q.

(** Phi(y)_k depends only on the values y_j with j < k. *)
Lemma picard_op_ext_eq : forall (y z : nat -> Q) (k : nat),
  (forall j, (j < k)%nat -> y j = z j) ->
  picard_op f h y0 y k = picard_op f h y0 z k.
Proof.
  intros y z k H. unfold picard_op, picard_sum.
  assert (E : q_sum (fun j => f (tgrid h j) (y j)) k
              = q_sum (fun j => f (tgrid h j) (z j)) k).
  { apply q_sum_ext_eq. intros j Hj. rewrite (H j Hj). reflexivity. }
  rewrite E. reflexivity.
Qed.

(** At the node k the iterates stop changing from the number k + 1 on. *)
Lemma picard_iter_stable : forall n k, (k <= n)%nat ->
  picard_iter f h y0 (S (S n)) k = picard_iter f h y0 (S n) k.
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (k = 0%nat) by lia. subst k. reflexivity.
  - change (picard_iter f h y0 (S (S (S n))) k)
      with (picard_op f h y0 (picard_iter f h y0 (S (S n))) k).
    change (picard_iter f h y0 (S (S n)) k)
      with (picard_op f h y0 (picard_iter f h y0 (S n)) k).
    apply picard_op_ext_eq. intros j Hj. apply IH. lia.
Qed.

Lemma picard_iter_stable_ge : forall n m k, (k <= n)%nat -> (S n <= m)%nat ->
  picard_iter f h y0 m k = picard_iter f h y0 (S n) k.
Proof.
  intros n m k Hk. induction m as [|m IH]; intro Hm; [ lia | ].
  destruct (Nat.eq_dec m n) as [E|E].
  - subst. reflexivity.
  - assert (Hm' : (S n <= m)%nat) by lia.
    rewrite <- (IH Hm').
    destruct m as [|m']; [ lia | ].
    apply picard_iter_stable. lia.
Qed.

(** From the number N + 1 on all iterates coincide on the whole grid
    (Leibniz equality). *)
Theorem picard_iter_eventually_constant : forall (N m n k : nat),
  (S N <= m)%nat -> (S N <= n)%nat -> (k <= N)%nat ->
  picard_iter f h y0 m k = picard_iter f h y0 n k.
Proof.
  intros N m n k Hm Hn Hk.
  rewrite (picard_iter_stable_ge N m k Hk Hm).
  rewrite (picard_iter_stable_ge N n k Hk Hn). reflexivity.
Qed.

(** The fixed point on the grid: the (N+1)-th iterate. *)
Definition picard_fix (N : nat) : nat -> Q := picard_iter f h y0 (S N).

Theorem picard_fix_is_fixed : forall N k, (k <= N)%nat ->
  picard_op f h y0 (picard_fix N) k = picard_fix N k.
Proof.
  intros N k Hk. unfold picard_fix.
  change (picard_op f h y0 (picard_iter f h y0 (S N)) k)
    with (picard_iter f h y0 (S (S N)) k).
  apply picard_iter_stable. exact Hk.
Qed.

(** The iterates reach the fixed point: from the number N + 1 on they
    coincide with it at every node. *)
Theorem picard_iter_reaches_fix : forall (N m k : nat),
  (S N <= m)%nat -> (k <= N)%nat ->
  picard_iter f h y0 m k = picard_fix N k.
Proof.
  intros N m k Hm Hk. unfold picard_fix.
  apply (picard_iter_stable_ge N m k Hk Hm).
Qed.

(** Continuation along the grid: the solution on a longer grid coincides
    with the solution on a shorter one at all nodes of the shorter grid. *)
Theorem picard_fix_extends : forall N N' k, (N <= N')%nat -> (k <= N)%nat ->
  picard_fix N' k = picard_fix N k.
Proof.
  intros N N' k HN Hk. unfold picard_fix.
  apply (picard_iter_stable_ge N (S N') k Hk). lia.
Qed.

(** EXISTENCE of a fixed point of the Picard operator on the grid -- for
    every right-hand side f, every step h and every N. *)
Theorem picard_fixed_exists : forall N, exists y : nat -> Q,
  forall k, (k <= N)%nat -> picard_op f h y0 y k == y k.
Proof.
  intro N. exists (picard_fix N). intros k Hk.
  rewrite (picard_fix_is_fixed N k Hk). reflexivity.
Qed.

(** Every fixed point of the Picard operator on the grid is the Euler
    polygon:  y_0 = y0,  y_(k+1) = y_k + h f(t_k, y_k). *)
Theorem picard_fixed_is_euler : forall N (y : nat -> Q),
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  y 0%nat == y0 /\
  forall k, (k < N)%nat -> y (S k) == y k + h * f (tgrid h k) (y k).
Proof.
  intros N y Hfix. split.
  - assert (E := Hfix 0%nat ltac:(lia)).
    unfold picard_op, picard_sum in E. cbn [q_sum] in E. lra.
  - intros k Hk.
    assert (E1 := Hfix (S k) ltac:(lia)). assert (E2 := Hfix k ltac:(lia)).
    unfold picard_op, picard_sum in E1, E2. cbn [q_sum] in E1.
    set (S0 := q_sum (fun j => f (tgrid h j) (y j)) k) in *.
    set (fk := f (tgrid h k) (y k)) in *.
    lra.
Qed.

(** Without any condition: from the number N + 1 on the iterates are
    eps-close (they coincide). *)
Theorem picard_iter_sup_cauchy_triangular : forall (N : nat) (eps : Q), 0 < eps ->
  exists M : nat, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    forall k, (k <= N)%nat ->
      Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps.
Proof.
  intros N eps Heps. exists (S N). intros m n Hm Hn k Hk.
  rewrite (picard_iter_eventually_constant N m n k Hm Hn Hk).
  assert (Ez : picard_iter f h y0 n k - picard_iter f h y0 n k == 0) by ring.
  rewrite Ez. exact Heps.
Qed.

End Triangular.

(* ===================================================================== *)
(*  2. Uniqueness of the fixed point on the grid at EVERY value of L*T    *)
(* ===================================================================== *)

(** A Lipschitz right-hand side respects the equality of rationals in its
    second argument. *)
Lemma lipschitz_compat : forall (f : Q -> Q -> Q) (L : Q),
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall t y1 y2, y1 == y2 -> f t y1 == f t y2.
Proof.
  intros f L Hlip t y1 y2 E.
  pose proof (Hlip t y1 y2) as H.
  assert (E0 : Qabs (y1 - y2) == 0).
  { assert (Ez : y1 - y2 == 0) by lra. rewrite Ez. reflexivity. }
  rewrite E0 in H.
  assert (H' : Qabs (f t y1 - f t y2) <= 0) by lra.
  apply Qabs_Qle_condition in H'. lra.
Qed.

Theorem picard_unique_triangular : forall (f : Q -> Q -> Q) (h y0 : Q) (N : nat),
  (forall t y1 y2, y1 == y2 -> f t y1 == f t y2) ->
  forall (y z : nat -> Q),
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  (forall k, (k <= N)%nat -> picard_op f h y0 z k == z k) ->
  forall k, (k <= N)%nat -> y k == z k.
Proof.
  intros f h y0 N Hc y z Hy Hz.
  assert (Hstrong : forall k, (k <= N)%nat -> forall j, (j <= k)%nat -> y j == z j).
  { induction k as [|k IH]; intros Hk j Hj.
    - assert (j = 0%nat) by lia. subst j.
      apply Qeq_trans with (picard_op f h y0 y 0%nat); [ symmetry; apply Hy; exact Hk | ].
      apply Qeq_trans with (picard_op f h y0 z 0%nat); [ | apply Hz; exact Hk ].
      unfold picard_op, picard_sum. cbn [q_sum]. reflexivity.
    - destruct (Nat.eq_dec j (S k)) as [E|E].
      + subst j.
        apply Qeq_trans with (picard_op f h y0 y (S k)); [ symmetry; apply Hy; exact Hk | ].
        apply Qeq_trans with (picard_op f h y0 z (S k)); [ | apply Hz; exact Hk ].
        unfold picard_op, picard_sum.
        apply Qplus_comp; [ reflexivity | ].
        apply Qmult_comp; [ reflexivity | ].
        apply q_sum_ext_Qeq. intros i Hi. apply Hc. apply IH; lia.
      + apply IH; lia. }
  intros k Hk. apply (Hstrong k Hk k). lia.
Qed.

(** Uniqueness of the solution on the grid for a Lipschitz right-hand side
    -- WITHOUT the condition L * Tlen < 1 (and without 0 < L, 0 <= h). *)
Theorem picard_unique_any_rate : forall (f : Q -> Q -> Q) (L : Q),
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall (h y0 : Q) (N : nat) (y z : nat -> Q),
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  (forall k, (k <= N)%nat -> picard_op f h y0 z k == z k) ->
  forall k, (k <= N)%nat -> y k == z k.
Proof.
  intros f L Hlip h y0 N y z Hy Hz.
  apply (picard_unique_triangular f h y0 N (lipschitz_compat f L Hlip) y z Hy Hz).
Qed.

(** Existence and uniqueness together, at every value of L * T. *)
Theorem picard_grid_exists_unique : forall (f : Q -> Q -> Q) (L : Q),
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall (h y0 : Q) (N : nat),
  (forall k, (k <= N)%nat ->
     picard_op f h y0 (picard_fix f h y0 N) k == picard_fix f h y0 N k) /\
  (forall y : nat -> Q,
     (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
     forall k, (k <= N)%nat -> y k == picard_fix f h y0 N k).
Proof.
  intros f L Hlip h y0 N.
  assert (Hfix : forall k, (k <= N)%nat ->
            picard_op f h y0 (picard_fix f h y0 N) k == picard_fix f h y0 N k).
  { intros k Hk. rewrite (picard_fix_is_fixed f h y0 N k Hk). reflexivity. }
  split; [ exact Hfix | ].
  intros y Hy. apply (picard_unique_any_rate f L Hlip h y0 N y _ Hy Hfix).
Qed.

(* ===================================================================== *)
(*  3. Bridges: the fixed point is the Euler polygon of Chapters 8.4      *)
(*     and 8.2                                                            *)
(* ===================================================================== *)

(** To ProcessODEStability.euler (nodes t_k = k h, the same as tgrid):
    every fixed point coincides with the Euler polygon at all nodes. *)
Theorem picard_fixed_eq_euler : forall (f : Q -> Q -> Q) (h y0 : Q) (N : nat),
  (forall t y1 y2, y1 == y2 -> f t y1 == f t y2) ->
  forall y : nat -> Q,
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  forall k, (k <= N)%nat -> y k == ProcessODEStability.euler f h y0 k.
Proof.
  intros f h y0 N Hc y Hfix.
  destruct (picard_fixed_is_euler f h y0 N y Hfix) as [H0 Hstep].
  induction k as [|k IH]; intro Hk.
  - cbn [ProcessODEStability.euler]. exact H0.
  - cbn [ProcessODEStability.euler].
    eapply Qeq_trans; [ apply Hstep; lia | ].
    assert (IHk : y k == ProcessODEStability.euler f h y0 k) by (apply IH; lia).
    apply Qplus_comp; [ exact IHk | ].
    apply Qmult_comp; [ reflexivity | ].
    apply Hc. exact IHk.
Qed.

Corollary picard_fix_eq_euler : forall (f : Q -> Q -> Q) (h y0 : Q) (N : nat),
  (forall t y1 y2, y1 == y2 -> f t y1 == f t y2) ->
  forall k, (k <= N)%nat -> picard_fix f h y0 N k == ProcessODEStability.euler f h y0 k.
Proof.
  intros f h y0 N Hc. apply (picard_fixed_eq_euler f h y0 N Hc).
  intros k Hk. rewrite (picard_fix_is_fixed f h y0 N k Hk). reflexivity.
Qed.

(** To PicardLindelof.euler_traj (step 1/N, nodes k/N): for a right-hand
    side that respects the equality of rationals in both arguments, the
    fixed point of the Picard operator with the step h = 1/N is the Euler
    polygon of the resolution N. *)
Theorem picard_fix_eq_euler_traj : forall (f : Q -> Q -> Q) (y0 : Q) (N : nat),
  (forall t1 t2 y1 y2, t1 == t2 -> y1 == y2 -> f t1 y1 == f t2 y2) ->
  forall k, (k <= N)%nat ->
  picard_fix f (1 / inject_Z (Z.of_nat N)) y0 N k == PicardLindelof.euler_traj f y0 N k.
Proof.
  intros f y0 N Hcompat.
  set (h := 1 / inject_Z (Z.of_nat N)).
  destruct (picard_fixed_is_euler f h y0 N (picard_fix f h y0 N)) as [H0 Hstep].
  { intros k Hk. rewrite (picard_fix_is_fixed f h y0 N k Hk). reflexivity. }
  induction k as [|k IH]; intro Hk.
  - cbn [PicardLindelof.euler_traj]. exact H0.
  - cbn [PicardLindelof.euler_traj]. unfold PicardLindelof.euler_step.
    eapply Qeq_trans; [ apply Hstep; lia | ].
    assert (IHk : picard_fix f h y0 N k == PicardLindelof.euler_traj f y0 N k)
      by (apply IH; lia).
    apply Qplus_comp; [ exact IHk | ].
    apply Qmult_comp; [ reflexivity | ].
    apply Hcompat; [ | exact IHk ].
    unfold tgrid, PicardLindelof.grid, h, Qdiv. ring.
Qed.

(* ===================================================================== *)
(*  4. eps-convergence of the iterates for L * T < 1, with a number that  *)
(*     does not depend on the grid                                        *)
(* ===================================================================== *)

Lemma rpow_Qpow : forall (L h : Q) (N n : nat),
  rpow L h N n == Qpow (L * Tlen h N) n.
Proof.
  intros L h N n. induction n as [|n IH]; cbn [rpow Qpow].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rate_nonneg : forall (L h : Q) (N : nat),
  0 < L -> 0 <= h -> 0 <= L * Tlen h N.
Proof.
  intros L h N HL Hh.
  apply Qmult_le_0_compat; [ lra | apply Tlen_nonneg; exact Hh ].
Qed.

(** The tail of a geometric progression gets below any eps. *)
Lemma geom_tail_small : forall r C eps : Q,
  0 <= r -> r < 1 -> 0 <= C -> 0 < eps ->
  exists M : nat, C * Qpow r M < eps * (1 - r).
Proof.
  intros r C eps Hr0 Hr1 HC Heps.
  destruct (Qlt_le_dec 0 r) as [Hpos|Hzero].
  - assert (Htarget : 0 < eps * (1 - r) / (C + 1)).
    { unfold Qdiv. apply Qmult_lt_0_compat;
        [ apply Qmult_lt_0_compat; lra | apply Qinv_lt_0_compat; lra ]. }
    destruct (Qpow_vanish r _ Hpos Hr1 Htarget) as [M HMv].
    exists M.
    assert (Hp0 : 0 <= Qpow r M)
      by (apply SeriesConvergence.Qpow_nonneg; exact Hr0).
    assert (Hmul : Qpow r M * (C + 1) < eps * (1 - r) / (C + 1) * (C + 1)).
    { apply Qmult_lt_compat_r; [ lra | exact HMv ]. }
    assert (Hsimp : eps * (1 - r) / (C + 1) * (C + 1) == eps * (1 - r))
      by (field; lra).
    rewrite Hsimp in Hmul.
    set (p := Qpow r M) in *. lra.
  - exists 1%nat. cbn [Qpow].
    assert (Hr : r == 0) by lra.
    rewrite Hr.
    assert (Hz : C * (0 * 1) == 0) by ring. rewrite Hz.
    assert (Hz2 : eps * (1 - 0) == eps) by ring. rewrite Hz2. exact Heps.
Qed.

(** Telescoping bound: (1 - r) |Phi^m - Phi^n|_k <= C (r^n - r^m), n <= m. *)
Lemma picard_iter_tel : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h -> forall (y0 : Q) (N : nat),
  L * Tlen h N < 1 ->
  forall C, 0 <= C ->
  (forall k, (k <= N)%nat ->
     Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k) <= C) ->
  forall n m, (n <= m)%nat -> forall k, (k <= N)%nat ->
  (1 - L * Tlen h N) * Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k)
  <= C * (Qpow (L * Tlen h N) n - Qpow (L * Tlen h N) m).
Proof.
  intros f L HL Hlip h Hh y0 N Hrate C HC Hfirst n m.
  induction m as [|m IH]; intros Hnm k Hk.
  - assert (n = 0%nat) by lia. subst n.
    assert (E : Qabs (picard_iter f h y0 0 k - picard_iter f h y0 0 k) == 0).
    { assert (Ez : picard_iter f h y0 0 k - picard_iter f h y0 0 k == 0) by ring.
      rewrite Ez. reflexivity. }
    rewrite E. apply Qle_of_Qeq. ring.
  - destruct (Nat.eq_dec n (S m)) as [En|En].
    + subst n.
      assert (E : Qabs (picard_iter f h y0 (S m) k - picard_iter f h y0 (S m) k) == 0).
      { assert (Ez : picard_iter f h y0 (S m) k - picard_iter f h y0 (S m) k == 0) by ring.
        rewrite Ez. reflexivity. }
      rewrite E. apply Qle_of_Qeq. ring.
    + assert (Hnm' : (n <= m)%nat) by lia.
      pose proof (IH Hnm' k Hk) as HIH.
      pose proof (picard_iter_gap f L HL Hlip h Hh y0 N C m HC Hfirst k Hk) as Hgap.
      rewrite rpow_Qpow in Hgap.
      assert (Htri : Qabs (picard_iter f h y0 (S m) k - picard_iter f h y0 n k)
                     <= Qabs (picard_iter f h y0 (S m) k - picard_iter f h y0 m k)
                        + Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k)).
      { setoid_replace (picard_iter f h y0 (S m) k - picard_iter f h y0 n k)
          with ((picard_iter f h y0 (S m) k - picard_iter f h y0 m k)
                + (picard_iter f h y0 m k - picard_iter f h y0 n k)) by ring.
        apply Qabs_triangle. }
      cbn [Qpow].
      set (r := L * Tlen h N) in *.
      set (a := Qabs (picard_iter f h y0 (S m) k - picard_iter f h y0 n k)) in *.
      set (b := Qabs (picard_iter f h y0 (S m) k - picard_iter f h y0 m k)) in *.
      set (c := Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k)) in *.
      set (p := Qpow r m) in *. set (q := Qpow r n) in *.
      assert (H1r : 0 <= 1 - r) by lra.
      assert (H1 : (1 - r) * a <= (1 - r) * (b + c)).
      { rewrite (Qmult_comm (1 - r) a), (Qmult_comm (1 - r) (b + c)).
        apply Qmult_le_compat_r; [ exact Htri | exact H1r ]. }
      assert (H2 : (1 - r) * b <= (1 - r) * (p * C)).
      { rewrite (Qmult_comm (1 - r) b), (Qmult_comm (1 - r) (p * C)).
        apply Qmult_le_compat_r; [ exact Hgap | exact H1r ]. }
      lra.
Qed.

Lemma picard_iter_tail : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h -> forall (y0 : Q) (N : nat),
  L * Tlen h N < 1 ->
  forall C, 0 <= C ->
  (forall k, (k <= N)%nat ->
     Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k) <= C) ->
  forall M n m k, (M <= n)%nat -> (n <= m)%nat -> (k <= N)%nat ->
  (1 - L * Tlen h N) * Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k)
  <= C * Qpow (L * Tlen h N) M.
Proof.
  intros f L HL Hlip h Hh y0 N Hrate C HC Hfirst M n m k HMn Hnm Hk.
  pose proof (picard_iter_tel f L HL Hlip h Hh y0 N Hrate C HC Hfirst n m Hnm k Hk) as Htel.
  pose proof (rate_nonneg L h N HL Hh) as Hr0.
  assert (Hpm : 0 <= Qpow (L * Tlen h N) m)
    by (apply SeriesConvergence.Qpow_nonneg; exact Hr0).
  assert (Hmono : Qpow (L * Tlen h N) n <= Qpow (L * Tlen h N) M)
    by (apply qpow_le_mono; [ exact Hr0 | lra | exact HMn ]).
  assert (H1 : 0 <= C * Qpow (L * Tlen h N) m) by (apply Qmult_le_0_compat; assumption).
  assert (H2 : C * Qpow (L * Tlen h N) n <= C * Qpow (L * Tlen h N) M).
  { rewrite (Qmult_comm C (Qpow (L * Tlen h N) n)), (Qmult_comm C (Qpow (L * Tlen h N) M)).
    apply Qmult_le_compat_r; [ exact Hmono | exact HC ]. }
  set (r := L * Tlen h N) in *.
  set (X := Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k)) in *.
  lra.
Qed.

(** ONE number for all right-hand sides and all grids with the rate at most
    r < 1 and the first gap at most C: from that number on the iterates are
    eps-close at every node. *)
Theorem picard_iter_modulus_uniform : forall (r C eps : Q),
  0 <= r -> r < 1 -> 0 <= C -> 0 < eps ->
  exists M : nat,
    forall (f : Q -> Q -> Q) (L : Q), 0 < L ->
    (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
    forall h, 0 <= h -> forall (y0 : Q) (N : nat),
    L * Tlen h N <= r ->
    (forall k, (k <= N)%nat ->
       Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k) <= C) ->
    forall m n, (M <= m)%nat -> (M <= n)%nat -> forall k, (k <= N)%nat ->
      Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps.
Proof.
  intros r C eps Hr0 Hr1 HC Heps.
  destruct (geom_tail_small r C eps Hr0 Hr1 HC Heps) as [M HM].
  exists M. intros f L HL Hlip h Hh y0 N Hrate Hfirst.
  assert (Hrate1 : L * Tlen h N < 1) by lra.
  pose proof (rate_nonneg L h N HL Hh) as Hr'0.
  assert (key : forall a b k, (M <= b)%nat -> (b <= a)%nat -> (k <= N)%nat ->
            Qabs (picard_iter f h y0 a k - picard_iter f h y0 b k) < eps).
  { intros a b k HMb Hba Hk.
    pose proof (picard_iter_tail f L HL Hlip h Hh y0 N Hrate1 C HC Hfirst
                  M b a k HMb Hba Hk) as Ht.
    assert (Hpw : Qpow (L * Tlen h N) M <= Qpow r M)
      by (apply Qpow_le_base; assumption).
    assert (Hcp : C * Qpow (L * Tlen h N) M <= C * Qpow r M).
    { rewrite (Qmult_comm C (Qpow (L * Tlen h N) M)), (Qmult_comm C (Qpow r M)).
      apply Qmult_le_compat_r; assumption. }
    pose proof (Qabs_nonneg (picard_iter f h y0 a k - picard_iter f h y0 b k)) as HX.
    set (X := Qabs (picard_iter f h y0 a k - picard_iter f h y0 b k)) in *.
    set (r' := L * Tlen h N) in *.
    assert (Hx : (1 - r) * X <= (1 - r') * X).
    { apply Qmult_le_compat_r; [ lra | exact HX ]. }
    apply (lt_of_scaled (1 - r) X eps (C * Qpow r M)); [ lra | lra | exact HM ]. }
  intros m n Hm Hn k Hk.
  destruct (Nat.le_ge_cases n m) as [Hnm|Hmn].
  - apply key; assumption.
  - rewrite (Qabs_minus_sym (picard_iter f h y0 m k) (picard_iter f h y0 n k)).
    apply key; assumption.
Qed.

(** eps-convergence of the Picard iterates, uniform over the nodes. *)
Theorem picard_iter_sup_cauchy_C : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h -> forall (y0 : Q) (N : nat),
  L * Tlen h N < 1 ->
  forall C, 0 <= C ->
  (forall k, (k <= N)%nat ->
     Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k) <= C) ->
  forall eps, 0 < eps ->
  exists M : nat, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    forall k, (k <= N)%nat ->
      Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps.
Proof.
  intros f L HL Hlip h Hh y0 N Hrate C HC Hfirst eps Heps.
  destruct (picard_iter_modulus_uniform (L * Tlen h N) C eps
              (rate_nonneg L h N HL Hh) Hrate HC Heps) as [M HM].
  exists M. intros m n Hm Hn k Hk.
  apply (HM f L HL Hlip h Hh y0 N (Qle_refl _) Hfirst m n Hm Hn k Hk).
Qed.

(** The same without an outer constant: C is the maximum of the first gap
    over the grid. *)
Theorem picard_iter_sup_cauchy : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h -> forall (y0 : Q) (N : nat),
  L * Tlen h N < 1 ->
  forall eps, 0 < eps ->
  exists M : nat, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    forall k, (k <= N)%nat ->
      Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps.
Proof.
  intros f L HL Hlip h Hh y0 N Hrate eps Heps.
  set (g := fun k => Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k)).
  apply (picard_iter_sup_cauchy_C f L HL Hlip h Hh y0 N Hrate (gmax g N)).
  - eapply Qle_trans; [ apply Qabs_nonneg | apply (gmax_ub g N 0%nat); lia ].
  - intros k Hk. apply (gmax_ub g N k Hk).
  - exact Heps.
Qed.

(** The first gap, starting from the constant y0: at most T * F, where F
    bounds |f(t, y0)|. The bound does not depend on the number of nodes. *)
Lemma picard_first_gap : forall (f : Q -> Q -> Q) (h y0 F : Q) (N : nat),
  0 <= h -> (forall t, Qabs (f t y0) <= F) ->
  forall k, (k <= N)%nat ->
  Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k) <= Tlen h N * F.
Proof.
  intros f h y0 F N Hh HF k Hk.
  assert (HF0 : 0 <= F) by (eapply Qle_trans; [ apply Qabs_nonneg | apply (HF 0) ]).
  change (picard_iter f h y0 1 k) with (picard_op f h y0 (fun _ : nat => y0) k).
  change (picard_iter f h y0 0 k) with y0.
  unfold picard_op, picard_sum. cbv beta.
  set (S0 := q_sum (fun j => f (tgrid h j) y0) k).
  assert (E : y0 + h * S0 - y0 == h * S0) by ring.
  rewrite E, Qabs_Qmult, (Qabs_pos h Hh).
  assert (HS : Qabs S0 <= inject_Z (Z.of_nat k) * F).
  { unfold S0. apply q_sum_abs_bound. intros j _. apply HF. }
  pose proof (nat_Q_le k N Hk) as Hk'.
  unfold Tlen.
  apply Qle_trans with (h * (inject_Z (Z.of_nat k) * F)).
  - rewrite (Qmult_comm h (Qabs S0)), (Qmult_comm h (inject_Z (Z.of_nat k) * F)).
    apply Qmult_le_compat_r; assumption.
  - assert (E2 : h * (inject_Z (Z.of_nat k) * F)
                 == inject_Z (Z.of_nat k) * (h * F)) by ring.
    assert (E3 : inject_Z (Z.of_nat N) * h * F
                 == inject_Z (Z.of_nat N) * (h * F)) by ring.
    rewrite E2, E3.
    apply Qmult_le_compat_r; [ exact Hk' | apply Qmult_le_0_compat; assumption ].
Qed.

(** On an interval of length T with L * T < 1 the number from which the
    iterates are eps-close is ONE for all grids of the interval: it is
    chosen before the number of steps N. *)
Theorem picard_iter_modulus_grid_free : forall (f : Q -> Q -> Q) (L F T y0 : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  (forall t, Qabs (f t y0) <= F) ->
  0 <= T -> L * T < 1 ->
  forall eps, 0 < eps ->
  exists M : nat, forall N : nat, (0 < N)%nat ->
    forall m n, (M <= m)%nat -> (M <= n)%nat -> forall k, (k <= N)%nat ->
      Qabs (picard_iter f (T / inject_Z (Z.of_nat N)) y0 m k
            - picard_iter f (T / inject_Z (Z.of_nat N)) y0 n k) < eps.
Proof.
  intros f L F T y0 HL Hlip HF HT Hrate eps Heps.
  assert (HF0 : 0 <= F) by (eapply Qle_trans; [ apply Qabs_nonneg | apply (HF 0) ]).
  assert (Hr0 : 0 <= L * T) by (apply Qmult_le_0_compat; lra).
  assert (HC : 0 <= T * F) by (apply Qmult_le_0_compat; assumption).
  destruct (picard_iter_modulus_uniform (L * T) (T * F) eps Hr0 Hrate HC Heps) as [M HM].
  exists M. intros N HN m n Hm Hn k Hk.
  pose proof (nat_Q_pos N HN) as Hd.
  set (d := inject_Z (Z.of_nat N)) in *.
  assert (Hh : 0 <= T / d).
  { apply Qle_shift_div_l; [ exact Hd | ].
    assert (E0 : 0 * d == 0) by ring. rewrite E0. exact HT. }
  assert (ET : Tlen (T / d) N == T).
  { unfold Tlen. fold d. field. lra. }
  apply (HM f L HL Hlip (T / d) Hh y0 N); try assumption.
  - rewrite ET. apply Qle_refl.
  - intros j Hj.
    eapply Qle_trans; [ apply (picard_first_gap f (T / d) y0 F N Hh HF j Hj) | ].
    rewrite ET. apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  5. The contraction and the gap written through the maximum over the   *)
(*     nodes (the sup-metric of the page)                                 *)
(* ===================================================================== *)

Theorem picard_op_contraction_sup : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h -> forall (y0 : Q) (N : nat) (y z : nat -> Q),
  gmax (fun k => Qabs (picard_op f h y0 y k - picard_op f h y0 z k)) N
  <= (L * Tlen h N) * gmax (fun k => Qabs (y k - z k)) N.
Proof.
  intros f L HL Hlip h Hh y0 N y z.
  apply gmax_lub. intros k Hk.
  apply (picard_op_contraction f L HL Hlip h Hh y0 N y z).
  - eapply Qle_trans;
      [ apply Qabs_nonneg | apply (gmax_ub (fun j => Qabs (y j - z j)) N 0%nat); lia ].
  - exact Hk.
  - intros j Hj. apply (gmax_ub (fun j0 => Qabs (y j0 - z j0)) N j Hj).
Qed.

Theorem picard_iter_gap_sup : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall h, 0 <= h -> forall (y0 : Q) (N n : nat),
  gmax (fun k => Qabs (picard_iter f h y0 (S n) k - picard_iter f h y0 n k)) N
  <= rpow L h N n
     * gmax (fun k => Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k)) N.
Proof.
  intros f L HL Hlip h Hh y0 N n.
  set (g := fun k => Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k)).
  apply gmax_lub. intros k Hk.
  apply (picard_iter_gap f L HL Hlip h Hh y0 N (gmax g N) n).
  - eapply Qle_trans; [ apply Qabs_nonneg | apply (gmax_ub g N 0%nat); lia ].
  - intros j Hj. apply (gmax_ub g N j Hj).
  - exact Hk.
Qed.

(* ===================================================================== *)
(*  6. An example outside the regime L * T < 1                            *)
(*     y' = y, L = 1, h = 1, N = 3, T = 3, L * T = 3                      *)
(* ===================================================================== *)

Definition f_lin : Q -> Q -> Q := fun _ y => y.

Lemma f_lin_lipschitz : forall t y1 y2,
  Qabs (f_lin t y1 - f_lin t y2) <= 1 * Qabs (y1 - y2).
Proof. intros t y1 y2. unfold f_lin. lra. Qed.

Example rate_3_not_below_1 : ~ (1 * Tlen 1 3 < 1).
Proof. vm_compute. discriminate. Qed.

(** The fixed point is (1, 2, 4, 8). *)
Example fix_lin_values :
  picard_fix f_lin 1 1 3 0%nat == 1 /\ picard_fix f_lin 1 1 3 1%nat == 2 /\
  picard_fix f_lin 1 1 3 2%nat == 4 /\ picard_fix f_lin 1 1 3 3%nat == 8.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example fix_lin_unique : forall y : nat -> Q,
  (forall k, (k <= 3)%nat -> picard_op f_lin 1 1 y k == y k) ->
  forall k, (k <= 3)%nat -> y k == picard_fix f_lin 1 1 3 k.
Proof.
  intros y Hy.
  apply (proj2 (picard_grid_exists_unique f_lin 1 f_lin_lipschitz 1 1 3) y Hy).
Qed.

(** The coefficient L * T is attained: the constants 1 and 0 differ by
    D = 1, their images at the node N = 3 differ by exactly L * T * D = 3.
    For L * T > 1 the operator is not a contraction in the sup-metric,
    while the fixed point exists and is unique. *)
Example rate_attained :
  Qabs (picard_op f_lin 1 1 (fun _ => 1) 3 - picard_op f_lin 1 1 (fun _ => 0) 3)
  == (1 * Tlen 1 3) * 1.
Proof. vm_compute. reflexivity. Qed.

(** The second iterate has not yet reached the fixed point at the node 3
    (7 against 8): the number of iterations needed grows with the grid. *)
Example iterate_2_short_of_fix :
  ~ (picard_iter f_lin 1 1 2 3%nat == picard_fix f_lin 1 1 3 3%nat).
Proof. vm_compute. discriminate. Qed.
