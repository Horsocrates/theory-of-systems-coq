(** * ProcessPicardLipschitz.v -- The scalar Euler-Picard step under the Lipschitz condition alone: contraction, error process and what its limit is, as a ToS System

    Elements: rationals y0, h, L; the iterates y_n of the map
              E(y) = y0 + g(y) * h  ([euler_picard_iterate], ProcessPicard.v);
              the radius R = |g y0| h / (1 - L h); the numbers e_n of the
              error process.
    Roles:    g -- role-law of velocity (an autonomous right-hand side);
              y_n -- role-stage of the iteration; [y0 - R, y0 + R] --
              role-arena kept by the step; e_n -- role-error (bounds the
              distance from the stage n to every later stage); a solution p of
              p = y0 + h g(p) -- role-limit of the iteration (the value of one
              implicit Euler step).
    Rules:    g Lipschitz with the constant L and L h < 1  =>  E maps
              [y0 - R, y0 + R] into itself and contracts it with the
              coefficient L h; hence the iterates form a Cauchy process,
              |y_m - y_n| <= e_n for n <= m, and e_n -> 0.

    Proved (no axioms):
      - [euler_picard_contraction_lip], [euler_picard_cauchy_lip],
        [euler_picard_cauchy_vf]: the contraction and the Cauchy property of
        the scalar iteration under the Lipschitz condition and L h < 1 alone.
        The premise [is_bounded_auto] of ProcessPicard.euler_picard_contraction
        (the right-hand side is bounded on the whole of Q) is not needed;
      - [id_not_bounded_auto], [linear_not_bounded_auto]: a linear right-hand
        side a * y, a <> 0, does not satisfy that premise for any bound;
        [const_satisfies_both_premises]: the premises are satisfiable;
      - [euler_picard_fixed_iff], [euler_picard_iterate_to_fixed],
        [euler_picard_iterate_limit]: a fixed point of the step is a solution
        of p = y0 + h g(p); if such a rational p exists, the iterates approach
        it geometrically;
      - [linear_scalar_iteration_value], [linear_scalar_iteration_limit]: for
        y' = y, y0 = 1, h = 1/2 the iterates are 2 - (1/2)^n and tend to 2;
      - [euler_half_below], [scalar_limit_apart_from_euler_stages]: for the
        same problem every Euler polygon at the moment t = 1/2 is below 7/4.
        The limit of the scalar iteration is the value of one implicit step,
        not the limit of the Euler stages;
      - [euler_picard_error_process], [ep_err_vanishes], [ode_is_process_err]:
        the pair "solution process / error process", in which the error
        process bounds the distance between the stages and tends to zero;
        [ode_is_process_with_zero_err]: the conclusion of
        ProcessODE.ode_is_process holds with the zero "error process";
      - [newton2_contraction], [newton2_no_rational_fixed_point],
        [contraction_without_rational_fixed_point]: x |-> x/2 + 1/x contracts
        the segment [1, 2] of rationals, its iterates form a Cauchy process,
        and it has no rational fixed point.

    P4 diagnostic: every statement is about rational stages and rational
      bounds. A fixed point of the step is used only as a hypothesis ("if a
      rational p with p = y0 + h g(p) exists"); the last block shows that over
      Q it may be absent while the iterates are Cauchy. The limit stays a role.

    NOT claimed:
      - that the limit of the scalar iteration solves the Cauchy problem on an
        interval (it does not: see [scalar_limit_apart_from_euler_stages]);
      - that a rational fixed point of the step exists in general;
      - anything for a right-hand side that is Lipschitz only locally or
        depends on t (beyond a fixed moment t in [euler_picard_cauchy_vf]).

    STATUS: 32 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import CauchyReal SeriesConvergence FixedPoint.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessPicard.
From ToS Require Import process.ProcessODE.
(* files with declarations of the same names (euler_step, grid, qpow ...): no Import *)
From ToS Require analysis.Sqrt2Irrational.
From ToS Require analysis.PicardLindelof analysis.EulerTrajectoryGeneral.
From ToS Require process.ProcessExpProcess process.ProcessExpLadder.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The contraction without the boundedness premise                    *)
(*     ProcessPicard.euler_picard_contraction takes is_bounded_auto g M    *)
(*     (|g y| <= M for all y).  The premise can be dropped: the segment    *)
(*     [y0 - R, y0 + R] with R = |g y0| h / (1 - L h) is mapped into       *)
(*     itself.                                                             *)
(* ===================================================================== *)

Definition ep_radius (g : Q -> Q) (y0 h L : Q) : Q :=
  Qabs (g y0) * h / (1 - L * h).

Lemma ep_radius_eq : forall g y0 h L, L * h < 1 ->
  ep_radius g y0 h L * (1 - L * h) == Qabs (g y0) * h.
Proof. intros g y0 h L Hc. unfold ep_radius. field. lra. Qed.

Lemma ep_radius_nonneg : forall g y0 h L, 0 <= h -> L * h < 1 ->
  0 <= ep_radius g y0 h L.
Proof.
  intros g y0 h L Hh Hc. unfold ep_radius, Qdiv.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat; [ apply Qabs_nonneg | exact Hh ].
  - apply Qlt_le_weak, Qinv_lt_0_compat. lra.
Qed.

(** The step keeps the segment [y0 - R, y0 + R]. *)
Lemma euler_picard_interval_lip : forall g y0 h L y,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  y0 - ep_radius g y0 h L <= y -> y <= y0 + ep_radius g y0 h L ->
  y0 - ep_radius g y0 h L <= euler_picard g y0 h y /\
  euler_picard g y0 h y <= y0 + ep_radius g y0 h L.
Proof.
  intros g y0 h L y Hh [HL Hlip] Hc Hlo Hhi.
  pose proof (ep_radius_eq g y0 h L Hc) as HR.
  set (R := ep_radius g y0 h L) in *.
  assert (Hy : Qabs (y - y0) <= R) by (apply Qabs_Qle_condition; split; lra).
  pose proof (Hlip y y0) as Hg.
  assert (HLy : L * Qabs (y - y0) <= L * R)
    by (apply FixedPoint.Qmult_le_compat_l; [ exact Hy | lra ]).
  pose proof (Qabs_triangle (g y0) (g y - g y0)) as Htri.
  assert (Heq : g y0 + (g y - g y0) == g y) by ring.
  rewrite Heq in Htri.
  assert (Hg2 : Qabs (g y) <= Qabs (g y0) + L * R) by lra.
  assert (Hgh : Qabs (g y) * h <= (Qabs (g y0) + L * R) * h)
    by (apply Qmult_le_compat_r; [ exact Hg2 | exact Hh ]).
  assert (E1 : (Qabs (g y0) + L * R) * h == Qabs (g y0) * h + L * h * R) by ring.
  assert (E2 : R * (1 - L * h) == R - L * h * R) by ring.
  assert (Hb : Qabs (g y * h) <= R).
  { rewrite Qabs_Qmult, (Qabs_pos h Hh). lra. }
  apply Qabs_Qle_condition in Hb. destruct Hb as [Hb1 Hb2].
  unfold euler_picard. split; lra.
Qed.

(** The contraction under the Lipschitz condition and L h < 1 alone. *)
Theorem euler_picard_contraction_lip : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  is_contraction (euler_picard g y0 h)
    (y0 - ep_radius g y0 h L) (y0 + ep_radius g y0 h L) (L * h).
Proof.
  intros g y0 h L Hh Hlip Hc.
  unfold is_contraction. split; [ | split; [ | split ] ].
  - destruct Hlip as [HL _]. apply Qmult_le_0_compat; [ lra | exact Hh ].
  - exact Hc.
  - intros u Hu1 Hu2. apply euler_picard_interval_lip; assumption.
  - intros u v _ _ _ _. apply euler_picard_lip; assumption.
Qed.

(** The Cauchy process under the Lipschitz condition alone. *)
Theorem euler_picard_cauchy_lip : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  is_cauchy (euler_picard_process g y0 h).
Proof.
  intros g y0 h L Hh Hlip Hc.
  pose proof (ep_radius_nonneg g y0 h L Hh Hc) as HR.
  unfold euler_picard_process, euler_picard_iterate.
  apply iterate_is_cauchy
    with (a := y0 - ep_radius g y0 h L) (b := y0 + ep_radius g y0 h L) (c := L * h).
  - apply euler_picard_contraction_lip; assumption.
  - lra.
  - lra.
Qed.

(** The same for a right-hand side f(t, y) taken at a fixed moment t. *)
Corollary euler_picard_cauchy_vf : forall (f : VectorField) (t y0 h L : Q),
  0 <= h -> is_lipschitz f L -> L * h < 1 ->
  is_cauchy (euler_picard_process (f t) y0 h).
Proof.
  intros f t y0 h L Hh Hlip Hc.
  apply euler_picard_cauchy_lip with (L := L);
    [ exact Hh | apply vf_to_auto_lip; exact Hlip | exact Hc ].
Qed.

(** The linear right-hand side g(y) = y is Lipschitz, but does not satisfy
    the boundedness premise of the earlier theorem for any M. *)
Lemma id_lipschitz_auto : is_lipschitz_auto (fun y : Q => y) 1.
Proof. split; [ lra | intros y1 y2; lra ]. Qed.

Lemma id_not_bounded_auto : forall M, ~ is_bounded_auto (fun y : Q => y) M.
Proof.
  intros M [HM Hb]. specialize (Hb (M + 1)).
  rewrite Qabs_pos in Hb by lra. lra.
Qed.

(** The same for every linear right-hand side g(y) = a y, a <> 0. *)
Lemma linear_not_bounded_auto : forall a M : Q, ~ a == 0 ->
  ~ is_bounded_auto (fun y : Q => a * y) M.
Proof.
  intros a M Ha [HM Hb]. specialize (Hb ((M + 1) / a)). cbv beta in Hb.
  assert (E : a * ((M + 1) / a) == M + 1) by (field; exact Ha).
  rewrite E in Hb. rewrite Qabs_pos in Hb by lra. lra.
Qed.

(** The premises of the earlier theorem are satisfiable: a constant
    right-hand side satisfies both. *)
Lemma const_satisfies_both_premises : forall c : Q,
  is_lipschitz_auto (fun _ : Q => c) 1 /\ is_bounded_auto (fun _ : Q => c) (Qabs c + 1).
Proof.
  intro c. pose proof (Qabs_nonneg c) as Hc. split; split.
  - lra.
  - intros y1 y2. setoid_replace (c - c) with 0 by ring.
    change (Qabs 0) with 0. pose proof (Qabs_nonneg (y1 - y2)). lra.
  - lra.
  - intro y. lra.
Qed.

(** y' = y, y0 = 1, h = 1/2: the new theorem applies. *)
Example linear_scalar_iteration_cauchy :
  is_cauchy (euler_picard_process (fun y : Q => y) 1 (1#2)).
Proof.
  apply euler_picard_cauchy_lip with (L := 1).
  - rewrite Qle_alt. discriminate.
  - exact id_lipschitz_auto.
  - rewrite Qlt_alt. reflexivity.
Qed.

(* ===================================================================== *)
(*  2. What the scalar iteration tends to                                 *)
(*     A fixed point of y |-> y0 + g(y) h is a solution of                *)
(*     p = y0 + h g(p): the value of ONE implicit Euler step of the       *)
(*     length h.                                                          *)
(* ===================================================================== *)

Lemma euler_picard_fixed_iff : forall g y0 h p,
  euler_picard g y0 h p == p <-> p == y0 + h * g p.
Proof.
  intros g y0 h p. unfold euler_picard. split; intro H.
  - rewrite <- H at 1. ring.
  - rewrite H at 2. ring.
Qed.

Lemma euler_picard_iterate_succ : forall g y0 h n,
  euler_picard_iterate g y0 h (S n) = euler_picard g y0 h (euler_picard_iterate g y0 h n).
Proof. reflexivity. Qed.

(** If a rational fixed point exists, the iterates approach it
    geometrically (no condition L h < 1 is needed for the bound). *)
Lemma euler_picard_iterate_to_fixed : forall g y0 h L p,
  0 <= h -> is_lipschitz_auto g L -> p == y0 + h * g p ->
  forall n, Qabs (euler_picard_iterate g y0 h n - p) <= Qpow (L * h) n * Qabs (y0 - p).
Proof.
  intros g y0 h L p Hh Hlip Hp.
  assert (Hfix : euler_picard g y0 h p == p) by (apply euler_picard_fixed_iff; exact Hp).
  assert (Hc0 : 0 <= L * h)
    by (destruct Hlip as [HL _]; apply Qmult_le_0_compat; [ lra | exact Hh ]).
  induction n as [|n IH].
  - change (euler_picard_iterate g y0 h 0) with y0. cbn [Qpow]. lra.
  - rewrite euler_picard_iterate_succ.
    assert (E : euler_picard g y0 h (euler_picard_iterate g y0 h n) - p
                == euler_picard g y0 h (euler_picard_iterate g y0 h n)
                   - euler_picard g y0 h p)
      by (rewrite Hfix; reflexivity).
    rewrite E.
    eapply Qle_trans; [ apply (euler_picard_lip g y0 h L _ _ Hh Hlip) | ].
    cbn [Qpow].
    assert (E2 : L * h * Qpow (L * h) n * Qabs (y0 - p)
                 == (L * h) * (Qpow (L * h) n * Qabs (y0 - p))) by ring.
    rewrite E2.
    apply FixedPoint.Qmult_le_compat_l; [ exact IH | exact Hc0 ].
Qed.

Theorem euler_picard_iterate_limit : forall g y0 h L p,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 -> p == y0 + h * g p ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    Qabs (euler_picard_iterate g y0 h n - p) < eps.
Proof.
  intros g y0 h L p Hh Hlip Hc Hp eps Heps.
  assert (Hc0 : 0 <= L * h)
    by (destruct Hlip as [HL _]; apply Qmult_le_0_compat; [ lra | exact Hh ]).
  pose proof (Qabs_nonneg (y0 - p)) as HK.
  assert (Ht : 0 < eps / (Qabs (y0 - p) + 1)) by (apply Qlt_shift_div_l; lra).
  destruct (Qpow_limit_zero (L * h) Hc0 Hc _ Ht) as [N HN].
  exists N. intros n Hn.
  eapply Qle_lt_trans; [ apply (euler_picard_iterate_to_fixed g y0 h L p Hh Hlip Hp n) | ].
  pose proof (HN n Hn) as HP.
  assert (HP0 : 0 <= Qpow (L * h) n) by (apply SeriesConvergence.Qpow_nonneg; exact Hc0).
  assert (HPK : Qpow (L * h) n * (Qabs (y0 - p) + 1) < eps).
  { assert (H1 : Qpow (L * h) n * (Qabs (y0 - p) + 1)
                 < eps / (Qabs (y0 - p) + 1) * (Qabs (y0 - p) + 1))
      by (apply Qmult_lt_compat_r; [ lra | exact HP ]).
    assert (H2 : eps / (Qabs (y0 - p) + 1) * (Qabs (y0 - p) + 1) == eps) by (field; lra).
    lra. }
  assert (Hle : Qpow (L * h) n * Qabs (y0 - p)
                <= Qpow (L * h) n * (Qabs (y0 - p) + 1))
    by (apply FixedPoint.Qmult_le_compat_l; [ lra | exact HP0 ]).
  lra.
Qed.

(** y' = y, y0 = 1, h = 1/2: the iterates are 2 - (1/2)^n. *)
Lemma linear_scalar_iteration_value : forall n,
  euler_picard_iterate (fun y : Q => y) 1 (1#2) n == 2 - Qpow (1#2) n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite euler_picard_iterate_succ. unfold euler_picard.
    rewrite IH. cbn [Qpow]. ring.
Qed.

Lemma linear_scalar_fixed_point : euler_picard (fun y : Q => y) 1 (1#2) 2 == 2.
Proof. reflexivity. Qed.

Theorem linear_scalar_iteration_limit : forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (euler_picard_iterate (fun y : Q => y) 1 (1#2) n - 2) < eps.
Proof.
  intros eps Heps.
  assert (H0 : 0 <= 1#2) by (rewrite Qle_alt; discriminate).
  assert (H1 : 1#2 < 1) by (rewrite Qlt_alt; reflexivity).
  destruct (Qpow_limit_zero (1#2) H0 H1 eps Heps) as [N HN].
  exists N. intros n Hn.
  rewrite linear_scalar_iteration_value.
  setoid_replace (2 - Qpow (1#2) n - 2) with (- Qpow (1#2) n) by ring.
  rewrite Qabs_opp, Qabs_pos by (apply SeriesConvergence.Qpow_nonneg; exact H0).
  apply HN; exact Hn.
Qed.

(** The explicit Euler method for the same problem: one step 1/2 and two
    steps 1/4 (the moment t = 1/2). *)
Lemma explicit_euler_one_step :
  euler_method (fun _ y : Q => y) 0 1 (1#2) 1 == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma explicit_euler_two_half_steps :
  euler_method (fun _ y : Q => y) 0 1 (1#4) 2 == 25#16.
Proof. vm_compute. reflexivity. Qed.

(** The Euler polygon of Chapter 8.2 with 2N steps on [0, 1], read at the
    node N (the moment t = 1/2): (1 + 1/(2N))^N. *)
Lemma euler_half_closed : forall N : nat,
  PicardLindelof.euler_traj PicardLindelof.f_identity 1 (2 * N) N
  == ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N.
Proof.
  intro N. rewrite EulerTrajectoryGeneral.euler_traj_exp_closed. ring.
Qed.

(** Every such polygon is below 7/4 at t = 1/2: its square is the stage
    (1 + 1/(2N))^(2N) of the e-ladder, which is below 3. *)
Theorem euler_half_below : forall N : nat, (0 < N)%nat ->
  PicardLindelof.euler_traj PicardLindelof.f_identity 1 (2 * N) N < 7 # 4.
Proof.
  intros N HN. rewrite euler_half_closed.
  assert (Hsq : ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N
                * ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N
                == ProcessExpProcess.exp1_process (2 * N - 1)).
  { rewrite <- ProcessExpLadder.qpow_add. unfold ProcessExpProcess.exp1_process.
    replace (S (2 * N - 1)) with (2 * N)%nat by lia.
    replace (N + N)%nat with (2 * N)%nat by lia. reflexivity. }
  pose proof (ProcessExpLadder.exp1_upper (2 * N - 1)) as Hup.
  destruct (Qlt_le_dec
              (ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N) (7 # 4))
    as [Hlt | Hge]; [ exact Hlt | exfalso ].
  assert (H1 : 49 # 16
               <= (7 # 4) * ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N)
    by lra.
  assert (H2 : (7 # 4) * ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N
               <= ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N
                  * ProcessExpProcess.qpow (1 + 1 / inject_Z (Z.of_nat (2 * N))) N)
    by (apply Qmult_le_compat_r; lra).
  lra.
Qed.

(** The limit of the scalar iteration (2) is not the limit of the Euler
    stages at the same moment: all of them stay below 7/4. *)
Theorem scalar_limit_apart_from_euler_stages :
  (forall eps, 0 < eps -> exists K, forall n, (K <= n)%nat ->
     Qabs (euler_picard_iterate (fun y : Q => y) 1 (1#2) n - 2) < eps) /\
  (forall N : nat, (0 < N)%nat ->
     PicardLindelof.euler_traj PicardLindelof.f_identity 1 (2 * N) N < 7 # 4).
Proof. split; [ exact linear_scalar_iteration_limit | exact euler_half_below ]. Qed.

(* ===================================================================== *)
(*  3. An error process tied to the solution process                      *)
(*     In ProcessODE.ode_is_process only non-negativity is required of    *)
(*     err_proc.  Here the error bounds the distance from the stage n to  *)
(*     every later stage and tends to zero.                               *)
(* ===================================================================== *)

Definition ep_err (g : Q -> Q) (y0 h L : Q) : RealProcess :=
  fun n => Qabs (g y0 * h) * Qpow (L * h) n / (1 - L * h).

Lemma ep_err_nonneg : forall g y0 h L n,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 -> 0 <= ep_err g y0 h L n.
Proof.
  intros g y0 h L n Hh [HL _] Hc. unfold ep_err, Qdiv.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat; [ apply Qabs_nonneg | ].
    apply SeriesConvergence.Qpow_nonneg. apply Qmult_le_0_compat; [ lra | exact Hh ].
  - apply Qlt_le_weak, Qinv_lt_0_compat. lra.
Qed.

Theorem euler_picard_error_process : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  forall n m, (n <= m)%nat ->
    Qabs (euler_picard_iterate g y0 h m - euler_picard_iterate g y0 h n)
      <= ep_err g y0 h L n.
Proof.
  intros g y0 h L Hh Hlip Hc n m Hnm.
  pose proof (ep_radius_nonneg g y0 h L Hh Hc) as HR.
  pose proof (euler_picard_contraction_lip g y0 h L Hh Hlip Hc) as Hcon.
  assert (Ha : y0 - ep_radius g y0 h L <= y0) by lra.
  assert (Hb : y0 <= y0 + ep_radius g y0 h L) by lra.
  pose proof (iterate_diff_bound _ _ _ _ y0 Hcon Ha Hb n m Hnm) as Htel.
  assert (Hd : euler_picard g y0 h y0 - y0 == g y0 * h) by (unfold euler_picard; ring).
  rewrite Hd in Htel.
  assert (Hc0 : 0 <= L * h) by (destruct Hcon as [H _]; exact H).
  assert (Hpm : 0 <= Qpow (L * h) m) by (apply SeriesConvergence.Qpow_nonneg; exact Hc0).
  assert (Hdm : 0 <= Qabs (g y0 * h) * Qpow (L * h) m)
    by (apply Qmult_le_0_compat; [ apply Qabs_nonneg | exact Hpm ]).
  unfold euler_picard_iterate, ep_err.
  apply Qle_shift_div_l; [ lra | ].
  lra.
Qed.

Theorem ep_err_vanishes : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> ep_err g y0 h L n < eps.
Proof.
  intros g y0 h L Hh [HL Hlip] Hc eps Heps.
  assert (Hc0 : 0 <= L * h) by (apply Qmult_le_0_compat; [ lra | exact Hh ]).
  set (K := Qabs (g y0 * h) / (1 - L * h)).
  assert (HK : 0 <= K).
  { unfold K, Qdiv. apply Qmult_le_0_compat; [ apply Qabs_nonneg | ].
    apply Qlt_le_weak, Qinv_lt_0_compat. lra. }
  assert (Ht : 0 < eps / (K + 1)) by (apply Qlt_shift_div_l; lra).
  destruct (Qpow_limit_zero (L * h) Hc0 Hc _ Ht) as [N HN].
  exists N. intros n Hn.
  assert (E : ep_err g y0 h L n == K * Qpow (L * h) n)
    by (unfold ep_err, K; field; lra).
  rewrite E.
  pose proof (HN n Hn) as HP.
  assert (HP0 : 0 <= Qpow (L * h) n) by (apply SeriesConvergence.Qpow_nonneg; exact Hc0).
  assert (HPK : Qpow (L * h) n * (K + 1) < eps).
  { assert (H1 : Qpow (L * h) n * (K + 1) < eps / (K + 1) * (K + 1))
      by (apply Qmult_lt_compat_r; [ lra | exact HP ]).
    assert (H2 : eps / (K + 1) * (K + 1) == eps) by (field; lra).
    lra. }
  lra.
Qed.

(** The strengthening of ProcessODE.ode_is_process: the error process does
    bound the solution process; the boundedness premise is dropped. *)
Theorem ode_is_process_err : forall g y0 h L,
  is_lipschitz_auto g L -> 0 <= h -> L * h < 1 ->
  exists sol_proc err_proc : RealProcess,
    (forall n, sol_proc n == euler_picard_iterate g y0 h n) /\
    (forall n m, (n <= m)%nat -> Qabs (sol_proc m - sol_proc n) <= err_proc n) /\
    (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> err_proc n < eps) /\
    is_Cauchy sol_proc.
Proof.
  intros g y0 h L Hlip Hh Hc.
  exists (euler_picard_process g y0 h), (ep_err g y0 h L).
  split; [ intro n; reflexivity | ].
  split; [ intros n m Hnm; apply euler_picard_error_process; assumption | ].
  split; [ apply ep_err_vanishes; assumption | ].
  exact (euler_picard_cauchy_lip g y0 h L Hh Hlip Hc).
Qed.

(** The conclusion of ProcessODE.ode_is_process holds with the zero "error
    process" as well: its middle conjunct carries no information about the
    solution process. *)
Lemma ode_is_process_with_zero_err : forall g y0 h L M,
  is_lipschitz_auto g L -> is_bounded_auto g M -> 0 < h -> L * h < 1 ->
  let err_proc : RealProcess := fun _ => 0 in
  exists sol_proc : RealProcess,
    (forall n, sol_proc n == euler_picard_iterate g y0 h n) /\
    (forall n, 0 <= err_proc n) /\
    is_Cauchy sol_proc.
Proof.
  intros g y0 h L M Hlip Hbnd Hh Hc err_proc.
  exists (euler_picard_process g y0 h).
  split; [ intro n; reflexivity | ].
  split; [ intro n; unfold err_proc; lra | ].
  apply euler_picard_is_Cauchy with (L := L) (M := M); auto; lra.
Qed.

(* ===================================================================== *)
(*  4. A contraction of a segment of rationals without a rational fixed   *)
(*     point: x |-> x/2 + 1/x on [1, 2].  The iterates form a Cauchy      *)
(*     process, while "a fixed point exists" is false over Q.             *)
(* ===================================================================== *)

Definition newton2 (x : Q) : Q := (1#2) * x + / x.

Lemma inv_bounds_1_2 : forall x, 1 <= x -> x <= 2 -> (1#2) <= / x /\ / x <= 1.
Proof.
  intros x H1 H2.
  assert (Hu : 0 < / x) by (apply Qinv_lt_0_compat; lra).
  assert (E : x * / x == 1) by (apply Qmult_inv_r; lra).
  split.
  - assert (H : x * / x <= 2 * / x) by (apply Qmult_le_compat_r; lra). lra.
  - assert (H : 1 * / x <= x * / x) by (apply Qmult_le_compat_r; lra). lra.
Qed.

Lemma newton2_contraction : is_contraction newton2 1 2 (1#2).
Proof.
  unfold is_contraction. split; [ | split; [ | split ] ].
  - rewrite Qle_alt. discriminate.
  - rewrite Qlt_alt. reflexivity.
  - intros x H1 H2. destruct (inv_bounds_1_2 x H1 H2) as [Ha Hb].
    unfold newton2. split; lra.
  - intros x y Hx1 Hx2 Hy1 Hy2.
    destruct (inv_bounds_1_2 x Hx1 Hx2) as [Hax Hbx].
    destruct (inv_bounds_1_2 y Hy1 Hy2) as [Hay Hby].
    assert (E : newton2 x - newton2 y == (x - y) * ((1#2) - / x * / y)).
    { unfold newton2. field. split; lra. }
    rewrite E, Qabs_Qmult.
    rewrite (Qmult_comm (1#2)).
    apply FixedPoint.Qmult_le_compat_l; [ | apply Qabs_nonneg ].
    assert (P1 : / x * / y <= 1 * / y) by (apply Qmult_le_compat_r; lra).
    assert (P2 : (1#2) * / y <= / x * / y) by (apply Qmult_le_compat_r; lra).
    apply Qabs_Qle_condition. split; lra.
Qed.

Theorem newton2_no_rational_fixed_point : forall p : Q,
  1 <= p -> p <= 2 -> ~ newton2 p == p.
Proof.
  intros p H1 H2 Hfix. unfold newton2 in Hfix.
  apply (Sqrt2Irrational.no_rational_sqrt2 p).
  assert (E : p * / p == 1) by (apply Qmult_inv_r; lra).
  assert (E2 : / p == (1#2) * p) by lra.
  rewrite E2 in E. lra.
Qed.

Theorem contraction_without_rational_fixed_point :
  is_contraction newton2 1 2 (1#2) /\
  is_cauchy (fun n => iterate newton2 1 n) /\
  (forall p : Q, 1 <= p -> p <= 2 -> ~ newton2 p == p).
Proof.
  split; [ exact newton2_contraction | ].
  split; [ | exact newton2_no_rational_fixed_point ].
  apply iterate_is_cauchy with (a := 1) (b := 2) (c := 1#2).
  - exact newton2_contraction.
  - apply Qle_refl.
  - rewrite Qle_alt. discriminate.
Qed.
