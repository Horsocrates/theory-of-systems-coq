(** * ProcessEulerRefinement.v -- Euler polygons under refinement of the grid: the doubling process is Cauchy, as a ToS System

    Elements: the values [euler (fun _ => g) d y0 k] of the Euler polygon of
              an autonomous equation y' = g(y) (ProcessODEStability.v); the
              steps d = T / 2^j and the numbers of steps 2^j; the natural
              number j (level of refinement).
    Roles:    j -- role-resolution: the level j is the grid of 2^j steps on
              the interval of length T; [euler_dyadic T j] -- role-stage: the
              value of the polygon of the level j at the moment T;
              [refine_bound d k] -- role-defect between the polygons with the
              steps 2d and d at one and the same moment;
              [growth_cap (L * T) k0] -- role-ceiling of the growth factor,
              one for all levels; K / 2^n -- role-modulus.
    Rules:    one step of the coarse grid against two steps of the fine one:
                e_(k+1) <= (1 + 2 L d) e_k + L M d^2,   e_0 = 0,
              for a right-hand side g with |g| <= M and the Lipschitz
              constant L.

    Proved (no axioms):
      - [euler_refine_bound]: the polygon with the step 2d at the node k and
        the polygon with the step d at the node 2k (one and the same moment)
        differ by at most [refine_bound d k]; [refine_bound_closed] -- its
        closed form;
      - [euler_dyadic_step]: the levels j and j + 1 differ at the moment T by
        at most K / 2^j, K = (L M T^2 / 4) * growth_cap (L T) k0;
      - [euler_dyadic_modulus], [euler_dyadic_modulus_tail]: for n <= m the
        levels m and n differ by at most 2 K / 2^n;
      - [euler_dyadic_is_Cauchy]: for every T >= 0 the values of the Euler
        polygons at the moment T under doubling of the grid form a Cauchy
        process;
      - [euler_traj_eq_euler], [euler_traj_dyadic_is_Cauchy]: the same for
        [euler_traj] of PicardLindelof.v at the moment t = 1;
      - [clamp1_dyadic_is_Cauchy]: the premises hold for a right-hand side
        with L = 1 that is not constant (the identity cut at -1 and 1).

    P4 diagnostic: every stage is a rational number computed by a finite
      recursion. The Cauchy property is a property of the process (an
      explicit level for every eps); no limit of the process is built, and
      over Q there may be none.

    NOT claimed:
      - a limit function of the polygons, or that such a limit solves the
        equation;
      - anything for a right-hand side that depends on t, is unbounded
        (y' = y is not covered: see ProcessExpLadder.v for it) or is
        Lipschitz only locally;
      - the rate for refinements other than doubling;
      - convergence uniform in the moment of time.

    STATUS: 31 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessExpProcess.
From ToS Require Import process.ProcessExpLadder.
(* files with declarations of the same names (euler_step, grid, qmul_le_l ...): no Import *)
From ToS Require analysis.PicardLindelof process.ProcessODEStability.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. Helpers                                                            *)
(* ===================================================================== *)

Lemma Qle_of_Qeq : forall a b : Q, a == b -> a <= b.
Proof. intros a b E. rewrite E. apply Qle_refl. Qed.

Lemma abs_scale_bound : forall s x c : Q, 0 <= s -> Qabs x <= c -> Qabs (s * x) <= s * c.
Proof.
  intros s x c Hs Hx. rewrite Qabs_Qmult, (Qabs_pos s Hs).
  apply qmul_le_l; assumption.
Qed.

Lemma qpow_ge_1 : forall (b : Q) (n : nat), 1 <= b -> 1 <= qpow b n.
Proof.
  intros b n Hb. induction n as [|n IH]; cbn [qpow]; [ apply Qle_refl | ].
  apply Qle_trans with (1 * qpow b n); [ lra | ].
  apply Qmult_le_compat_r; [ exact Hb | lra ].
Qed.

(** Powers of one half. *)
Definition half_pow (j : nat) : Q := qpow (1 # 2) j.

Lemma half_pow_S' : forall j, half_pow (S j) == (1 # 2) * half_pow j.
Proof. intro j. unfold half_pow. cbn [qpow]. reflexivity. Qed.

Lemma half_pow_pos : forall j, 0 < half_pow j.
Proof. intro j. unfold half_pow. apply qpow_pos. reflexivity. Qed.

Lemma half_pow_antitone : forall n m, (n <= m)%nat -> half_pow m <= half_pow n.
Proof.
  intros n m H. induction H as [|m H IH].
  - apply Qle_refl.
  - rewrite (half_pow_S' m). pose proof (half_pow_pos m). lra.
Qed.

(** 2^j * (1/2)^j = 1. *)
Lemma pow2_half : forall j, inject_Z (Z.of_nat (2 ^ j)) * half_pow j == 1.
Proof.
  intro j. induction j as [|j IH].
  - vm_compute. reflexivity.
  - rewrite (half_pow_S' j), Nat.pow_succ_r', Nat2Z.inj_mul, inject_Z_mult.
    change (inject_Z (Z.of_nat 2)) with 2.
    set (n := inject_Z (Z.of_nat (2 ^ j))) in *. set (p := half_pow j) in *.
    assert (E : 2 * n * ((1 # 2) * p) == n * p) by ring.
    rewrite E. exact IH.
Qed.

(** (1/2)^J gets below any eps, with any factor in front. *)
Lemma half_pow_vanish : forall A eps : Q, 0 < eps ->
  exists J : nat, A * half_pow J < eps.
Proof.
  intros A eps Heps.
  destruct (ladder_archimedean A eps Heps) as [K HK]. exists K.
  pose proof (pow2_half K) as Hp. pose proof (half_pow_pos K) as Hh.
  assert (HKle : inject_Z (Z.of_nat K) <= inject_Z (Z.of_nat (2 ^ K))).
  { apply inj_le. apply Nat.lt_le_incl, Nat.pow_gt_lin_r. lia. }
  set (n := inject_Z (Z.of_nat (2 ^ K))) in *. set (p := half_pow K) in *.
  assert (H1 : A < n * eps).
  { eapply Qlt_le_trans; [ exact HK | apply Qmult_le_compat_r; lra ]. }
  assert (H2 : A * p < n * eps * p) by (apply Qmult_lt_compat_r; assumption).
  assert (E : n * eps * p == eps * (n * p)) by ring.
  rewrite E, Hp in H2.
  assert (E2 : eps * 1 == eps) by ring. rewrite E2 in H2. exact H2.
Qed.

(** The ceiling of the growth factor (1 + s/n)^n, one for all n
    (see expt_bounded in ProcessExpLadder.v). *)
Definition growth_cap (s : Q) (k0 : nat) : Q :=
  1 / qpow (1 - s / inject_Z (Z.of_nat (S k0))) (S k0).

Lemma growth_cap_ge_1 : forall (s : Q) (k0 : nat),
  0 <= s -> s < inject_Z (Z.of_nat (S k0)) -> 1 <= growth_cap s k0.
Proof.
  intros s k0 Hs Hk0. unfold growth_cap.
  pose proof (expt_bounded s 0 k0 Hs Hk0) as H1.
  pose proof (expt_lower s 0 Hs) as H2. lra.
Qed.

(* ===================================================================== *)
(*  1. Three definitions of the Euler polygon: a bridge                   *)
(* ===================================================================== *)

(** [euler_traj] of PicardLindelof.v (step 1/N, nodes k/N) is [euler] of
    ProcessODEStability.v with the step 1/N -- for a right-hand side that
    respects the equality of rationals in both arguments. *)
Theorem euler_traj_eq_euler : forall (f : Q -> Q -> Q) (y0 : Q) (N k : nat),
  (forall t1 t2 y1 y2, t1 == t2 -> y1 == y2 -> f t1 y1 == f t2 y2) ->
  PicardLindelof.euler_traj f y0 N k
  == ProcessODEStability.euler f (1 / inject_Z (Z.of_nat N)) y0 k.
Proof.
  intros f y0 N k Hc. induction k as [|k IH].
  - cbn [PicardLindelof.euler_traj ProcessODEStability.euler]. reflexivity.
  - cbn [PicardLindelof.euler_traj ProcessODEStability.euler].
    unfold PicardLindelof.euler_step.
    apply Qplus_comp; [ exact IH | ].
    apply Qmult_comp; [ reflexivity | ].
    apply Hc; [ | exact IH ].
    unfold PicardLindelof.grid, ProcessODEStability.tg, Qdiv. ring.
Qed.

(* ===================================================================== *)
(*  2. One step of the coarse grid against two steps of the fine one      *)
(* ===================================================================== *)

Section Refinement.

Variable g : Q -> Q.                 (* y' = g(y): an autonomous right-hand side *)
Variables L M : Q.
Hypothesis HL : 0 <= L.
Hypothesis Hlip : forall y1 y2, Qabs (g y1 - g y2) <= L * Qabs (y1 - y2).
Hypothesis Hbd : forall y, Qabs (g y) <= M.
Variable y0 : Q.

Local Notation eul := (ProcessODEStability.euler (fun _ : Q => g)).

Lemma bound_nonneg : 0 <= M.
Proof. eapply Qle_trans; [ apply Qabs_nonneg | apply (Hbd 0) ]. Qed.

Lemma g_compat : forall a b : Q, a == b -> g a == g b.
Proof.
  intros a b E. pose proof (Hlip a b) as H.
  assert (E0 : Qabs (a - b) == 0).
  { assert (Ez : a - b == 0) by lra. rewrite Ez. reflexivity. }
  rewrite E0 in H.
  assert (H' : Qabs (g a - g b) <= 0) by lra.
  apply Qabs_Qle_condition in H'. lra.
Qed.

(** The polygon respects the equality of rationals in the step. *)
Lemma eul_step_wd : forall (d1 d2 : Q) (k : nat),
  d1 == d2 -> eul d1 y0 k == eul d2 y0 k.
Proof.
  intros d1 d2 k E. induction k as [|k IH].
  - reflexivity.
  - cbn [ProcessODEStability.euler]. cbv beta.
    apply Qplus_comp; [ exact IH | ].
    apply Qmult_comp; [ exact E | ].
    apply g_compat. exact IH.
Qed.

Lemma refine_step : forall (d a b : Q), 0 <= d ->
  Qabs ((a + (2 * d) * g a) - ((b + d * g b) + d * g (b + d * g b)))
  <= (1 + 2 * L * d) * Qabs (a - b) + L * M * d * d.
Proof.
  intros d a b Hd.
  set (b1 := b + d * g b).
  assert (H1 : Qabs (g a - g b) <= L * Qabs (a - b)) by apply Hlip.
  assert (H3 : Qabs (a - b1) <= Qabs (a - b) + d * M).
  { unfold b1.
    setoid_replace (a - (b + d * g b)) with ((a - b) + d * (- g b)) by ring.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    apply Qplus_le_compat; [ apply Qle_refl | ].
    apply abs_scale_bound; [ exact Hd | ]. rewrite Qabs_opp. apply Hbd. }
  assert (H2 : Qabs (g a - g b1) <= L * (Qabs (a - b) + d * M)).
  { eapply Qle_trans; [ apply Hlip | ].
    apply qmul_le_l; [ exact HL | exact H3 ]. }
  setoid_replace (a + 2 * d * g a - (b1 + d * g b1))
    with ((a - b) + (d * (g a - g b) + d * (g a - g b1))) by (unfold b1; ring).
  eapply Qle_trans; [ apply Qabs_triangle | ].
  eapply Qle_trans;
    [ apply Qplus_le_compat; [ apply Qle_refl | apply Qabs_triangle ] | ].
  pose proof (abs_scale_bound d _ _ Hd H1) as K1.
  pose proof (abs_scale_bound d _ _ Hd H2) as K2.
  lra.
Qed.

(** The bound of the defect: e_0 = 0, e_(k+1) = (1 + 2 L d) e_k + L M d^2. *)
Fixpoint refine_bound (d : Q) (k : nat) : Q :=
  match k with
  | O => 0
  | S k' => (1 + 2 * L * d) * refine_bound d k' + L * M * d * d
  end.

(** The polygon with the step 2d at the node k against the polygon with the
    step d at the node 2k (one and the same moment t = 2 d k). *)
Theorem euler_refine_bound : forall (d : Q) (k : nat), 0 <= d ->
  Qabs (eul (2 * d) y0 k - eul d y0 (2 * k)) <= refine_bound d k.
Proof.
  intros d k Hd. induction k as [|k IH].
  - cbn [Nat.mul ProcessODEStability.euler refine_bound].
    assert (Ez : y0 - y0 == 0) by ring. rewrite Ez. apply Qle_refl.
  - replace (2 * S k)%nat with (S (S (2 * k))) by lia.
    cbn [ProcessODEStability.euler refine_bound].
    eapply Qle_trans; [ exact (refine_step d _ _ Hd) | ].
    apply Qplus_le_compat; [ | apply Qle_refl ].
    apply qmul_le_l; [ | exact IH ].
    assert (Hld : 0 <= L * d) by (apply Qmult_le_0_compat; assumption). lra.
Qed.

(** The closed form of the bound (without division). *)
Lemma refine_bound_closed : forall (d : Q) (k : nat),
  2 * L * d * refine_bound d k
  == L * M * d * d * (qpow (1 + 2 * L * d) k - 1).
Proof.
  intros d k. induction k as [|k IH]; cbn [refine_bound qpow].
  - ring.
  - assert (E : 2 * L * d * ((1 + 2 * L * d) * refine_bound d k + L * M * d * d)
                == (1 + 2 * L * d) * (2 * L * d * refine_bound d k)
                   + 2 * L * d * (L * M * d * d)) by ring.
    rewrite E, IH. ring.
Qed.

(** A bound without division: e_k <= k * L M d^2 * (1 + 2 L d)^k. *)
Lemma refine_bound_le : forall (d : Q) (k : nat), 0 <= d ->
  refine_bound d k
  <= inject_Z (Z.of_nat k) * (L * M * d * d) * qpow (1 + 2 * L * d) k.
Proof.
  intros d k Hd. pose proof bound_nonneg as HM.
  assert (Hc : 0 <= L * M * d * d) by (repeat apply Qmult_le_0_compat; assumption).
  assert (Hq1 : 1 <= 1 + 2 * L * d).
  { assert (0 <= L * d) by (apply Qmult_le_0_compat; assumption). lra. }
  induction k as [|k IH].
  - cbn [refine_bound qpow]. change (inject_Z (Z.of_nat 0)) with 0.
    apply Qle_of_Qeq. ring.
  - cbn [refine_bound qpow]. rewrite (inj_S k).
    pose proof (inj_nonneg k) as Hm.
    pose proof (qpow_ge_1 (1 + 2 * L * d) k Hq1) as HP1.
    set (q := 1 + 2 * L * d) in *. set (c := L * M * d * d) in *.
    set (m := inject_Z (Z.of_nat k)) in *. set (P := qpow q k) in *.
    set (R := refine_bound d k) in *.
    assert (H1 : q * R <= q * (m * c * P)) by (apply qmul_le_l; [ lra | exact IH ]).
    assert (HqP : 1 <= q * P).
    { apply Qle_trans with (1 * P); [ lra | apply Qmult_le_compat_r; lra ]. }
    assert (H2 : c * 1 <= c * (q * P)) by (apply qmul_le_l; assumption).
    assert (E : (m + 1) * c * (q * P) == q * (m * c * P) + c * (q * P)) by ring.
    rewrite E. lra.
Qed.

(* ===================================================================== *)
(*  3. Doubling of the grid on an interval of length T                    *)
(* ===================================================================== *)

(** The value of the Euler polygon at the moment T on the grid of 2^j
    steps (the step is T / 2^j). *)
Definition euler_dyadic (T : Q) (j : nat) : Q :=
  eul (T * half_pow j) y0 (2 ^ j).

Lemma euler_dyadic_step_raw : forall T j, 0 <= T ->
  Qabs (euler_dyadic T j - euler_dyadic T (S j))
  <= refine_bound (T * half_pow (S j)) (2 ^ j).
Proof.
  intros T j HT. unfold euler_dyadic.
  pose proof (half_pow_pos (S j)) as HpS.
  set (d := T * half_pow (S j)).
  assert (Hd : 0 <= d) by (unfold d; apply Qmult_le_0_compat; lra).
  assert (E1 : eul (T * half_pow j) y0 (2 ^ j) == eul (2 * d) y0 (2 ^ j)).
  { apply eul_step_wd. unfold d. rewrite (half_pow_S' j). ring. }
  rewrite E1, Nat.pow_succ_r'.
  apply euler_refine_bound. exact Hd.
Qed.

(** The growth factor of the level j is under the ceiling. *)
Lemma dyadic_growth_bound : forall T j k0, 0 <= T ->
  L * T < inject_Z (Z.of_nat (S k0)) ->
  qpow (1 + 2 * L * (T * half_pow (S j))) (2 ^ j) <= growth_cap (L * T) k0.
Proof.
  intros T j k0 HT Hk0.
  assert (Hs : 0 <= L * T) by (apply Qmult_le_0_compat; assumption).
  pose proof (pow2_half j) as Hp.
  assert (Hpos : (0 < 2 ^ j)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  remember (2 ^ j)%nat as n eqn:En in *. destruct n as [|m]; [ lia | ].
  pose proof (inj_pos (S m) ltac:(lia)) as Hdn.
  set (dn := inject_Z (Z.of_nat (S m))) in *.
  assert (Ehp : half_pow j == 1 / dn).
  { assert (X : half_pow j == (dn * half_pow j) / dn) by (field; lra).
    rewrite Hp in X. exact X. }
  assert (Ebase : 1 + 2 * L * (T * half_pow (S j)) == 1 + L * T / dn).
  { rewrite (half_pow_S' j), Ehp. field. lra. }
  rewrite (qpow_wd _ _ (S m) Ebase).
  unfold growth_cap. exact (expt_bounded (L * T) m k0 Hs Hk0).
Qed.

Lemma dyadic_const_nonneg : forall T k0, 0 <= T ->
  L * T < inject_Z (Z.of_nat (S k0)) ->
  0 <= (L * M * T * T / 4) * growth_cap (L * T) k0.
Proof.
  intros T k0 HT Hk0. pose proof bound_nonneg as HM.
  assert (Hs : 0 <= L * T) by (apply Qmult_le_0_compat; assumption).
  pose proof (growth_cap_ge_1 (L * T) k0 Hs Hk0) as HG.
  apply Qmult_le_0_compat; [ | lra ].
  assert (E : L * M * T * T / 4 == (1 # 4) * (L * M * T * T)) by field.
  rewrite E. apply Qmult_le_0_compat; [ unfold Qle; simpl; lia | ].
  repeat apply Qmult_le_0_compat; assumption.
Qed.

(** The levels j and j + 1 differ at the moment T by at most K / 2^j. *)
Lemma euler_dyadic_step : forall T j k0, 0 <= T ->
  L * T < inject_Z (Z.of_nat (S k0)) ->
  Qabs (euler_dyadic T j - euler_dyadic T (S j))
  <= (L * M * T * T / 4) * growth_cap (L * T) k0 * half_pow j.
Proof.
  intros T j k0 HT Hk0.
  eapply Qle_trans; [ apply euler_dyadic_step_raw; exact HT | ].
  pose proof (dyadic_growth_bound T j k0 HT Hk0) as HB.
  pose proof (pow2_half j) as Hp.
  pose proof (half_pow_pos (S j)) as HpS.
  pose proof bound_nonneg as HM.
  pose proof (inj_nonneg (2 ^ j)) as Hn.
  set (d := T * half_pow (S j)) in *.
  assert (Hd : 0 <= d) by (unfold d; apply Qmult_le_0_compat; lra).
  eapply Qle_trans; [ apply (refine_bound_le d (2 ^ j) Hd) | ].
  set (n := inject_Z (Z.of_nat (2 ^ j))) in *.
  set (B := growth_cap (L * T) k0) in *.
  assert (Hc0 : 0 <= n * (L * M * d * d)).
  { assert (HLM : 0 <= L * M) by (apply Qmult_le_0_compat; assumption).
    apply Qmult_le_0_compat; [ exact Hn | ].
    apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; assumption | exact Hd ]. }
  assert (Hcoef : n * (L * M * d * d) == (L * M * T * T / 4) * half_pow j).
  { unfold d. rewrite (half_pow_S' j).
    assert (E : n * (L * M * (T * ((1 # 2) * half_pow j)) * (T * ((1 # 2) * half_pow j)))
                == (L * M * T * T / 4) * half_pow j * (n * half_pow j)) by field.
    rewrite E, Hp. ring. }
  apply Qle_trans with (n * (L * M * d * d) * B).
  - apply qmul_le_l; [ exact Hc0 | exact HB ].
  - rewrite Hcoef. apply Qle_of_Qeq. ring.
Qed.

(** For n <= m the levels m and n differ by at most 2 K (1/2^n - 1/2^m). *)
Theorem euler_dyadic_modulus : forall T k0, 0 <= T ->
  L * T < inject_Z (Z.of_nat (S k0)) ->
  forall n m, (n <= m)%nat ->
  Qabs (euler_dyadic T m - euler_dyadic T n)
  <= 2 * ((L * M * T * T / 4) * growth_cap (L * T) k0) * (half_pow n - half_pow m).
Proof.
  intros T k0 HT Hk0 n m.
  set (K := (L * M * T * T / 4) * growth_cap (L * T) k0).
  induction m as [|m IH]; intro Hnm.
  - assert (n = 0%nat) by lia. subst n.
    assert (E : Qabs (euler_dyadic T 0 - euler_dyadic T 0) == 0).
    { assert (Ez : euler_dyadic T 0 - euler_dyadic T 0 == 0) by ring.
      rewrite Ez. reflexivity. }
    rewrite E. apply Qle_of_Qeq. ring.
  - destruct (Nat.eq_dec n (S m)) as [En|En].
    + subst n.
      assert (E : Qabs (euler_dyadic T (S m) - euler_dyadic T (S m)) == 0).
      { assert (Ez : euler_dyadic T (S m) - euler_dyadic T (S m) == 0) by ring.
        rewrite Ez. reflexivity. }
      rewrite E. apply Qle_of_Qeq. ring.
    + assert (Hnm' : (n <= m)%nat) by lia.
      pose proof (IH Hnm') as HIH.
      pose proof (euler_dyadic_step T m k0 HT Hk0) as Hst. fold K in Hst.
      rewrite (Qabs_Qminus (euler_dyadic T m) (euler_dyadic T (S m))) in Hst.
      assert (Htri : Qabs (euler_dyadic T (S m) - euler_dyadic T n)
                     <= Qabs (euler_dyadic T (S m) - euler_dyadic T m)
                        + Qabs (euler_dyadic T m - euler_dyadic T n)).
      { setoid_replace (euler_dyadic T (S m) - euler_dyadic T n)
          with ((euler_dyadic T (S m) - euler_dyadic T m)
                + (euler_dyadic T m - euler_dyadic T n)) by ring.
        apply Qabs_triangle. }
      rewrite (half_pow_S' m).
      set (a := half_pow n) in *. set (b := half_pow m) in *.
      set (X := Qabs (euler_dyadic T (S m) - euler_dyadic T n)) in *.
      set (X1 := Qabs (euler_dyadic T (S m) - euler_dyadic T m)) in *.
      set (X2 := Qabs (euler_dyadic T m - euler_dyadic T n)) in *.
      clearbody K. lra.
Qed.

(** For n <= m the levels m and n differ by at most 2 K / 2^n. *)
Corollary euler_dyadic_modulus_tail : forall T k0, 0 <= T ->
  L * T < inject_Z (Z.of_nat (S k0)) ->
  forall n m, (n <= m)%nat ->
  Qabs (euler_dyadic T m - euler_dyadic T n)
  <= 2 * ((L * M * T * T / 4) * growth_cap (L * T) k0) * half_pow n.
Proof.
  intros T k0 HT Hk0 n m Hnm.
  eapply Qle_trans; [ apply (euler_dyadic_modulus T k0 HT Hk0 n m Hnm) | ].
  pose proof (dyadic_const_nonneg T k0 HT Hk0) as HK.
  pose proof (half_pow_pos m) as Hm.
  set (K := (L * M * T * T / 4) * growth_cap (L * T) k0) in *.
  apply qmul_le_l; lra.
Qed.

(** THE GUARANTEE FOR THE POLYGON ITSELF: for every T >= 0 the values of the
    Euler polygons at the moment T under doubling of the grid form a Cauchy
    process. *)
Theorem euler_dyadic_is_Cauchy : forall T, 0 <= T -> is_Cauchy (euler_dyadic T).
Proof.
  intros T HT eps Heps.
  assert (H01 : 0 < 1) by lra.
  destruct (ladder_archimedean (L * T) 1 H01) as [K0 HK0].
  assert (Hk0 : L * T < inject_Z (Z.of_nat (S K0))).
  { rewrite inj_S. lra. }
  pose proof (dyadic_const_nonneg T K0 HT Hk0) as HK.
  set (K := (L * M * T * T / 4) * growth_cap (L * T) K0) in *.
  destruct (half_pow_vanish (2 * K) eps Heps) as [J HJ].
  exists J. intros m n Hm Hn.
  assert (key : forall a b, (J <= b)%nat -> (b <= a)%nat ->
            Qabs (euler_dyadic T a - euler_dyadic T b) < eps).
  { intros a b Hb Hba.
    eapply Qle_lt_trans; [ apply (euler_dyadic_modulus_tail T K0 HT Hk0 b a Hba) | ].
    fold K.
    pose proof (half_pow_antitone J b Hb) as H1.
    assert (H3 : 2 * K * half_pow b <= 2 * K * half_pow J)
      by (apply qmul_le_l; lra).
    lra. }
  destruct (Nat.le_ge_cases n m) as [Hnm|Hmn].
  - apply key; assumption.
  - rewrite (Qabs_Qminus (euler_dyadic T m) (euler_dyadic T n)).
    apply key; assumption.
Qed.

(* ===================================================================== *)
(*  4. The same for euler_traj of Chapter 8.2 at the moment t = 1         *)
(* ===================================================================== *)

Lemma euler_traj_dyadic : forall j : nat,
  PicardLindelof.euler_traj (fun _ : Q => g) y0 (2 ^ j) (2 ^ j) == euler_dyadic 1 j.
Proof.
  intro j.
  eapply Qeq_trans;
    [ apply euler_traj_eq_euler; intros t1 t2 y1 y2 _ E; apply g_compat; exact E | ].
  unfold euler_dyadic. apply eul_step_wd.
  pose proof (pow2_half j) as Hp.
  assert (Hn : 0 < inject_Z (Z.of_nat (2 ^ j))).
  { apply inj_pos. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. }
  set (n := inject_Z (Z.of_nat (2 ^ j))) in *.
  assert (X : half_pow j == (n * half_pow j) / n) by (field; lra).
  rewrite Hp in X. rewrite X. field. lra.
Qed.

Theorem euler_traj_dyadic_is_Cauchy :
  is_Cauchy (fun j => PicardLindelof.euler_traj (fun _ : Q => g) y0 (2 ^ j) (2 ^ j)).
Proof.
  intros eps Heps.
  assert (H01 : 0 <= 1) by lra.
  destruct (euler_dyadic_is_Cauchy 1 H01 eps Heps) as [J HJ].
  exists J. intros m n Hm Hn. cbv beta.
  rewrite (euler_traj_dyadic m), (euler_traj_dyadic n). apply HJ; assumption.
Qed.

End Refinement.

(** For L = 0 (a constant right-hand side) the bound is zero: the polygons
    of all grids coincide at the common nodes. *)
Lemma refine_bound_zero_L : forall (M d : Q) (k : nat), refine_bound 0 M d k == 0.
Proof.
  intros M d k. induction k as [|k IH]; cbn [refine_bound].
  - reflexivity.
  - rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  5. The premises are satisfiable with L > 0: the identity cut at -1, 1 *)
(* ===================================================================== *)

Definition clamp1 (y : Q) : Q :=
  if Qlt_le_dec y (-1) then -1 else if Qlt_le_dec 1 y then 1 else y.

Lemma clamp1_bounded : forall y, Qabs (clamp1 y) <= 1.
Proof.
  intro y. unfold clamp1.
  destruct (Qlt_le_dec y (-1)); [ | destruct (Qlt_le_dec 1 y) ];
    apply Qabs_Qle_condition; split; lra.
Qed.

Lemma clamp1_lipschitz : forall y1 y2,
  Qabs (clamp1 y1 - clamp1 y2) <= 1 * Qabs (y1 - y2).
Proof.
  intros y1 y2.
  pose proof (Qle_Qabs (y1 - y2)) as H1.
  pose proof (Qle_Qabs (- (y1 - y2))) as H2. rewrite Qabs_opp in H2.
  pose proof (Qabs_nonneg (y1 - y2)) as H0.
  set (A := Qabs (y1 - y2)) in *.
  apply Qabs_Qle_condition. unfold clamp1.
  destruct (Qlt_le_dec y1 (-1)); destruct (Qlt_le_dec 1 y1);
    destruct (Qlt_le_dec y2 (-1)); destruct (Qlt_le_dec 1 y2); split; lra.
Qed.

(** It is the identity between -1 and 1: there the equation is y' = y. *)
Lemma clamp1_inside : forall y, -1 <= y -> y <= 1 -> clamp1 y == y.
Proof.
  intros y H1 H2. unfold clamp1.
  destruct (Qlt_le_dec y (-1)); [ lra | destruct (Qlt_le_dec 1 y); lra ].
Qed.

Theorem clamp1_dyadic_is_Cauchy : forall (y0 T : Q), 0 <= T ->
  is_Cauchy (euler_dyadic clamp1 y0 T).
Proof.
  intros y0 T HT.
  assert (H01 : 0 <= 1) by lra.
  exact (euler_dyadic_is_Cauchy clamp1 1 1 H01 clamp1_lipschitz clamp1_bounded y0 T HT).
Qed.
