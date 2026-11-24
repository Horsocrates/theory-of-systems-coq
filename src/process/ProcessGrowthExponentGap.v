(** * ProcessGrowthExponentGap.v — The gap between the exponents 1 and 2 as a statement
      about recurrences: a linear growth rate gives a bound uniform in the step for
      every time; a quadratic one gives it only up to a finite moment and not beyond
      (Part IX, chapter 5: the "wall")

    Elements: rational values y_n of a recurrence on every step; the rate constant
              C; the step h = T / N; the moment T; natural numbers N (steps), K
              (modes).
    Roles:    y_{n+1} = y_n + h C y_n     = role-linear comparison (exponent 1);
              y_{n+1} = y_n + h C y_n^2   = role-quadratic comparison (exponent 2);
              a bound for all N at once = role-control uniform in the step;
              1 / (C y_0) = role-critical moment of the quadratic comparison;
              C y_0 T < 1 = role-subcritical regime ("small data or short time").
    Rules:    the linear recurrence is y_0 (1 + C T / N)^N, and the ladder
              (1 + s / N)^N is bounded for all N. For the quadratic recurrence
              y_n (1 - n h C y_0) <= y_0 always; and y_0 <= y_n (1 - n h C y_0 +
              n (h C)^2 y_0 M) as long as the values stay below M.

    ============ E/R/R разбор ============
      Rules (L5): линейная рекуррента есть y_0 (1 + C T / N)^N, а лестница
                  (1 + s / N)^N ограничена при всех N. Для квадратичной рекурренты
                  всегда y_n (1 − n h C y_0) <= y_0; и y_0 <= y_n (1 − n h C y_0 +
                  n (h C)^2 y_0 M), пока значения не превосходят M.
      Roles (L4): линейная рекуррента — роль-сравнение с показателем 1;
                  квадратичная — роль-сравнение с показателем 2; оценка сразу при
                  всех N — роль-контроль, равномерный по шагу; 1 / (C y_0) —
                  роль-критический момент; C y_0 T < 1 — роль-докритический режим.
      Elements  : рациональные значения на каждом конечном шаге (L1 + P4).
    ДИАГНОСТИКА P4: «взрыва за конечное время» как завершённого события в
    утверждениях нет: сказано, что при C y_0 T > 1 для всякого числа M найдётся
    шаг сетки, при котором значение в момент T больше M. Предел по шагу не берётся.

    PROVED (all closed under the global context):
      - exponent 1: for every C, y_0, T >= 0 the values of the linear recurrence at
        the moment T are bounded by one number for all steps
        ([linear_growth_uniform_in_step]);
      - exponent 2, below the critical moment: for C y_0 T < 1 the values of the
        quadratic recurrence at the moment T are bounded by y_0 / (1 - C y_0 T)
        for all steps ([quadratic_growth_subcritical]);
      - exponent 2, beyond the critical moment: for C y_0 T > 1 there is no bound
        uniform in the step ([quadratic_growth_not_uniform_in_step]);
      - in the terms of the Navier-Stokes layer: the constant of the linear
        estimate at a fixed number of modes K is unbounded in K
        ([k_rate_unbounded]).

    NOT claimed: that the enstrophy of a Galerkin trajectory satisfies either
    recurrence; that no method closes the gap (it cannot be a theorem); anything
    about the limit of the step; the case C y_0 T = 1.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessExpProcess.
From ToS Require Import process.ProcessExpLadder.
From ToS Require navier_stokes.EnstrophyProduction.
From ToS Require navier_stokes.GronwallAnalysis.

Open Scope Q_scope.

Lemma inject_nat_S_gap : forall n, inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. reflexivity.
Qed.

Lemma inject_nat_nonneg_gap : forall n, 0 <= inject_Z (Z.of_nat n).
Proof. intro n. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

(* ===================================================================== *)
(*  1. Exponent 1: the linear recurrence                                   *)
(* ===================================================================== *)

Fixpoint lin_iter (C h y0 : Q) (n : nat) : Q :=
  match n with
  | O => y0
  | S k => lin_iter C h y0 k + h * C * lin_iter C h y0 k
  end.

Lemma lin_iter_closed : forall C h y0 n, lin_iter C h y0 n == y0 * qpow (1 + h * C) n.
Proof.
  intros C h y0 n. induction n as [|n IH]; cbn [lin_iter qpow].
  - ring.
  - rewrite IH. ring.
Qed.

(** For every moment T the values at T are bounded by one number for all steps. *)
Theorem linear_growth_uniform_in_step : forall C y0 T,
  0 <= C -> 0 <= y0 -> 0 <= T ->
  exists U, forall N, lin_iter C (T / inject_Z (Z.of_nat (S N))) y0 (S N) <= U.
Proof.
  intros C y0 T HC Hy0 HT.
  set (s := C * T).
  assert (Hs : 0 <= s) by (unfold s; apply Qmult_le_0_compat; assumption).
  destruct (ladder_archimedean s 1 ltac:(reflexivity)) as [K HK].
  assert (HsK : s < inject_Z (Z.of_nat (S K))).
  { rewrite inject_nat_S_gap. rewrite Qmult_1_r in HK. lra. }
  exists (y0 * (1 / qpow (1 - s / inject_Z (Z.of_nat (S K))) (S K))).
  intro N. rewrite lin_iter_closed.
  pose proof (exp1_pos_denom N) as Hd.
  assert (E : qpow (1 + T / inject_Z (Z.of_nat (S N)) * C) (S N) == expt_process s N).
  { unfold expt_process. apply qpow_wd. unfold s. field. lra. }
  rewrite E.
  pose proof (expt_bounded s N K Hs HsK) as Hb.
  assert (H1 : y0 * expt_process s N
               <= y0 * (1 / qpow (1 - s / inject_Z (Z.of_nat (S K))) (S K))).
  { rewrite (Qmult_comm y0 (expt_process s N)).
    rewrite (Qmult_comm y0 (1 / qpow (1 - s / inject_Z (Z.of_nat (S K))) (S K))).
    apply Qmult_le_compat_r; assumption. }
  exact H1.
Qed.

(* ===================================================================== *)
(*  2. Exponent 2: the quadratic recurrence                                *)
(* ===================================================================== *)

Fixpoint quad_iter (C h y0 : Q) (n : nat) : Q :=
  match n with
  | O => y0
  | S k => quad_iter C h y0 k + h * C * (quad_iter C h y0 k * quad_iter C h y0 k)
  end.

Lemma quad_iter_pos : forall C h y0, 0 <= C -> 0 <= h -> 0 < y0 ->
  forall n, 0 < quad_iter C h y0 n.
Proof.
  intros C h y0 HC Hh Hy0 n. induction n as [|n IH]; cbn [quad_iter].
  - exact Hy0.
  - assert (H1 : 0 <= h * C) by (apply Qmult_le_0_compat; assumption).
    assert (H2 : 0 <= quad_iter C h y0 n * quad_iter C h y0 n)
      by (apply Qmult_le_0_compat; lra).
    assert (H3 : 0 <= h * C * (quad_iter C h y0 n * quad_iter C h y0 n))
      by (apply Qmult_le_0_compat; assumption).
    lra.
Qed.

Lemma quad_iter_step_le : forall C h y0 n, 0 <= C -> 0 <= h ->
  quad_iter C h y0 n <= quad_iter C h y0 (S n).
Proof.
  intros C h y0 n HC Hh. cbn [quad_iter].
  assert (H1 : 0 <= h * C) by (apply Qmult_le_0_compat; assumption).
  assert (H2 : 0 <= quad_iter C h y0 n * quad_iter C h y0 n).
  { destruct (Qlt_le_dec (quad_iter C h y0 n) 0) as [Hneg | Hpos].
    - assert (E : quad_iter C h y0 n * quad_iter C h y0 n
                  == (- quad_iter C h y0 n) * (- quad_iter C h y0 n)) by ring.
      rewrite E. apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; assumption. }
  assert (H3 : 0 <= h * C * (quad_iter C h y0 n * quad_iter C h y0 n))
    by (apply Qmult_le_0_compat; assumption).
  lra.
Qed.

Lemma quad_iter_mono : forall C h y0 n m, 0 <= C -> 0 <= h -> (n <= m)%nat ->
  quad_iter C h y0 n <= quad_iter C h y0 m.
Proof.
  intros C h y0 n m HC Hh Hnm. induction Hnm as [|m Hnm IH].
  - apply Qle_refl.
  - eapply Qle_trans; [ exact IH | apply quad_iter_step_le; assumption ].
Qed.

(** Always: y_n (1 - n h C y_0) <= y_0. *)
Lemma quad_iter_upper_key : forall C h y0, 0 <= C -> 0 <= h -> 0 < y0 -> forall n,
  quad_iter C h y0 n * (1 - inject_Z (Z.of_nat n) * (h * C * y0)) <= y0.
Proof.
  intros C h y0 HC Hh Hy0 n. induction n as [|n IH].
  - cbn [quad_iter Z.of_nat inject_Z].
    assert (E : y0 * (1 - 0 * (h * C * y0)) == y0) by ring.
    rewrite E. apply Qle_refl.
  - cbn [quad_iter]. rewrite inject_nat_S_gap.
    pose proof (quad_iter_pos C h y0 HC Hh Hy0 n) as Hy.
    set (y := quad_iter C h y0 n) in *.
    set (m := inject_Z (Z.of_nat n)) in *.
    assert (Hc : 0 <= h * C) by (apply Qmult_le_0_compat; assumption).
    assert (Hcy : 0 <= h * C * y) by (apply Qmult_le_0_compat; lra).
    (* (y + c y^2)(D - a) = y D + c y (y D) - c y0 y - a c y^2,  D = 1 - m a, a = c y0 *)
    assert (H1 : (h * C * y) * (y * (1 - m * (h * C * y0))) <= (h * C * y) * y0).
    { rewrite (Qmult_comm (h * C * y) (y * (1 - m * (h * C * y0)))).
      rewrite (Qmult_comm (h * C * y) y0).
      apply Qmult_le_compat_r; assumption. }
    assert (H2 : 0 <= (h * C * y0) * (h * C) * (y * y)).
    { apply Qmult_le_0_compat.
      - apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; lra | exact Hc ].
      - apply Qmult_le_0_compat; lra. }
    assert (E : (y + h * C * (y * y)) * (1 - (m + 1) * (h * C * y0))
                == y * (1 - m * (h * C * y0))
                   + (h * C * y) * (y * (1 - m * (h * C * y0)))
                   - (h * C * y) * y0
                   - (h * C * y0) * (h * C) * (y * y)) by ring.
    rewrite E.
    set (p := y * (1 - m * (h * C * y0))) in *.
    set (q := (h * C * y) * p) in *.
    set (r := (h * C * y) * y0) in *.
    set (t := (h * C * y0) * (h * C) * (y * y)) in *.
    lra.
Qed.

(** Below the critical moment the values at T are bounded for all steps. *)
Theorem quadratic_growth_subcritical : forall C y0 T,
  0 <= C -> 0 < y0 -> 0 <= T -> C * y0 * T < 1 ->
  forall N, quad_iter C (T / inject_Z (Z.of_nat (S N))) y0 (S N) <= y0 / (1 - C * y0 * T).
Proof.
  intros C y0 T HC Hy0 HT Hsub N.
  pose proof (exp1_pos_denom N) as Hd.
  set (d := inject_Z (Z.of_nat (S N))) in *.
  set (h := T / d).
  assert (Hh : 0 <= h).
  { unfold h. apply Qle_shift_div_l; [ exact Hd | lra ]. }
  assert (Hdh : d * h == T) by (unfold h; field; lra).
  pose proof (quad_iter_upper_key C h y0 HC Hh Hy0 (S N)) as HK.
  fold d in HK.
  assert (E : 1 - d * (h * C * y0) == 1 - C * y0 * T).
  { assert (E1 : 1 - d * (h * C * y0) == 1 - (d * h) * (C * y0)) by ring.
    rewrite E1, Hdh. ring. }
  rewrite E in HK.
  apply Qle_shift_div_l; [ lra | exact HK ].
Qed.

(** While the values stay below M:
    y_0 <= y_n (1 - n h C y_0 + n (h C)^2 y_0 M). *)
Lemma quad_iter_lower_key : forall C h y0 M, 0 <= C -> 0 <= h -> 0 < y0 -> forall n,
  (forall k, (k < n)%nat -> quad_iter C h y0 k <= M) ->
  y0 <= quad_iter C h y0 n
        * (1 - inject_Z (Z.of_nat n) * (h * C * y0)
           + inject_Z (Z.of_nat n) * ((h * C) * (h * C) * y0 * M)).
Proof.
  intros C h y0 M HC Hh Hy0 n. induction n as [|n IH]; intro HM.
  - cbn [quad_iter Z.of_nat inject_Z].
    assert (E : y0 * (1 - 0 * (h * C * y0) + 0 * ((h * C) * (h * C) * y0 * M)) == y0) by ring.
    rewrite E. apply Qle_refl.
  - cbn [quad_iter]. rewrite inject_nat_S_gap.
    assert (IH' := IH (fun k Hk => HM k (Nat.lt_lt_succ_r _ _ Hk))).
    pose proof (HM n (Nat.lt_succ_diag_r n)) as HyM.
    pose proof (quad_iter_pos C h y0 HC Hh Hy0 n) as Hy.
    set (y := quad_iter C h y0 n) in *.
    set (m := inject_Z (Z.of_nat n)) in *.
    assert (Hc : 0 <= h * C) by (apply Qmult_le_0_compat; assumption).
    set (Ee := 1 - m * (h * C * y0) + m * ((h * C) * (h * C) * y0 * M)) in *.
    assert (T1 : 0 <= (y * Ee - y0) * (1 + h * C * y)).
    { apply Qmult_le_0_compat; [ lra | ].
      assert (0 <= h * C * y) by (apply Qmult_le_0_compat; lra). lra. }
    assert (T2 : 0 <= (h * C) * (h * C) * y0 * y * (M - y)).
    { apply Qmult_le_0_compat; [ | lra ].
      apply Qmult_le_0_compat; [ | lra ].
      apply Qmult_le_0_compat; [ | lra ].
      apply Qmult_le_0_compat; assumption. }
    assert (T3 : 0 <= (h * C) * (h * C) * (h * C) * y0 * M * (y * y)).
    { apply Qmult_le_0_compat; [ | apply Qmult_le_0_compat; lra ].
      apply Qmult_le_0_compat; [ | lra ].
      apply Qmult_le_0_compat; [ | lra ].
      apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; assumption | exact Hc ]. }
    assert (E : (y + h * C * (y * y))
                * (1 - (m + 1) * (h * C * y0) + (m + 1) * ((h * C) * (h * C) * y0 * M))
                == y0 + (y * Ee - y0) * (1 + h * C * y)
                   + (h * C) * (h * C) * y0 * y * (M - y)
                   + (h * C) * (h * C) * (h * C) * y0 * M * (y * y))
      by (unfold Ee; ring).
    rewrite E.
    set (t1 := (y * Ee - y0) * (1 + h * C * y)) in *.
    set (t2 := (h * C) * (h * C) * y0 * y * (M - y)) in *.
    set (t3 := (h * C) * (h * C) * (h * C) * y0 * M * (y * y)) in *.
    lra.
Qed.

(** Beyond the critical moment there is no bound uniform in the step: for every
    M there is a grid on which the value at the moment T exceeds M. *)
Theorem quadratic_growth_not_uniform_in_step : forall C y0 T M,
  0 < C -> 0 < y0 -> 1 < C * y0 * T ->
  exists N, M < quad_iter C (T / inject_Z (Z.of_nat (S N))) y0 (S N).
Proof.
  intros C y0 T M HC Hy0 Hsup.
  assert (Hp : 0 < C * y0) by (apply Qmult_lt_0_compat; assumption).
  assert (HT : 0 < T).
  { destruct (Qlt_le_dec 0 T) as [H | H]; [ exact H | exfalso ].
    assert (Hx : 0 <= (C * y0) * (- T)) by (apply Qmult_le_0_compat; lra).
    assert (E : (C * y0) * (- T) == - (C * y0 * T)) by ring.
    rewrite E in Hx. lra. }
  destruct (Qlt_le_dec 0 M) as [HM | HM].
  2: { exists 0%nat.
       assert (Hh : 0 <= T / inject_Z (Z.of_nat 1)).
       { apply Qle_shift_div_l; [ reflexivity | lra ]. }
       pose proof (quad_iter_pos C (T / inject_Z (Z.of_nat 1)) y0
                     (Qlt_le_weak _ _ HC) Hh Hy0 1%nat) as Hpos.
       lra. }
  set (g := C * y0 * T - 1).
  assert (Hg : 0 < g) by (unfold g; lra).
  set (Kc := T * C * C * y0 * M).
  destruct (ladder_archimedean (T * Kc) g Hg) as [K HK].
  exists K.
  pose proof (exp1_pos_denom K) as Hd.
  set (d := inject_Z (Z.of_nat (S K))) in *.
  set (h := T / d).
  assert (Hh : 0 <= h).
  { unfold h. apply Qle_shift_div_l; [ exact Hd | lra ]. }
  assert (Hdh : d * h == T) by (unfold h; field; lra).
  destruct (Qlt_le_dec M (quad_iter C h y0 (S K))) as [Hgt | Hle]; [ exact Hgt | exfalso ].
  assert (Hall : forall k, (k < S K)%nat -> quad_iter C h y0 k <= M).
  { intros k Hk. eapply Qle_trans; [ | exact Hle ].
    apply quad_iter_mono; [ lra | exact Hh | lia ]. }
  pose proof (quad_iter_lower_key C h y0 M (Qlt_le_weak _ _ HC) Hh Hy0 (S K) Hall) as Hkey.
  fold d in Hkey.
  pose proof (quad_iter_pos C h y0 (Qlt_le_weak _ _ HC) Hh Hy0 (S K)) as Hy.
  set (y := quad_iter C h y0 (S K)) in *.
  assert (E : 1 - d * (h * C * y0) + d * ((h * C) * (h * C) * y0 * M)
              == 1 - C * y0 * T + h * Kc).
  { assert (E1 : 1 - d * (h * C * y0) + d * ((h * C) * (h * C) * y0 * M)
                 == 1 - (d * h) * (C * y0) + h * ((d * h) * C * C * y0 * M)) by ring.
    rewrite E1, Hdh. unfold Kc. ring. }
  rewrite E in Hkey.
  (* h * Kc < g *)
  assert (HdK : inject_Z (Z.of_nat K) <= d).
  { unfold d. rewrite inject_nat_S_gap. lra. }
  assert (HKg : inject_Z (Z.of_nat K) * g <= d * g)
    by (apply Qmult_le_compat_r; [ exact HdK | lra ]).
  assert (HhK : h * Kc < g).
  { assert (E2 : h * Kc == (T * Kc) / d) by (unfold h; field; lra).
    rewrite E2. apply Qlt_shift_div_r; [ exact Hd | ].
    set (u := inject_Z (Z.of_nat K) * g) in *. set (v := d * g) in *.
    assert (E3 : g * d == v) by (unfold v; ring).
    rewrite E3. lra. }
  assert (Hneg : 1 - C * y0 * T + h * Kc < 0) by (unfold g in HhK; lra).
  assert (Hprod : 0 < y * (- (1 - C * y0 * T + h * Kc))) by (apply Qmult_lt_0_compat; lra).
  assert (E4 : y * (- (1 - C * y0 * T + h * Kc)) == - (y * (1 - C * y0 * T + h * Kc))) by ring.
  rewrite E4 in Hprod.
  set (z := y * (1 - C * y0 * T + h * Kc)) in *.
  lra.
Qed.

(* ===================================================================== *)
(*  3. In the terms of the Navier-Stokes layer                             *)
(* ===================================================================== *)

(** The constant of the linear estimate at a fixed number of modes K — the number
    k_dependent_rate of GronwallAnalysis.v — is unbounded in K. *)
Theorem k_rate_unbounded : forall C_lady E_0 nu M,
  0 < C_lady -> 0 < E_0 -> 0 < nu ->
  exists K : nat, M < GronwallAnalysis.k_dependent_rate C_lady E_0 nu K.
Proof.
  intros C E0 nu M HC HE Hnu.
  set (c := C * C * E0 / nu).
  assert (Hc : 0 < c).
  { unfold c. apply Qlt_shift_div_l; [ exact Hnu | ].
    assert (0 < C * C) by (apply Qmult_lt_0_compat; assumption).
    assert (0 < C * C * E0) by (apply Qmult_lt_0_compat; assumption).
    lra. }
  destruct (ladder_archimedean M c Hc) as [K HK].
  exists K.
  unfold GronwallAnalysis.k_dependent_rate, EnstrophyProduction.linear_rate_constant.
  assert (Hle : inject_Z (Z.of_nat K) <= inject_Z (Z.of_nat (K * K))).
  { rewrite <- Zle_Qle. apply Nat2Z.inj_le. nia. }
  assert (E : C * C * E0 * inject_Z (Z.of_nat (K * K)) / nu
              == inject_Z (Z.of_nat (K * K)) * c).
  { unfold c. unfold Qdiv. ring. }
  rewrite E.
  apply Qlt_le_trans with (inject_Z (Z.of_nat K) * c); [ exact HK | ].
  apply Qmult_le_compat_r; [ exact Hle | lra ].
Qed.

Print Assumptions linear_growth_uniform_in_step.
Print Assumptions quadratic_growth_subcritical.
Print Assumptions quadratic_growth_not_uniform_in_step.
Print Assumptions k_rate_unbounded.
