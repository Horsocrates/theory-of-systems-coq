(** * ProcessODELinearLaws.v — Exponential, linear equations, decay, systems and the
      oscillator: laws for every number of steps (Part VIII, chapter 5)

    Elements: rational Euler stages of y' = y, y' = L y, y' = -alpha y for every
              number of steps n; stages of the ladder (1 + s/n)^n for a rational s
              of either sign; rational state pairs (y_n, v_n) of the oscillator and
              its grid energy E_n = y_n^2 + v_n^2.
    Roles:    1 + L h = factor of one step; (1 + L t/n)^n = stage reached at the
              moment t in n steps; 1 - alpha h = factor of decay; 1 + h^2 = factor
              by which one explicit Euler step multiplies the energy; v = role of
              the first derivative in the reduction of order.
    Rules:    the general Euler recursion [euler_method] with the right-hand sides
              of the examples gives the closed forms; substitution h = t/n turns
              them into stages of the ladder; the ladder is a Cauchy process for
              every rational s; the grid energy obeys E_{k+1} = (1 + h^2) E_k, and
              its drift at a fixed moment t vanishes as the grid is refined.

    ============ E/R/R разбор ============
      Rules (L5): рекурсия Эйлера с правыми частями примеров даёт замкнутые формы
                  y0 (1+h)^n, y0 (1+Lh)^n, y0 (1-alpha h)^n; подстановка h = t/n —
                  стадия лестницы (1 + s/n)^n; закон энергии E_{k+1} = (1+h^2) E_k.
      Roles (L4): множитель шага — роль-темп; стадия лестницы — роль-рост к моменту t;
                  скорость v — роль первой производной; энергия — роль-инвариант
                  потока, на сетке — растущая величина.
      Elements  : рациональные стадии при каждом конечном n (L1 + P4).
    ДИАГНОСТИКА P4: все утверждения — о конечных рациональных стадиях; момент t и
    показатель s — рациональные параметры. Чисел e^t, e^{-alpha t}, функций sin, cos
    в утверждениях нет: их место занимают лестницы стадий и свойство Коши.

    PROVED (all closed under the global context):
      - y' = y: [exp_euler], [euler_yeqy], the e-process and the e^t-process are
        the general Euler recursion ([exp_euler_is_euler_method], [expt_is_euler_method]);
      - y' = L y: closed form for every n ([linear_euler_closed]), it is the
        homogeneous Gronwall iteration ([linear_euler_gronwall]), strict growth
        for L > 0 ([linear_growth]), the stage at the moment t ([linear_euler_at_time]);
      - the ladder (1 + s/n)^n is a Cauchy process for EVERY rational s
        ([expt_process_is_Cauchy_all]), with an explicit modulus for s <= 0
        ([expt_neg_modulus]);
      - y' = -alpha y: closed form, decay step by step for a nonnegative start,
        decay of the absolute value for every start, vanishing
        ([decay_euler_closed], [decay_euler_monotone], [decay_euler_abs_monotone],
        [decay_euler_vanishes]); the stage at the moment t and its Cauchy property
        ([decay_euler_at_time], [decay_euler_at_time_is_Cauchy]);
      - the examples under the Lipschitz condition alone are Cauchy processes of
        Euler-Picard iterations ([exp_picard_cauchy], [decay_picard_cauchy],
        [linear_picard_cauchy]);
      - reduction of order: the second difference equation
        ([order2_second_difference]);
      - oscillator: the energy law for every h and every start ([sho_energy_step],
        [sho_energy_closed]), strict drift ([sho_energy_strict]), the drift at a
        fixed moment t is at most 2 t^2/n times the initial energy and vanishes
        under refinement ([sho_energy_at_time_drift], [sho_energy_drift_vanishes]);
        the sign of the velocity ([sho_v1]).

    NOT claimed: the numbers e^t, e^{-alpha t} or the functions sin, cos as completed
    objects; convergence of the vector Euler process of the oscillator to a
    trajectory; conservation of energy by any scheme; Lipschitz/contraction
    estimates for systems.

    STATUS: 50 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessPicard.
From ToS Require Import process.ProcessGronwall.
From ToS Require Import process.ProcessODE.
From ToS Require Import process.ProcessODEExamples.
From ToS Require Import process.ProcessExpProcess.
From ToS Require Import process.ProcessExpLadder.
From ToS Require Import process.ProcessGronwallInequality.
From ToS Require Import process.ProcessPicardLipschitz.
From ToS Require Import process.ProcessODESystem.
From ToS Require CauchyReal.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. Helpers                                                             *)
(* ===================================================================== *)

Lemma is_Cauchy_ext : forall (R P : nat -> Q),
  (forall n, P n == R n) -> is_Cauchy R -> is_Cauchy P.
Proof.
  intros R P HP HR eps Heps.
  destruct (HR eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  rewrite (HP m), (HP n). apply HN; assumption.
Qed.

(** A constant multiple of a Cauchy process is a Cauchy process. *)
Lemma cauchy_scale_ext : forall (c : Q) (R P : nat -> Q),
  (forall n, P n == c * R n) -> is_Cauchy R -> is_Cauchy P.
Proof.
  intros c R P HP HR eps Heps.
  set (C := Qabs c + 1).
  assert (HC : 0 < C) by (unfold C; pose proof (Qabs_nonneg c); lra).
  assert (Hec : 0 < eps / C).
  { apply Qlt_shift_div_l; [ exact HC | lra ]. }
  destruct (HR (eps / C) Hec) as [N HN].
  exists N. intros m n Hm Hn.
  assert (E : P m - P n == c * (R m - R n)) by (rewrite (HP m), (HP n); ring).
  rewrite E, Qabs_Qmult.
  pose proof (HN m n Hm Hn) as Hlt.
  pose proof (Qabs_nonneg (R m - R n)) as Hd.
  assert (H1 : Qabs c * Qabs (R m - R n) <= C * Qabs (R m - R n)).
  { apply Qmult_le_compat_r; [ unfold C; lra | exact Hd ]. }
  assert (H2 : C * Qabs (R m - R n) < C * (eps / C)).
  { apply Qmult_lt_l; assumption. }
  assert (H3 : C * (eps / C) == eps) by (field; lra).
  lra.
Qed.

Lemma Qabs_mul_bound : forall x y p q,
  Qabs x <= p -> Qabs y <= q -> Qabs (x * y) <= p * q.
Proof.
  intros x y p q Hx Hy. rewrite Qabs_Qmult.
  pose proof (Qabs_nonneg x) as Hx0. pose proof (Qabs_nonneg y) as Hy0.
  apply Qle_trans with (p * Qabs y).
  - apply Qmult_le_compat_r; assumption.
  - apply qmul_le_l; [ lra | exact Hy ].
Qed.

(** a^2/(j+1) does not exceed a^2/(N+1) for j >= N. *)
Lemma sq_over_mono : forall a N j, (N <= j)%nat ->
  a * a / inject_Z (Z.of_nat (S j)) <= a * a / inject_Z (Z.of_nat (S N)).
Proof.
  intros a N j Hj.
  pose proof (exp1_pos_denom N) as HdN. pose proof (exp1_pos_denom j) as Hdj.
  pose proof (inj_le (S N) (S j) ltac:(lia)) as Hle.
  pose proof (Qsq_nonneg a) as Haa.
  set (dN := inject_Z (Z.of_nat (S N))) in *.
  set (dj := inject_Z (Z.of_nat (S j))) in *.
  apply Qle_shift_div_r; [ exact Hdj | ].
  apply Qle_trans with (a * a / dN * dN).
  - assert (E : a * a / dN * dN == a * a) by (field; lra).
    rewrite E. apply Qle_refl.
  - apply qmul_le_l; [ | exact Hle ].
    apply Qle_shift_div_l; [ exact HdN | lra ].
Qed.

(* ===================================================================== *)
(*  1. y' = y: the closed forms ARE the general Euler recursion            *)
(* ===================================================================== *)

(** [exp_euler] is defined by the closed formula y0 (1+h)^n. The general Euler
    method [euler_method] with the right-hand side [exp_rhs] gives exactly it. *)
Lemma exp_euler_is_euler_method : forall t0 y0 h n,
  euler_method (fun _ y => exp_rhs y) t0 y0 h n == exp_euler y0 h n.
Proof.
  intros t0 y0 h n. induction n as [|k IH].
  - unfold exp_euler. simpl. ring.
  - rewrite euler_method_succ. unfold euler_step, exp_rhs.
    rewrite IH, exp_euler_succ. ring.
Qed.

(** The local recursion [euler_yeqy] (ProcessExpProcess.v) is the same process. *)
Lemma euler_yeqy_is_exp_euler : forall h y0 M,
  euler_yeqy h y0 M == exp_euler y0 h M.
Proof.
  intros h y0 M. rewrite euler_yeqy_closed. unfold exp_euler.
  rewrite qpow_is_Qpow. reflexivity.
Qed.

(** The e-process is [exp_euler] with y0 = 1, h = 1/(N+1), N+1 steps. *)
Lemma exp1_is_exp_euler : forall N,
  exp1_process N == exp_euler 1 (1 / inject_Z (Z.of_nat (S N))) (S N).
Proof.
  intro N. unfold exp1_process, exp_euler. rewrite qpow_is_Qpow. ring.
Qed.

(** For an arbitrary moment t: the stage of the e^t-process is the Euler
    trajectory of y' = y with the step t/(N+1) after N+1 steps. *)
Lemma expt_is_euler : forall t N,
  expt_process t N == euler_yeqy (t / inject_Z (Z.of_nat (S N))) 1 (S N).
Proof.
  intros t N. unfold expt_process. rewrite euler_yeqy_closed. ring.
Qed.

Theorem expt_is_euler_method : forall t N,
  expt_process t N
  == euler_method (fun _ y => exp_rhs y) 0 1 (t / inject_Z (Z.of_nat (S N))) (S N).
Proof.
  intros t N. rewrite exp_euler_is_euler_method.
  unfold exp_euler, expt_process. rewrite qpow_is_Qpow. ring.
Qed.

(* ===================================================================== *)
(*  2. y' = L y: the Euler trajectory for every number of steps            *)
(* ===================================================================== *)

Lemma linear_euler_closed : forall L t0 y0 h n,
  euler_method (fun _ y => L * y) t0 y0 h n == y0 * Qpow (1 + L * h) n.
Proof.
  intros L t0 y0 h n. induction n as [|k IH].
  - simpl. ring.
  - rewrite euler_method_succ, linear_euler_step, IH. cbn [Qpow]. ring.
Qed.

(** The trajectory of the linear equation is the homogeneous Gronwall iteration. *)
Lemma linear_euler_gronwall : forall L t0 y0 h n,
  euler_method (fun _ y => L * y) t0 y0 h n == gronwall_iterate L 0 h y0 n.
Proof.
  intros. rewrite linear_euler_closed, gronwall_beta_zero. reflexivity.
Qed.

(** Growth for L > 0: a positive trajectory strictly increases. *)
Lemma linear_growth : forall L y0 h n, 0 < L -> 0 < h -> 0 < y0 ->
  y0 * Qpow (1 + L * h) n < y0 * Qpow (1 + L * h) (S n).
Proof.
  intros L y0 h n HL Hh Hy.
  assert (HLh : 0 < L * h) by (apply Qmult_lt_0_compat; assumption).
  assert (Hp : 0 < Qpow (1 + L * h) n) by (apply Qpow_pos; lra).
  assert (Hyp : 0 < y0 * Qpow (1 + L * h) n) by (apply Qmult_lt_0_compat; assumption).
  assert (Hinc : 0 < (L * h) * (y0 * Qpow (1 + L * h) n))
    by (apply Qmult_lt_0_compat; assumption).
  cbn [Qpow].
  setoid_replace (y0 * ((1 + L * h) * Qpow (1 + L * h) n))
    with (y0 * Qpow (1 + L * h) n + (L * h) * (y0 * Qpow (1 + L * h) n)) by ring.
  lra.
Qed.

Theorem linear_euler_growth : forall L t0 y0 h n, 0 < L -> 0 < h -> 0 < y0 ->
  euler_method (fun _ y => L * y) t0 y0 h n
  < euler_method (fun _ y => L * y) t0 y0 h (S n).
Proof.
  intros L t0 y0 h n HL Hh Hy. rewrite !linear_euler_closed.
  apply linear_growth; assumption.
Qed.

(** The moment t reached in k+1 steps: the stage of the ladder (1 + L t/n)^n. *)
Theorem linear_euler_at_time : forall L t y0 k,
  euler_method (fun _ y => L * y) 0 y0 (t / inject_Z (Z.of_nat (S k))) (S k)
  == y0 * expt_process (L * t) k.
Proof.
  intros L t y0 k. rewrite linear_euler_closed. unfold expt_process.
  rewrite <- qpow_is_Qpow.
  pose proof (exp1_pos_denom k) as Hd.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (E : 1 + L * (t / d) == 1 + L * t / d) by (field; lra).
  rewrite (qpow_wd _ _ (S k) E). reflexivity.
Qed.

(* ===================================================================== *)
(*  3. The ladder (1 + s/n)^n for a NEGATIVE exponent                      *)
(* ===================================================================== *)

(** (1 - a/n)^n (1 + a/n)^n = (1 - a^2/n^2)^n. *)
Lemma expt_neg_times_pos : forall a k,
  expt_process (- a) k * expt_process a k
  == qpow (1 - (a / inject_Z (Z.of_nat (S k))) * (a / inject_Z (Z.of_nat (S k)))) (S k).
Proof.
  intros a k. unfold expt_process.
  pose proof (exp1_pos_denom k) as Hd.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  rewrite <- qpow_mult.
  apply qpow_wd. field. lra.
Qed.

(** 1 - a^2/n <= (1 - a^2/n^2)^n <= 1, and the power is nonnegative (n >= a). *)
Lemma sq_ladder_bounds : forall a k,
  0 <= a -> a <= inject_Z (Z.of_nat (S k)) ->
  1 - a * a / inject_Z (Z.of_nat (S k))
    <= qpow (1 - (a / inject_Z (Z.of_nat (S k))) * (a / inject_Z (Z.of_nat (S k)))) (S k)
  /\ qpow (1 - (a / inject_Z (Z.of_nat (S k))) * (a / inject_Z (Z.of_nat (S k)))) (S k) <= 1
  /\ 0 <= qpow (1 - (a / inject_Z (Z.of_nat (S k))) * (a / inject_Z (Z.of_nat (S k)))) (S k).
Proof.
  intros a k Ha Had.
  pose proof (exp1_pos_denom k) as Hd.
  pose proof (bernoulli_ge_m1
                (- ((a / inject_Z (Z.of_nat (S k))) * (a / inject_Z (Z.of_nat (S k)))))
                (S k)) as HB.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (Hx0 : 0 <= a / d) by (apply Qle_shift_div_l; [ exact Hd | lra ]).
  assert (Hx1 : a / d <= 1) by (apply Qle_shift_div_r; [ exact Hd | lra ]).
  assert (E1 : 1 + d * - (a / d * (a / d)) == 1 - a * a / d) by (field; lra).
  set (x := a / d) in *.
  assert (Hxx0 : 0 <= x * x) by (apply Qmult_le_0_compat; assumption).
  assert (Hxx1 : x * x <= 1).
  { apply Qle_trans with (1 * x); [ apply Qmult_le_compat_r; assumption | lra ]. }
  assert (E2 : 1 + - (x * x) == 1 - x * x) by ring.
  split; [ | split ].
  - specialize (HB ltac:(lra)).
    rewrite E1, (qpow_wd _ _ (S k) E2) in HB. exact HB.
  - apply Qle_trans with (qpow 1 (S k)); [ | rewrite qpow_one; apply Qle_refl ].
    apply qpow_le_base; lra.
  - apply qpow_nonneg_base. lra.
Qed.

Lemma expt_neg_pos_product_bounds : forall a N j,
  0 <= a -> a <= inject_Z (Z.of_nat (S N)) -> (N <= j)%nat ->
  1 - a * a / inject_Z (Z.of_nat (S N)) <= expt_process (- a) j * expt_process a j
  /\ expt_process (- a) j * expt_process a j <= 1
  /\ 0 <= expt_process (- a) j * expt_process a j.
Proof.
  intros a N j Ha HaN Hj.
  assert (Haj : a <= inject_Z (Z.of_nat (S j))).
  { eapply Qle_trans; [ exact HaN | apply inj_le; lia ]. }
  destruct (sq_ladder_bounds a j Ha Haj) as [Hlo [Hhi H0]].
  rewrite expt_neg_times_pos. split; [ | split; assumption ].
  eapply Qle_trans; [ | exact Hlo ].
  pose proof (sq_over_mono a N j Hj) as Hm.
  set (u := a * a / inject_Z (Z.of_nat (S j))) in *.
  set (w := a * a / inject_Z (Z.of_nat (S N))) in *.
  lra.
Qed.

(** Bounds of a stage with a negative exponent: 1 - a <= (1 - a/n)^n <= 1. *)
Lemma expt_neg_bounds : forall a k,
  0 <= a -> a <= inject_Z (Z.of_nat (S k)) ->
  1 - a <= expt_process (- a) k /\ expt_process (- a) k <= 1
  /\ 0 <= expt_process (- a) k.
Proof.
  intros a k Ha Had. unfold expt_process.
  pose proof (exp1_pos_denom k) as Hd.
  pose proof (bernoulli_ge_m1 (- a / inject_Z (Z.of_nat (S k))) (S k)) as HB.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (Hx0 : 0 <= a / d) by (apply Qle_shift_div_l; [ exact Hd | lra ]).
  assert (Hx1 : a / d <= 1) by (apply Qle_shift_div_r; [ exact Hd | lra ]).
  assert (Ex : - a / d == - (a / d)) by (field; lra).
  assert (E1 : 1 + d * (- a / d) == 1 - a) by (field; lra).
  set (x := a / d) in *.
  split; [ | split ].
  - assert (Hm1 : -1 <= - a / d) by (rewrite Ex; lra).
    specialize (HB Hm1). rewrite E1 in HB. exact HB.
  - apply Qle_trans with (qpow 1 (S k)); [ | rewrite qpow_one; apply Qle_refl ].
    apply qpow_le_base; rewrite Ex; lra.
  - apply qpow_nonneg_base. rewrite Ex. lra.
Qed.

(** Explicit modulus for a negative exponent: beyond the stage N >= k0, where
    k0 + 1 > a, any two stages differ by at most 2 B a^2/(N+1),
    B = (1 - a/(k0+1))^(-(k0+1)). *)
Theorem expt_neg_modulus : forall a k0, 0 <= a -> a < inject_Z (Z.of_nat (S k0)) ->
  forall N m n, (k0 <= N)%nat -> (N <= m)%nat -> (N <= n)%nat ->
  Qabs (expt_process (- a) m - expt_process (- a) n)
  <= 2 * (1 / qpow (1 - a / inject_Z (Z.of_nat (S k0))) (S k0))
       * (a * a / inject_Z (Z.of_nat (S N))).
Proof.
  intros a k0 Ha Hk0 N m n HN Hm Hn.
  assert (HaN : a <= inject_Z (Z.of_nat (S N))).
  { eapply Qle_trans; [ apply Qlt_le_weak; exact Hk0 | apply inj_le; lia ]. }
  pose proof (expt_lower a m Ha) as HEm1.
  pose proof (expt_lower a n Ha) as HEn1.
  pose proof (expt_bounded a m k0 Ha Hk0) as HEmB.
  pose proof (expt_bounded a n k0 Ha Hk0) as HEnB.
  destruct (expt_neg_pos_product_bounds a N m Ha HaN Hm) as [Hcm_lo [Hcm_hi Hcm0]].
  destruct (expt_neg_pos_product_bounds a N n Ha HaN Hn) as [Hcn_lo [Hcn_hi Hcn0]].
  pose proof (expt_modulus a k0 Ha Hk0 m n ltac:(lia)) as Hmn.
  pose proof (expt_modulus a k0 Ha Hk0 n m ltac:(lia)) as Hnm.
  pose proof (sq_over_mono a N n Hn) as Hgn.
  pose proof (sq_over_mono a N m Hm) as Hgm.
  pose proof (Qsq_nonneg a) as Haa.
  assert (Hg0 : 0 <= a * a / inject_Z (Z.of_nat (S N))).
  { apply Qle_shift_div_l; [ apply exp1_pos_denom | lra ]. }
  set (B := 1 / qpow (1 - a / inject_Z (Z.of_nat (S k0))) (S k0)) in *.
  set (g := a * a / inject_Z (Z.of_nat (S N))) in *.
  set (gn := a * a / inject_Z (Z.of_nat (S n))) in *.
  set (gm := a * a / inject_Z (Z.of_nat (S m))) in *.
  set (Dm := expt_process (- a) m) in *. set (Dn := expt_process (- a) n) in *.
  set (Em := expt_process a m) in *. set (En := expt_process a n) in *.
  assert (HB0 : 0 <= B) by lra.
  assert (Hbn : B * gn <= B * g) by (apply qmul_le_l; assumption).
  assert (Hbm : B * gm <= B * g) by (apply qmul_le_l; assumption).
  assert (HgapE : Qabs (En - Em) <= B * g).
  { apply Qabs_Qle_condition. split; lra. }
  set (cm := Dm * Em) in *. set (cn := Dn * En) in *.
  assert (Hid : (Dm - Dn) * (Em * En) == (cm - cn) * En + cn * (En - Em))
    by (unfold cm, cn; ring).
  assert (H1 : Qabs ((cm - cn) * En) <= g * B).
  { apply Qabs_mul_bound.
    - apply Qabs_Qle_condition. split; lra.
    - rewrite Qabs_pos; lra. }
  assert (H2 : Qabs (cn * (En - Em)) <= 1 * (B * g)).
  { apply Qabs_mul_bound.
    - rewrite Qabs_pos; lra.
    - exact HgapE. }
  assert (H3 : Qabs ((Dm - Dn) * (Em * En)) <= g * B + 1 * (B * g)).
  { rewrite Hid. eapply Qle_trans; [ apply Qabs_triangle | ]. lra. }
  assert (HEE : 1 <= Em * En).
  { apply Qle_trans with (1 * En); [ lra | apply Qmult_le_compat_r; lra ]. }
  assert (H4 : Qabs (Dm - Dn) <= Qabs ((Dm - Dn) * (Em * En))).
  { rewrite Qabs_Qmult, (Qabs_pos (Em * En)) by lra.
    pose proof (Qabs_nonneg (Dm - Dn)) as H0.
    apply Qle_trans with (Qabs (Dm - Dn) * 1); [ lra | apply qmul_le_l; assumption ]. }
  assert (E : 2 * B * g == g * B + 1 * (B * g)) by ring.
  rewrite E. eapply Qle_trans; [ exact H4 | exact H3 ].
Qed.

Theorem expt_process_neg_is_Cauchy : forall a, 0 <= a -> is_Cauchy (expt_process (- a)).
Proof.
  intros a Ha eps Heps.
  destruct (ladder_archimedean a 1 ltac:(lra)) as [K0 HK0].
  assert (Hk0 : a < inject_Z (Z.of_nat (S K0))).
  { eapply Qlt_le_trans; [ | apply (inj_le K0 (S K0)); lia ].
    assert (E : inject_Z (Z.of_nat K0) * 1 == inject_Z (Z.of_nat K0)) by ring.
    rewrite <- E. exact HK0. }
  set (B := 1 / qpow (1 - a / inject_Z (Z.of_nat (S K0))) (S K0)).
  destruct (ladder_archimedean (2 * B * (a * a)) eps Heps) as [K1 HK1].
  exists (Nat.max K0 K1). intros m n Hm Hn.
  eapply Qle_lt_trans.
  - apply (expt_neg_modulus a K0 Ha Hk0 (Nat.max K0 K1) m n);
      [ lia | exact Hm | exact Hn ].
  - fold B.
    pose proof (exp1_pos_denom (Nat.max K0 K1)) as Hd.
    pose proof (inj_le K1 (S (Nat.max K0 K1)) ltac:(lia)) as Hle.
    set (d := inject_Z (Z.of_nat (S (Nat.max K0 K1)))) in *.
    set (k1 := inject_Z (Z.of_nat K1)) in *.
    assert (E : 2 * B * (a * a / d) == 2 * B * (a * a) / d) by (field; lra).
    rewrite E. apply Qlt_shift_div_r; [ exact Hd | ].
    assert (Hmul : k1 * eps <= d * eps) by (apply Qmult_le_compat_r; lra).
    rewrite (Qmult_comm eps d). lra.
Qed.

(** The ladder (1 + s/n)^n is a Cauchy process for every rational s. *)
Theorem expt_process_is_Cauchy_all : forall s, is_Cauchy (expt_process s).
Proof.
  intro s. destruct (Qlt_le_dec s 0) as [Hneg | Hpos].
  - apply (is_Cauchy_ext (expt_process (- (- s)))).
    + intro n. unfold expt_process. apply qpow_wd.
      setoid_replace (- - s) with s by ring. reflexivity.
    + apply expt_process_neg_is_Cauchy. lra.
  - apply expt_process_is_Cauchy. exact Hpos.
Qed.

(** The Euler trajectories of y' = L y at the moment t, indexed by the number of
    steps, form a Cauchy process — for every rational L, t, y0. *)
Theorem linear_euler_at_time_is_Cauchy : forall L t y0,
  is_Cauchy (fun k => euler_method (fun _ y => L * y) 0 y0
                        (t / inject_Z (Z.of_nat (S k))) (S k)).
Proof.
  intros L t y0.
  apply (cauchy_scale_ext y0 (expt_process (L * t))).
  - intro k. apply linear_euler_at_time.
  - apply expt_process_is_Cauchy_all.
Qed.

(* ===================================================================== *)
(*  4. Decay y' = -alpha y                                                 *)
(* ===================================================================== *)

(** The Euler method with the right-hand side [decay_rhs alpha] gives the
    process of factors y0 (1 - alpha h)^n. *)
Lemma decay_euler_closed : forall alpha t0 y0 h n,
  euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n
  == y0 * Qpow (1 - alpha * h) n.
Proof.
  intros alpha t0 y0 h n. induction n as [|k IH].
  - simpl. ring.
  - rewrite euler_method_succ. unfold euler_step, decay_rhs.
    rewrite IH. cbn [Qpow]. ring.
Qed.

Lemma decay_euler_is_gronwall : forall alpha t0 y0 h n,
  euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n
  == gronwall_iterate (- alpha) 0 h y0 n.
Proof.
  intros alpha t0 y0 h n. rewrite decay_euler_closed, gronwall_beta_zero.
  apply Qmult_comp; [ reflexivity | ].
  apply Qpow_compat. ring.
Qed.

(** Decay from step to step: 0 <= 1 - alpha h <= 1 and a nonnegative start. *)
Theorem decay_euler_monotone : forall alpha t0 y0 h n,
  0 <= 1 - alpha * h -> 1 - alpha * h <= 1 -> 0 <= y0 ->
  euler_method (fun _ y => decay_rhs alpha y) t0 y0 h (S n)
  <= euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n.
Proof.
  intros alpha t0 y0 h n H0 H1 Hy.
  rewrite !decay_euler_is_gronwall.
  assert (E : 1 + - alpha * h == 1 - alpha * h) by ring.
  apply gronwall_iterate_decay_monotone; [ rewrite E; exact H0 | rewrite E; exact H1 | exact Hy ].
Qed.

Theorem decay_euler_bounded : forall alpha t0 y0 h n,
  0 <= 1 - alpha * h -> 1 - alpha * h <= 1 -> 0 <= y0 ->
  euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n <= y0.
Proof.
  intros alpha t0 y0 h n H0 H1 Hy.
  rewrite decay_euler_is_gronwall.
  assert (E : 1 + - alpha * h == 1 - alpha * h) by ring.
  apply gronwall_iterate_decay; [ rewrite E; exact H0 | rewrite E; exact H1 | exact Hy ].
Qed.

(** Without a condition on the sign of the start: the absolute value decays. *)
Theorem decay_euler_abs_monotone : forall alpha t0 y0 h n,
  Qabs (1 - alpha * h) <= 1 ->
  Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h (S n))
  <= Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n).
Proof.
  intros alpha t0 y0 h n Hr.
  rewrite !decay_euler_is_gronwall.
  apply gronwall_iterate_abs_monotone.
  assert (E : 1 + - alpha * h == 1 - alpha * h) by ring.
  rewrite E. exact Hr.
Qed.

Theorem decay_euler_abs_bounded : forall alpha t0 y0 h n,
  Qabs (1 - alpha * h) <= 1 ->
  Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n) <= Qabs y0.
Proof.
  intros alpha t0 y0 h n Hr.
  rewrite decay_euler_is_gronwall.
  apply gronwall_iterate_abs_decay.
  assert (E : 1 + - alpha * h == 1 - alpha * h) by ring.
  rewrite E. exact Hr.
Qed.

(** With the factor strictly inside (-1, 1) the trajectory vanishes. *)
Theorem decay_euler_vanishes : forall alpha t0 y0 h,
  Qabs (1 - alpha * h) < 1 ->
  forall eps, 0 < eps -> exists N : nat, forall n, (N <= n)%nat ->
    Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n) < eps.
Proof.
  intros alpha t0 y0 h Hr eps Heps.
  assert (E : 1 + - alpha * h == 1 - alpha * h) by ring.
  assert (Hr' : Qabs (1 + - alpha * h) < 1) by (rewrite E; exact Hr).
  destruct (gronwall_iterate_vanishes (- alpha) h y0 Hr' eps Heps) as [N HN].
  exists N. intros n Hn. rewrite decay_euler_is_gronwall. apply HN. exact Hn.
Qed.

(** The moment t reached in k+1 steps: the stage of the ladder (1 - alpha t/n)^n. *)
Theorem decay_euler_at_time : forall alpha t y0 k,
  euler_method (fun _ y => decay_rhs alpha y) 0 y0
               (t / inject_Z (Z.of_nat (S k))) (S k)
  == y0 * expt_process (- (alpha * t)) k.
Proof.
  intros alpha t y0 k. rewrite decay_euler_closed. unfold expt_process.
  rewrite <- qpow_is_Qpow.
  pose proof (exp1_pos_denom k) as Hd.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (E : 1 - alpha * (t / d) == 1 + - (alpha * t) / d) by (field; lra).
  rewrite (qpow_wd _ _ (S k) E). reflexivity.
Qed.

Theorem decay_euler_at_time_is_Cauchy : forall alpha t y0,
  is_Cauchy (fun k => euler_method (fun _ y => decay_rhs alpha y) 0 y0
                        (t / inject_Z (Z.of_nat (S k))) (S k)).
Proof.
  intros alpha t y0.
  apply (cauchy_scale_ext y0 (expt_process (- (alpha * t)))).
  - intro k. apply decay_euler_at_time.
  - apply expt_process_is_Cauchy_all.
Qed.

(** At the moment t the decaying trajectory with a nonnegative start stays
    between y0 (1 - alpha t) and y0 (grids with k + 1 >= alpha t). *)
Theorem decay_euler_at_time_bounds : forall alpha t y0 k,
  0 <= alpha * t -> alpha * t <= inject_Z (Z.of_nat (S k)) -> 0 <= y0 ->
  y0 * (1 - alpha * t)
    <= euler_method (fun _ y => decay_rhs alpha y) 0 y0
                    (t / inject_Z (Z.of_nat (S k))) (S k)
  /\ euler_method (fun _ y => decay_rhs alpha y) 0 y0
                  (t / inject_Z (Z.of_nat (S k))) (S k) <= y0.
Proof.
  intros alpha t y0 k Ha Hk Hy.
  rewrite decay_euler_at_time.
  destruct (expt_neg_bounds (alpha * t) k Ha Hk) as [Hlo [Hhi _]].
  set (D := expt_process (- (alpha * t)) k) in *.
  split.
  - apply qmul_le_l; assumption.
  - apply Qle_trans with (y0 * 1); [ apply qmul_le_l; assumption | lra ].
Qed.

(* ===================================================================== *)
(*  5. The examples under the Lipschitz condition alone                    *)
(* ===================================================================== *)

(** The right-hand sides y, -alpha y, L y are not bounded on Q, so the
    theorem with the boundedness premise does not apply to them; the theorem
    without it does. *)
Theorem exp_picard_cauchy : forall y0 h, 0 <= h -> h < 1 ->
  CauchyReal.is_cauchy (euler_picard_process exp_rhs y0 h).
Proof.
  intros y0 h Hh Hh1.
  apply (euler_picard_cauchy_lip exp_rhs y0 h 1);
    [ exact Hh | apply exp_rhs_lipschitz | lra ].
Qed.

Theorem decay_picard_cauchy : forall alpha y0 h, 0 < alpha -> 0 <= h -> alpha * h < 1 ->
  CauchyReal.is_cauchy (euler_picard_process (decay_rhs alpha) y0 h).
Proof.
  intros alpha y0 h Ha Hh Hc.
  apply (euler_picard_cauchy_lip (decay_rhs alpha) y0 h alpha);
    [ exact Hh | apply decay_rhs_lipschitz; exact Ha | exact Hc ].
Qed.

Theorem linear_picard_cauchy : forall L y0 h, 0 < L -> 0 <= h -> L * h < 1 ->
  CauchyReal.is_cauchy (euler_picard_process (linear_rhs L) y0 h).
Proof.
  intros L y0 h HL Hh Hc.
  apply (euler_picard_cauchy_lip (linear_rhs L) y0 h L);
    [ exact Hh | apply linear_rhs_lipschitz; exact HL | exact Hc ].
Qed.

(* ===================================================================== *)
(*  6. Systems: reduction of order                                         *)
(* ===================================================================== *)

(** In the reduced system the position satisfies the difference equation of the
    SECOND order:  y_{k+2} - 2 y_{k+1} + y_k = h^2 g(t_k, y_k, v_k). *)
Lemma order2_second_difference : forall g h y0 v0 k,
  fst (order2_euler g h y0 v0 (S (S k)))
    - 2 * fst (order2_euler g h y0 v0 (S k))
    + fst (order2_euler g h y0 v0 k)
  == h * h * g (tg h k) (fst (order2_euler g h y0 v0 k))
                         (snd (order2_euler g h y0 v0 k)).
Proof.
  intros g h y0 v0 k. unfold order2_euler.
  rewrite (sys_euler_fst_S _ _ h y0 v0 (S k)).
  rewrite (sys_euler_snd_S _ _ h y0 v0 k).
  rewrite (sys_euler_fst_S _ _ h y0 v0 k).
  ring.
Qed.

(* ===================================================================== *)
(*  7. The oscillator: the law of the grid energy                          *)
(* ===================================================================== *)

Definition sho_E (h y0 v0 : Q) (n : nat) : Q :=
  fst (sho_euler h y0 v0 n) * fst (sho_euler h y0 v0 n)
  + snd (sho_euler h y0 v0 n) * snd (sho_euler h y0 v0 n).

Lemma sho_fst_S : forall h y0 v0 k,
  fst (sho_euler h y0 v0 (S k))
  == fst (sho_euler h y0 v0 k) + h * snd (sho_euler h y0 v0 k).
Proof. intros. unfold sho_euler. apply order2_position_step. Qed.

Lemma sho_snd_S : forall h y0 v0 k,
  snd (sho_euler h y0 v0 (S k))
  == snd (sho_euler h y0 v0 k) - h * fst (sho_euler h y0 v0 k).
Proof.
  intros. unfold sho_euler, order2_euler.
  rewrite sys_euler_snd_S. ring.
Qed.

(** Every step of explicit Euler multiplies the energy exactly by 1 + h^2. *)
Theorem sho_energy_step : forall h y0 v0 k,
  sho_E h y0 v0 (S k) == (1 + h * h) * sho_E h y0 v0 k.
Proof.
  intros h y0 v0 k. unfold sho_E.
  rewrite sho_fst_S, sho_snd_S. ring.
Qed.

Theorem sho_energy_closed : forall h y0 v0 n,
  sho_E h y0 v0 n == Qpow (1 + h * h) n * sho_E h y0 v0 0.
Proof.
  intros h y0 v0 n. induction n as [|k IH].
  - cbn [Qpow]. ring.
  - rewrite sho_energy_step, IH. cbn [Qpow]. ring.
Qed.

Lemma sho_E_0 : forall h y0 v0, sho_E h y0 v0 0 == y0 * y0 + v0 * v0.
Proof. intros. unfold sho_E. cbn. reflexivity. Qed.

Lemma sho_E_nonneg : forall h y0 v0 n, 0 <= sho_E h y0 v0 n.
Proof.
  intros h y0 v0 n. unfold sho_E.
  pose proof (Qsq_nonneg (fst (sho_euler h y0 v0 n))).
  pose proof (Qsq_nonneg (snd (sho_euler h y0 v0 n))).
  lra.
Qed.

(** The grid energy never decreases, whatever the step. *)
Lemma sho_energy_nondecreasing : forall h y0 v0 k,
  sho_E h y0 v0 k <= sho_E h y0 v0 (S k).
Proof.
  intros h y0 v0 k. rewrite sho_energy_step.
  pose proof (sho_E_nonneg h y0 v0 k) as H0.
  pose proof (Qsq_nonneg h) as Hh.
  assert (Hinc : 0 <= (h * h) * sho_E h y0 v0 k)
    by (apply Qmult_le_0_compat; assumption).
  setoid_replace ((1 + h * h) * sho_E h y0 v0 k)
    with (sho_E h y0 v0 k + (h * h) * sho_E h y0 v0 k) by ring.
  lra.
Qed.

Lemma sho_energy_ge_start : forall h y0 v0 n,
  sho_E h y0 v0 0 <= sho_E h y0 v0 n.
Proof.
  intros h y0 v0 n. induction n as [|k IH].
  - apply Qle_refl.
  - eapply Qle_trans; [ exact IH | apply sho_energy_nondecreasing ].
Qed.

(** The drift is strict at every step for a nonzero step h and a nonzero start. *)
Theorem sho_energy_strict : forall h y0 v0 k,
  ~ h == 0 -> 0 < sho_E h y0 v0 0 ->
  sho_E h y0 v0 k < sho_E h y0 v0 (S k).
Proof.
  intros h y0 v0 k Hh H0.
  pose proof (Qsq_pos h Hh) as Hhh.
  assert (Hk : 0 < sho_E h y0 v0 k).
  { rewrite sho_energy_closed. apply Qmult_lt_0_compat; [ | exact H0 ].
    apply Qpow_pos. lra. }
  rewrite sho_energy_step.
  assert (Hinc : 0 < (h * h) * sho_E h y0 v0 k)
    by (apply Qmult_lt_0_compat; assumption).
  setoid_replace ((1 + h * h) * sho_E h y0 v0 k)
    with (sho_E h y0 v0 k + (h * h) * sho_E h y0 v0 k) by ring.
  lra.
Qed.

(** The example of the chapter is a case of the law: (1 + 1/100)^2 = 10201/10000. *)
Lemma sho_energy2_from_law : sho_E (1 # 10) 1 0 2 == 10201 # 10000.
Proof.
  rewrite sho_energy_closed, sho_E_0. vm_compute. reflexivity.
Qed.

(** The sign of the velocity: from (y, v) = (1, 0) the first step gives v_1 = -h. *)
Lemma sho_v1 : forall h, snd (sho_euler h 1 0 1) == - h.
Proof. intro h. rewrite sho_snd_S. cbn. ring. Qed.

(* ===================================================================== *)
(*  8. The drift of the energy at a fixed moment vanishes under refinement *)
(* ===================================================================== *)

(** If 2 n x <= 1 then (1 + x)^n <= 1 + 2 n x. *)
Lemma qpow_drift_bound : forall x n, 0 <= x ->
  2 * (inject_Z (Z.of_nat n) * x) <= 1 ->
  qpow (1 + x) n <= 1 + 2 * (inject_Z (Z.of_nat n) * x).
Proof.
  intros x n Hx Hs.
  pose proof (qpow_bernoulli_upper x n Hx) as Hb.
  pose proof (inj_nonneg n) as Hn.
  set (m := inject_Z (Z.of_nat n)) in *.
  assert (Hs0 : 0 <= m * x) by (apply Qmult_le_0_compat; assumption).
  set (s := m * x) in *.
  set (P := qpow (1 + x) n) in *.
  assert (Hpos : 0 < 1 - s) by lra.
  apply (proj1 (Qmult_le_r _ _ (1 - s) Hpos)).
  apply Qle_trans with 1; [ exact Hb | ].
  assert (Hq : 0 <= s * (1 - 2 * s)) by (apply Qmult_le_0_compat; lra).
  assert (E : (1 + 2 * s) * (1 - s) == 1 + s * (1 - 2 * s)) by ring.
  rewrite E. lra.
Qed.

(** At the moment t reached in k+1 steps (k + 1 >= 2 t^2) the energy exceeds
    the initial one by at most 2 t^2/(k+1) of it. *)
Theorem sho_energy_at_time_drift : forall t y0 v0 k,
  2 * (t * t) <= inject_Z (Z.of_nat (S k)) ->
  sho_E (t / inject_Z (Z.of_nat (S k))) y0 v0 (S k) - (y0 * y0 + v0 * v0)
  <= 2 * (t * t / inject_Z (Z.of_nat (S k))) * (y0 * y0 + v0 * v0).
Proof.
  intros t y0 v0 k Hk.
  pose proof (exp1_pos_denom k) as Hd.
  rewrite sho_energy_closed, sho_E_0, <- qpow_is_Qpow.
  pose proof (qpow_drift_bound
                (t / inject_Z (Z.of_nat (S k)) * (t / inject_Z (Z.of_nat (S k))))
                (S k)) as Hb.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (Hx : 0 <= t / d * (t / d)) by apply Qsq_nonneg.
  assert (Es : d * (t / d * (t / d)) == t * t / d) by (field; lra).
  assert (E2 : 2 * (t * t / d) == 2 * (t * t) / d) by (field; lra).
  assert (Hs : 2 * (d * (t / d * (t / d))) <= 1).
  { rewrite Es, E2. apply Qle_shift_div_r; [ exact Hd | lra ]. }
  specialize (Hb Hx Hs). rewrite Es in Hb.
  assert (HE0 : 0 <= y0 * y0 + v0 * v0).
  { pose proof (Qsq_nonneg y0). pose proof (Qsq_nonneg v0). lra. }
  set (E0 := y0 * y0 + v0 * v0) in *.
  set (P := qpow (1 + t / d * (t / d)) (S k)) in *.
  set (g := t * t / d) in *.
  assert (Hm : P * E0 <= (1 + 2 * g) * E0) by (apply Qmult_le_compat_r; assumption).
  assert (E : (1 + 2 * g) * E0 == E0 + 2 * g * E0) by ring.
  lra.
Qed.

(** Exact conservation as the role-limit: at a fixed moment t the drift of the
    energy becomes smaller than any eps once the grid is fine enough. *)
Theorem sho_energy_drift_vanishes : forall t y0 v0 eps, 0 < eps ->
  exists N : nat, forall k, (N <= k)%nat ->
    0 <= sho_E (t / inject_Z (Z.of_nat (S k))) y0 v0 (S k) - (y0 * y0 + v0 * v0)
    /\ sho_E (t / inject_Z (Z.of_nat (S k))) y0 v0 (S k) - (y0 * y0 + v0 * v0) < eps.
Proof.
  intros t y0 v0 eps Heps.
  destruct (ladder_archimedean (2 * (t * t)) 1 ltac:(lra)) as [K1 HK1].
  destruct (ladder_archimedean (2 * (t * t) * (y0 * y0 + v0 * v0)) eps Heps) as [K2 HK2].
  exists (Nat.max K1 K2). intros k Hk.
  pose proof (exp1_pos_denom k) as Hd.
  pose proof (inj_le K1 (S k) ltac:(lia)) as H1.
  pose proof (inj_le K2 (S k) ltac:(lia)) as H2.
  pose proof (sho_energy_ge_start (t / inject_Z (Z.of_nat (S k))) y0 v0 (S k)) as Hlo.
  rewrite sho_E_0 in Hlo.
  pose proof (sho_energy_at_time_drift t y0 v0 k) as Hup.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  set (k1 := inject_Z (Z.of_nat K1)) in *.
  set (k2 := inject_Z (Z.of_nat K2)) in *.
  set (E0 := y0 * y0 + v0 * v0) in *.
  set (En := sho_E (t / d) y0 v0 (S k)) in *.
  split; [ lra | ].
  eapply Qle_lt_trans; [ apply Hup; lra | ].
  assert (E : 2 * (t * t / d) * E0 == 2 * (t * t) * E0 / d) by (field; lra).
  rewrite E. apply Qlt_shift_div_r; [ exact Hd | ].
  assert (Hmul : k2 * eps <= d * eps) by (apply Qmult_le_compat_r; lra).
  rewrite (Qmult_comm eps d). lra.
Qed.

Print Assumptions expt_process_is_Cauchy_all.
Print Assumptions sho_energy_drift_vanishes.
