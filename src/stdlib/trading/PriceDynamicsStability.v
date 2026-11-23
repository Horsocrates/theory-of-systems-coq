(** * PriceDynamicsStability.v — Price dynamics: what the threshold checks say about
      trajectories (Part VIII, chapter 5)

    Elements: prices p_n, a target price, a rate alpha, deviations p_n - target —
              rational numbers at every finite step; lists of external forces.
    Roles:    1 - alpha = factor by which one step of mean reversion multiplies
              the deviation; |1 - alpha| = Lipschitz coefficient of the step map;
              [lipschitz_check] / [stability_signal] = threshold tests of a number;
              target = fixed point of the step map.
    Rules:    additive dynamics p_{n+1} = p_n + f_n keeps the distance between two
              trajectories (coefficient exactly 1, no contraction); mean reversion
              p_{n+1} = p_n + alpha (target - p_n) multiplies the deviation by
              1 - alpha, so the coefficient |1 - alpha| decides: <= 1 — the
              deviation does not grow, < 1 — it vanishes, > 1 — it grows.

    ============ E/R/R разбор ============
      Rules (L5): шаг цены; шаг возврата к среднему — отображение с коэффициентом
                  Липшица |1 - alpha|; пороговые проверки числа.
      Roles (L4): коэффициент |1 - alpha| — роль-темп сближения с целью; цель —
                  роль-неподвижная точка; проверка — роль-признак.
      Elements  : рациональные цены и отклонения на каждом конечном шаге (L1 + P4).
    ДИАГНОСТИКА P4: утверждения — о конечных шагах n и рациональных ценах; «сходится
    к цели» записано как «отклонение меньше любого eps, начиная с некоторого шага».

    PROVED (all closed under the global context):
      - additive dynamics: the trajectory is the start plus the sum of forces;
        two trajectories under the same forces keep their distance
        ([price_trajectory_sum], [price_traj_shift]); all stages of the example
        of the chapter ([price_history_ex]); the price step is an Euler step;
      - the checks of PriceDynamicsODE.v are threshold tests:
        [lipschitz_check L = true <-> L <= 1], [stability_signal L <> -1 <-> L < 1];
      - mean reversion: closed form of the deviation ([mr_deviation]), the step
        map is Lipschitz with the coefficient |1 - alpha| ([mr_step_lipschitz]),
        which is exactly the [lipschitz_ratio] of the step ([mr_lipschitz_ratio]);
        the check implies that the deviation does not grow ([mr_stable_by_check]);
        the signal implies that the trajectory comes to the target
        ([mr_converges_by_signal]); at the threshold |1 - alpha| = 1 the check
        passes, yet the deviation keeps its size ([mr_marginal_no_convergence]);
        beyond the threshold it grows ([mr_unstable_grows]);
      - the step map is a contraction in the sense of FixedPoint.v
        ([mr_map_is_contraction]) with the target as its fixed point; the
        deviation is the homogeneous Gronwall iteration with the rate -alpha
        ([mr_deviation_is_gronwall]) — the decay equation of the chapter.

    NOT claimed: any statement about real markets; stability of the additive
    dynamics under a price-dependent force other than mean reversion.

    STATUS: 32 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith List Bool Lia Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import FixedPoint.
From ToS Require Import process.ProcessPicard.
From ToS Require Import process.ProcessGronwall.
From ToS Require Import process.ProcessODE.
From ToS Require Import stdlib.trading.PriceDynamicsODE.
Import ListNotations.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. Helpers                                                             *)
(* ===================================================================== *)

Lemma Qabs_eq0 : forall x : Q, Qabs x == 0 -> x == 0.
Proof.
  intros x H.
  assert (H1 : Qabs x <= 0) by (rewrite H; apply Qle_refl).
  apply Qabs_Qle_condition in H1. destruct H1 as [Ha Hb].
  apply Qle_antisym; [ exact Hb | lra ].
Qed.

Lemma Qabs_Qpow : forall r n, Qabs (Qpow r n) == Qpow (Qabs r) n.
Proof.
  intros r n. induction n as [|k IH].
  - reflexivity.
  - cbn [Qpow]. rewrite Qabs_Qmult, IH. reflexivity.
Qed.

(* ===================================================================== *)
(*  1. Additive dynamics p_{n+1} = p_n + f_n                               *)
(* ===================================================================== *)

Lemma price_trajectory_sum : forall forces p,
  price_trajectory p forces == p + fold_right Qplus 0 forces.
Proof.
  induction forces as [|f rest IH]; intro p.
  - simpl. ring.
  - simpl. rewrite IH. unfold price_step. ring.
Qed.

(** Two trajectories under the same forces keep their distance: the coefficient
    of the step p |-> p + f with respect to the price is exactly one. *)
Lemma price_traj_shift : forall forces p q,
  price_trajectory p forces - price_trajectory q forces == p - q.
Proof.
  intros forces p q. rewrite !price_trajectory_sum. ring.
Qed.

(** All the stages of the example of the chapter in one statement. *)
Lemma price_history_ex :
  map Qred (price_history p0_ex forces_ex)
  = [100; 101; 201 # 2; 405 # 4; 101; 203 # 2].
Proof. vm_compute. reflexivity. Qed.

(** The price step is an Euler step with the step 1 and a right-hand side that
    does not depend on the price. *)
Lemma price_step_is_euler_step : forall p f t,
  price_step p f == euler_step (fun _ _ => f) t p 1.
Proof. intros. unfold price_step, euler_step. ring. Qed.

(* ===================================================================== *)
(*  2. The checks of PriceDynamicsODE.v are threshold tests of a number    *)
(* ===================================================================== *)

Lemma lipschitz_check_spec : forall L, lipschitz_check L = true <-> L <= 1.
Proof. intro L. unfold lipschitz_check. apply Qle_bool_iff. Qed.

Lemma lipschitz_check_at_one : lipschitz_check 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stability_signal_at_one : stability_signal 1 = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

(** The signal differs from "unstable" exactly when the number is below one. *)
Lemma stability_signal_spec : forall L, stability_signal L <> (-1)%Z <-> L < 1.
Proof.
  intro L. unfold stability_signal.
  destruct (Qlt_le_dec L (1 # 2)) as [H1 | H1].
  - split; [ intros _ | intros _; discriminate ].
    apply Qlt_trans with (1 # 2); [ exact H1 | reflexivity ].
  - destruct (Qlt_le_dec L 1) as [H2 | H2].
    + split; [ intros _; exact H2 | intros _; discriminate ].
    + split; [ intro H; exfalso; apply H; reflexivity | intro H ].
      exfalso. apply (Qlt_irrefl L). eapply Qlt_le_trans; [ exact H | exact H2 ].
Qed.

(** With coinciding abscissas the ratio is zero (division by zero in Q gives 0),
    and the signal reads "strongly stable". *)
Lemma lipschitz_ratio_degenerate : forall x y1 y2, lipschitz_ratio x y1 x y2 == 0.
Proof.
  intros x y1 y2. unfold lipschitz_ratio.
  assert (E : Qabs (x - x) == 0).
  { setoid_replace (x - x) with 0 by ring. reflexivity. }
  unfold Qdiv. rewrite E. change (/ 0) with 0. ring.
Qed.

Lemma stability_signal_degenerate :
  stability_signal (lipschitz_ratio 1 0 1 100) = 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  3. Mean reversion: the deviation is multiplied by 1 - alpha            *)
(* ===================================================================== *)

(** The step map of mean reversion. *)
Definition mr_map (target alpha p : Q) : Q := p + mean_reverting_force p target alpha.

Lemma mr_trajectory_is_iterate : forall p0 target alpha n,
  mr_trajectory p0 target alpha n = iterate (mr_map target alpha) p0 n.
Proof.
  intros p0 target alpha n. induction n as [|k IH]; [ reflexivity | ].
  cbn [mr_trajectory iterate]. cbv zeta. rewrite IH. reflexivity.
Qed.

Lemma mr_map_fixed : forall target alpha, mr_map target alpha target == target.
Proof. intros. unfold mr_map, mean_reverting_force. ring. Qed.

Lemma mr_step : forall p0 target alpha n,
  mr_trajectory p0 target alpha (S n) - target
  == (1 - alpha) * (mr_trajectory p0 target alpha n - target).
Proof.
  intros. cbn [mr_trajectory]. cbv zeta. unfold mean_reverting_force. ring.
Qed.

Theorem mr_deviation : forall p0 target alpha n,
  mr_trajectory p0 target alpha n - target
  == (p0 - target) * Qpow (1 - alpha) n.
Proof.
  intros p0 target alpha n. induction n as [|k IH].
  - cbn [mr_trajectory Qpow]. ring.
  - rewrite mr_step, IH. cbn [Qpow]. ring.
Qed.

Theorem mr_abs_deviation : forall p0 target alpha n,
  Qabs (mr_trajectory p0 target alpha n - target)
  == Qabs (p0 - target) * Qpow (Qabs (1 - alpha)) n.
Proof.
  intros. rewrite mr_deviation, Qabs_Qmult, Qabs_Qpow. reflexivity.
Qed.

(** The step of mean reversion is a Lipschitz map with the coefficient |1 - alpha|. *)
Lemma mr_step_lipschitz : forall p q target alpha,
  Qabs ((p + mean_reverting_force p target alpha)
        - (q + mean_reverting_force q target alpha))
  == Qabs (1 - alpha) * Qabs (p - q).
Proof.
  intros. unfold mean_reverting_force. rewrite <- Qabs_Qmult.
  apply Qabs_wd. ring.
Qed.

(** That coefficient is exactly the [lipschitz_ratio] of the step, computed on
    any two distinct prices. *)
Lemma mr_lipschitz_ratio : forall p q target alpha, ~ p == q ->
  lipschitz_ratio p (p + mean_reverting_force p target alpha)
                  q (q + mean_reverting_force q target alpha)
  == Qabs (1 - alpha).
Proof.
  intros p q target alpha Hpq. unfold lipschitz_ratio.
  rewrite (mr_step_lipschitz q p target alpha).
  assert (Hne : ~ Qabs (q - p) == 0).
  { intro H. apply Hpq. apply Qabs_eq0 in H. lra. }
  field. exact Hne.
Qed.

(** Two trajectories with the same target: their distance is multiplied by
    1 - alpha at every step. *)
Theorem mr_two_trajectories : forall p0 q0 target alpha n,
  mr_trajectory p0 target alpha n - mr_trajectory q0 target alpha n
  == (p0 - q0) * Qpow (1 - alpha) n.
Proof.
  intros p0 q0 target alpha n.
  assert (E : mr_trajectory p0 target alpha n - mr_trajectory q0 target alpha n
              == (mr_trajectory p0 target alpha n - target)
                 - (mr_trajectory q0 target alpha n - target)) by ring.
  rewrite E, !mr_deviation. ring.
Qed.

(* ===================================================================== *)
(*  4. What the coefficient decides                                        *)
(* ===================================================================== *)

(** |1 - alpha| <= 1: the deviation does not grow. *)
Theorem mr_stable : forall p0 target alpha n,
  Qabs (1 - alpha) <= 1 ->
  Qabs (mr_trajectory p0 target alpha n - target) <= Qabs (p0 - target).
Proof.
  intros p0 target alpha n Ha. rewrite mr_abs_deviation.
  apply gronwall_decay_factor; [ apply Qabs_nonneg | exact Ha | apply Qabs_nonneg ].
Qed.

Theorem mr_stable_monotone : forall p0 target alpha n,
  Qabs (1 - alpha) <= 1 ->
  Qabs (mr_trajectory p0 target alpha (S n) - target)
  <= Qabs (mr_trajectory p0 target alpha n - target).
Proof.
  intros p0 target alpha n Ha. rewrite mr_step, Qabs_Qmult.
  pose proof (Qabs_nonneg (mr_trajectory p0 target alpha n - target)) as H0.
  apply Qle_trans with (1 * Qabs (mr_trajectory p0 target alpha n - target));
    [ apply Qmult_le_compat_r; assumption | lra ].
Qed.

(** The check of the file, applied to the coefficient of the step, implies that
    the deviation does not grow. *)
Theorem mr_stable_by_check : forall p0 target alpha,
  lipschitz_check (Qabs (1 - alpha)) = true ->
  forall n, Qabs (mr_trajectory p0 target alpha n - target) <= Qabs (p0 - target).
Proof.
  intros p0 target alpha H n. apply mr_stable. apply lipschitz_check_spec. exact H.
Qed.

(** |1 - alpha| < 1: the trajectory comes to the target. *)
Theorem mr_converges : forall p0 target alpha,
  Qabs (1 - alpha) < 1 ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (mr_trajectory p0 target alpha n - target) < eps.
Proof.
  intros p0 target alpha Ha eps Heps.
  set (C := Qabs (p0 - target) + 1).
  assert (HC : 0 < C) by (unfold C; pose proof (Qabs_nonneg (p0 - target)); lra).
  assert (Hec : 0 < eps / C).
  { apply Qlt_shift_div_l; [ exact HC | lra ]. }
  destruct (Qpow_limit_zero (Qabs (1 - alpha)) (Qabs_nonneg _) Ha (eps / C) Hec)
    as [N HN].
  exists N. intros n Hn.
  rewrite mr_abs_deviation.
  assert (Hp0 : 0 <= Qpow (Qabs (1 - alpha)) n)
    by (apply SeriesConvergence.Qpow_nonneg; apply Qabs_nonneg).
  pose proof (HN n Hn) as Hlt.
  set (P := Qpow (Qabs (1 - alpha)) n) in *.
  assert (H1 : Qabs (p0 - target) * P <= C * P).
  { apply Qmult_le_compat_r; [ unfold C; lra | exact Hp0 ]. }
  assert (H2 : C * P < C * (eps / C)).
  { apply Qmult_lt_l; assumption. }
  assert (H3 : C * (eps / C) == eps) by (field; lra).
  lra.
Qed.

(** The signal of the file, applied to the coefficient of the step: anything but
    "unstable" implies that the trajectory comes to the target. *)
Theorem mr_converges_by_signal : forall p0 target alpha,
  stability_signal (Qabs (1 - alpha)) <> (-1)%Z ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (mr_trajectory p0 target alpha n - target) < eps.
Proof.
  intros p0 target alpha H. apply mr_converges. apply stability_signal_spec. exact H.
Qed.

(** The usual range of the rate: 0 < alpha < 1. *)
Corollary mr_converges_rate : forall p0 target alpha,
  0 < alpha -> alpha < 1 ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (mr_trajectory p0 target alpha n - target) < eps.
Proof.
  intros p0 target alpha Ha0 Ha1. apply mr_converges.
  rewrite Qabs_pos; lra.
Qed.

(** At the threshold: for alpha = 2 the coefficient is 1, the check passes, and
    the deviation keeps its size — it neither grows nor vanishes. *)
Lemma mr_check_passes_at_two : lipschitz_check (Qabs (1 - 2)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem mr_marginal_no_convergence : forall p0 target n,
  Qabs (mr_trajectory p0 target 2 n - target) == Qabs (p0 - target).
Proof.
  intros p0 target n. rewrite mr_abs_deviation.
  assert (E : Qabs (1 - 2) == 1) by reflexivity.
  rewrite (Qpow_compat _ _ n E), Qpow_1. ring.
Qed.

(** Beyond the threshold the deviation strictly grows at every step. *)
Theorem mr_unstable_grows : forall p0 target alpha n,
  1 < Qabs (1 - alpha) -> ~ p0 == target ->
  Qabs (mr_trajectory p0 target alpha n - target)
  < Qabs (mr_trajectory p0 target alpha (S n) - target).
Proof.
  intros p0 target alpha n Hr Hne.
  assert (Hd0 : 0 < Qabs (p0 - target)).
  { pose proof (Qabs_nonneg (p0 - target)) as H0.
    destruct (Qlt_le_dec 0 (Qabs (p0 - target))) as [H | H]; [ exact H | ].
    exfalso. apply Hne.
    assert (Hz : Qabs (p0 - target) == 0) by (apply Qle_antisym; assumption).
    apply Qabs_eq0 in Hz. lra. }
  assert (Hdn : 0 < Qabs (mr_trajectory p0 target alpha n - target)).
  { rewrite mr_abs_deviation. apply Qmult_lt_0_compat; [ exact Hd0 | ].
    apply Qpow_pos. lra. }
  rewrite mr_step, Qabs_Qmult.
  set (r := Qabs (1 - alpha)) in *.
  set (D := Qabs (mr_trajectory p0 target alpha n - target)) in *.
  assert (Hinc : 0 < (r - 1) * D) by (apply Qmult_lt_0_compat; lra).
  setoid_replace (r * D) with (D + (r - 1) * D) by ring. lra.
Qed.

(* ===================================================================== *)
(*  5. The same mechanism as in the pure problem                           *)
(* ===================================================================== *)

(** The step map of mean reversion is a contraction in the sense of
    FixedPoint.v on every interval centred at the target. *)
Theorem mr_map_is_contraction : forall target alpha R,
  Qabs (1 - alpha) < 1 -> 0 <= R ->
  is_contraction (mr_map target alpha) (target - R) (target + R) (Qabs (1 - alpha)).
Proof.
  intros target alpha R Hr HR. unfold is_contraction.
  split; [ apply Qabs_nonneg | ]. split; [ exact Hr | ]. split.
  - intros x Hlo Hhi.
    assert (E : mr_map target alpha x - target == (1 - alpha) * (x - target))
      by (unfold mr_map, mean_reverting_force; ring).
    assert (Hb : Qabs (mr_map target alpha x - target) <= R).
    { rewrite E, Qabs_Qmult.
      assert (Hx : Qabs (x - target) <= R) by (apply Qabs_Qle_condition; split; lra).
      pose proof (Qabs_nonneg (x - target)) as H0.
      apply Qle_trans with (1 * Qabs (x - target));
        [ apply Qmult_le_compat_r; [ apply Qlt_le_weak; exact Hr | exact H0 ] | lra ]. }
    apply Qabs_Qle_condition in Hb. destruct Hb as [Ha Hb]. split; lra.
  - intros x y _ _ _ _. unfold mr_map. rewrite mr_step_lipschitz. apply Qle_refl.
Qed.

(** The deviation from the target is the homogeneous Gronwall iteration with the
    rate -alpha and the step 1: mean reversion is the decay equation. *)
Theorem mr_deviation_is_gronwall : forall p0 target alpha n,
  mr_trajectory p0 target alpha n - target
  == gronwall_iterate (- alpha) 0 1 (p0 - target) n.
Proof.
  intros p0 target alpha n. rewrite mr_deviation, gronwall_beta_zero.
  apply Qmult_comp; [ reflexivity | ].
  apply Qpow_compat. ring.
Qed.

(** The trajectory of mean reversion is the Euler method with the step 1 for
    the equation p' = alpha (target - p). *)
Theorem mr_trajectory_is_euler_method : forall p0 target alpha n,
  mr_trajectory p0 target alpha n
  == euler_method (fun _ p => alpha * (target - p)) 0 p0 1 n.
Proof.
  intros p0 target alpha n. induction n as [|k IH]; [ reflexivity | ].
  rewrite euler_method_succ. unfold euler_step. cbv beta. rewrite <- IH.
  cbn [mr_trajectory]. cbv zeta. unfold mean_reverting_force. ring.
Qed.

Print Assumptions mr_converges_by_signal.
Print Assumptions mr_map_is_contraction.
