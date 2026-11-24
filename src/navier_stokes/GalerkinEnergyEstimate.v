(** * GalerkinEnergyEstimate.v — The energy of the Galerkin system in time: the estimate
      E(n) <= E(0) on the trajectory of the explicit scheme under a condition on the
      step that is fixed in advance; without a condition on the step the scheme can
      increase the energy (Part IX, chapter 5)

    Elements: rational amplitudes of the modes k < K on every step; the coupling B;
              the viscosity nu; the step dt; a bound M of the coupling; the initial
              energy E0.
    Roles:    energy_conserving B K = role-rule "the nonlinear term does no work";
              E(a) = role-dissipating quantity; the term (1/2) dt^2 sum F_k^2 of
              the step identity = role-price of the explicit step;
              2 dt nu K^2 <= 1 and 4 dt M^2 K^3 E0 <= nu = role-regime (a condition
              on the step known before the trajectory is computed);
              the sequence u_grow and the step of the example = role-witnesses
              that the premise and the condition cannot be dropped.
    Rules:    E(a + dt F) = E(a) - 2 nu dt Omega(a) + (1/2) dt^2 sum F_k^2 for an
              energy-conserving coupling; sum F_k^2 is bounded through Omega and
              E^2; while E <= E0 the condition on the step makes the second-order
              term smaller than the dissipation, hence E does not grow, hence
              E <= E0 on the next step: induction.

    ============ E/R/R разбор ============
      Rules (L5): тождество шага E(a + dt F) = E(a) − 2 nu dt Omega + (1/2) dt^2
                  sum F_k^2; оценка sum F_k^2 через Omega и E^2; пока E <= E0,
                  условие на шаг делает член второго порядка меньше диссипации —
                  индукция по шагам.
      Roles (L4): energy_conserving — роль-правило «нелинейный член работы не
                  совершает»; член второго порядка — роль-цена явного шага; условие
                  на шаг — роль-режим, известный до вычисления траектории;
                  u_grow и шаг примера — роль-свидетели того, что посылку и условие
                  опустить нельзя.
      Elements  : рациональные амплитуды конечного числа мод на каждом конечном
                  шаге (L1 + P4).
    ДИАГНОСТИКА P4: «E(t) <= E(0)» — «при всяком конечном номере шага n энергия
    состояния после n шагов не больше начальной»; времени как континуума и
    производной по времени в утверждениях нет.

    PROVED (all closed under the global context):
      - for an arbitrary sequence of states the estimate E(n) <= E(0) is false:
        the premise energy_decreasing of EnergyEstimate.v is needed
        ([energy_bound_needs_premise], [u_grow_not_decreasing]);
      - for every energy-conserving coupling: the energy rate along the
        right-hand side and the identity of the step ([conserving_energy_rate],
        [conserving_step_energy]); couplings adv T and the coefficient B_coeff
        are energy-conserving ([adv_energy_conserving],
        [formal_energy_conserving]);
      - without a condition on the step the explicit scheme can increase the
        energy ([galerkin_euler_energy_can_grow]);
      - a bound of the nonlinear term and of sum F_k^2 for a bounded coupling
        ([nl_bound], [rhs_sq_sum_bound]);
      - THE ESTIMATE: for a bounded energy-conserving coupling, under
        2 dt nu K^2 <= 1 and 4 dt M^2 K^3 E(a0) <= nu, the energy does not grow
        from step to step and E(n) <= E(0) for every n
        ([galerkin_traj_energy_apriori], [adv_traj_energy_apriori]) — the premise
        energy_decreasing is proved for the trajectory;
      - the same with a condition checked along the trajectory, without a bound
        of the coupling ([galerkin_traj_energy_bounded]);
      - for the system with the coefficient B_coeff (it is viscous) and for the
        viscous polygon euler_evolve of ResolutionRegularity.v: the energy does
        not grow under a condition on the step ([formal_traj_energy_decreasing],
        [viscous_euler_energy_decreasing]).

    NOT claimed: an estimate without a condition on the step (it is false for the
    explicit scheme); a continuous-time solution or dE/dt as a derivative; an
    estimate uniform in the number of modes K (the condition on the step depends
    on K); that the coefficients of real advection are bounded by a given M.

    STATUS: 30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.
From ToS Require Import navier_stokes.EnergyEstimate.
From ToS Require Import navier_stokes.GalerkinAdvection.
From ToS Require navier_stokes.ResolutionRegularity.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. For an arbitrary sequence of states the premise is needed           *)
(* ===================================================================== *)

Definition u_grow : time_series := fun n => fun _ => inject_Z (Z.of_nat n).

Lemma energy_bound_needs_premise :
  ~ (forall K (u : time_series) n, energy_at K u n <= energy_at K u 0).
Proof.
  intro H. specialize (H 1%nat u_grow 1%nat).
  vm_compute in H. apply H. reflexivity.
Qed.

Lemma u_grow_not_decreasing : ~ energy_decreasing 1 u_grow.
Proof.
  intro H. specialize (H 0%nat). vm_compute in H. apply H. reflexivity.
Qed.

(* ===================================================================== *)
(*  2. Energy-conserving couplings: the rate and the step                  *)
(* ===================================================================== *)

(** The nonlinear term does no work on the modes k < K, for every state. *)
Definition energy_conserving (B : nat -> nat -> nat -> Q) (K : nat) : Prop :=
  forall a : nat -> Q, sum_Q_ns (fun k => a k * nl B K a k) K == 0.

Lemma adv_energy_conserving : forall T K, energy_conserving (adv T) K.
Proof. intros T K a. apply adv_energy_zero. Qed.

(** The coefficient of GalerkinSystem.v conserves energy trivially: its
    nonlinear term is zero in every mode. *)
Lemma formal_energy_conserving : forall (nsc : NSCoupling) K, energy_conserving B_coeff K.
Proof.
  intros nsc K a.
  rewrite (sum_ns_ext (fun k => a k * nl B_coeff K a k) (fun _ => 0) K).
  - apply sum_ns_zero_fn.
  - intros k _. rewrite (nl_Bcoeff_is_inner nsc K a k), (nl_mode_zero nsc K k a). ring.
Qed.

Theorem conserving_energy_rate : forall nu B K (a : nat -> Q),
  energy_conserving B K ->
  sum_Q_ns (fun k => a k * grhs nu B K a k) K == - (2) * nu * modal_enstrophy K a.
Proof.
  intros nu B K a HB. unfold grhs.
  transitivity (sum_Q_ns (fun k => (- nu) * (wgt k * a k * a k)
                                   + a k * nl B K a k) K).
  { apply sum_ns_ext. intros k _. ring. }
  rewrite (sum_ns_add (fun k => (- nu) * (wgt k * a k * a k))
                      (fun k => a k * nl B K a k) K).
  rewrite (sum_ns_scale (- nu) (fun k => wgt k * a k * a k) K).
  rewrite (HB a).
  unfold modal_enstrophy, wgt. ring.
Qed.

Theorem conserving_step_energy : forall nu B K dt (a : nat -> Q),
  energy_conserving B K ->
  modal_energy K (gstep nu B K dt a) ==
  modal_energy K a - 2 * nu * dt * modal_enstrophy K a
  + (1#2) * dt * dt * sum_Q_ns (fun k => grhs nu B K a k * grhs nu B K a k) K.
Proof.
  intros nu B K dt a HB. unfold gstep.
  rewrite (energy_step_identity K a (grhs nu B K a) dt).
  rewrite (conserving_energy_rate nu B K a HB). ring.
Qed.

(** A condition on the step, read off the state, under which the energy does
    not grow over one step. *)
Corollary conserving_step_energy_le : forall nu B K dt (a : nat -> Q),
  energy_conserving B K -> 0 <= dt ->
  dt * sum_Q_ns (fun k => grhs nu B K a k * grhs nu B K a k) K
    <= 4 * nu * modal_enstrophy K a ->
  modal_energy K (gstep nu B K dt a) <= modal_energy K a.
Proof.
  intros nu B K dt a HB Hdt Hcond.
  rewrite (conserving_step_energy nu B K dt a HB).
  set (S := sum_Q_ns (fun k => grhs nu B K a k * grhs nu B K a k) K) in *.
  set (Om := modal_enstrophy K a) in *.
  assert (H : 0 <= dt * (4 * nu * Om - dt * S)).
  { apply Qmult_le_0_compat; lra. }
  lra.
Qed.

(** Without a condition on the step the explicit scheme increases the energy:
    nu = 1/100, dt = 1, two modes, the coupling adv T_pair, the unit state. *)
Lemma galerkin_euler_energy_can_grow :
  modal_energy 2 a_unit < modal_energy 2 (gstep (1#100) (adv T_pair) 2 1 a_unit).
Proof. vm_compute. reflexivity. Qed.

(** The trajectory under a condition checked along it (no bound of the coupling
    is needed): the premise energy_decreasing of EnergyEstimate.v holds. *)
Theorem galerkin_traj_energy_bounded : forall nu B K dt (a0 : modal_state),
  energy_conserving B K -> 0 <= dt ->
  (forall n,
     dt * sum_Q_ns (fun k => grhs nu B K (gtraj nu B K dt a0 n) k
                             * grhs nu B K (gtraj nu B K dt a0 n) k) K
     <= 4 * nu * modal_enstrophy K (gtraj nu B K dt a0 n)) ->
  energy_decreasing K (gtraj nu B K dt a0) /\
  (forall n, energy_at K (gtraj nu B K dt a0) n <= energy_at K (gtraj nu B K dt a0) 0).
Proof.
  intros nu B K dt a0 HB Hdt Hcond.
  assert (Hdec : energy_decreasing K (gtraj nu B K dt a0)).
  { intro n. unfold energy_at. cbn [gtraj].
    apply conserving_step_energy_le; [ exact HB | exact Hdt | apply Hcond ]. }
  split; [ exact Hdec | ].
  apply energy_bounded_by_initial. exact Hdec.
Qed.

(* ===================================================================== *)
(*  3. Bounds: the nonlinear term and the square sum of the right-hand side *)
(* ===================================================================== *)

Lemma qmul_le_l : forall x y z, x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros x y z Hxy Hz.
  assert (H1 : z * x == x * z) by ring. rewrite H1.
  assert (H2 : z * y == y * z) by ring. rewrite H2.
  apply Qmult_le_compat_r; assumption.
Qed.

Lemma inject_nat_S_ns : forall n, inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. reflexivity.
Qed.

Lemma inject_nat_nonneg_ns : forall n, 0 <= inject_Z (Z.of_nat n).
Proof. intro n. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

Lemma sum_ns_constant : forall (c : Q) n,
  sum_Q_ns (fun _ => c) n == inject_Z (Z.of_nat n) * c.
Proof.
  intros c n. induction n as [|n IH].
  - rewrite sum_ns_0. cbn [Z.of_nat inject_Z]. ring.
  - rewrite sum_ns_S, IH, inject_nat_S_ns. ring.
Qed.

Lemma sum_ns_abs_le : forall f n,
  Qabs (sum_Q_ns f n) <= sum_Q_ns (fun i => Qabs (f i)) n.
Proof.
  intros f n. induction n as [|n IH].
  - cbn [sum_Q_ns]. apply Qle_refl.
  - cbn [sum_Q_ns]. eapply Qle_trans; [ apply Qabs_triangle | ].
    apply Qplus_le_compat; [ exact IH | apply Qle_refl ].
Qed.

Lemma Qabs_mult_le_half_squares : forall x y, Qabs (x * y) <= (1#2) * (x * x + y * y).
Proof.
  intros x y. apply Qabs_Qle_condition.
  pose proof (Qsq_nonneg (x - y)) as H1.
  pose proof (Qsq_nonneg (x + y)) as H2.
  assert (E1 : (x - y) * (x - y) == x * x + y * y - 2 * (x * y)) by ring.
  assert (E2 : (x + y) * (x + y) == x * x + y * y + 2 * (x * y)) by ring.
  rewrite E1 in H1. rewrite E2 in H2.
  set (p := x * y) in *. set (s := x * x + y * y) in *.
  split; lra.
Qed.

Lemma sq_le_of_abs_le : forall x r, Qabs x <= r -> x * x <= r * r.
Proof.
  intros x r H. apply Qabs_Qle_condition in H. destruct H as [H1 H2].
  assert (H : 0 <= (r - x) * (r + x)) by (apply Qmult_le_0_compat; lra).
  assert (E : (r - x) * (r + x) == r * r - x * x) by ring.
  rewrite E in H. lra.
Qed.

Lemma sq_add_bound : forall p q : Q, (p + q) * (p + q) <= 2 * (p * p) + 2 * (q * q).
Proof.
  intros p q. pose proof (Qsq_nonneg (p - q)) as H.
  assert (E : (p - q) * (p - q) == p * p + q * q - 2 * (p * q)) by ring.
  rewrite E in H.
  assert (E2 : (p + q) * (p + q) == p * p + q * q + 2 * (p * q)) by ring.
  rewrite E2. set (x := p * q) in *. lra.
Qed.

Lemma double_sum_sq_eval : forall (c : Q) K (a : nat -> Q),
  sum_Q_ns (fun l => sum_Q_ns (fun m => c * (a l * a l + a m * a m)) K) K
  == 2 * c * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K.
Proof.
  intros c K a.
  set (Kq := inject_Z (Z.of_nat K)).
  set (S2 := sum_Q_ns (fun l => a l * a l) K).
  transitivity (sum_Q_ns (fun l => (c * Kq) * (a l * a l) + c * S2) K).
  { apply sum_ns_ext. intros l _.
    rewrite (sum_ns_ext (fun m => c * (a l * a l + a m * a m))
               (fun m => c * (a l * a l) + c * (a m * a m)) K) by (intros; ring).
    rewrite (sum_ns_add (fun _ => c * (a l * a l)) (fun m => c * (a m * a m)) K).
    rewrite (sum_ns_constant (c * (a l * a l)) K).
    rewrite (sum_ns_scale c (fun m => a m * a m) K).
    fold Kq. fold S2. ring. }
  rewrite (sum_ns_add (fun l => (c * Kq) * (a l * a l)) (fun _ => c * S2) K).
  rewrite (sum_ns_scale (c * Kq) (fun l => a l * a l) K).
  rewrite (sum_ns_constant (c * S2) K).
  fold Kq. fold S2. ring.
Qed.

(** The nonlinear term of a mode for a coupling bounded by M on the modes < K:
    |nl_k(a)| <= M K sum a_l^2. *)
Lemma nl_bound : forall B K M (a : nat -> Q) k,
  (forall l m, (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  Qabs (nl B K a k) <= M * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K.
Proof.
  intros B K M a k HB. unfold nl.
  eapply Qle_trans; [ apply sum_ns_abs_le | ].
  apply Qle_trans with
    (sum_Q_ns (fun l => sum_Q_ns (fun m => (M * (1#2)) * (a l * a l + a m * a m)) K) K).
  - apply sum_ns_le. intros l Hl.
    eapply Qle_trans; [ apply sum_ns_abs_le | ].
    apply sum_ns_le. intros m Hm.
    assert (E : B k l m * a l * a m == B k l m * (a l * a m)) by ring.
    rewrite E, Qabs_Qmult.
    pose proof (HB l m Hl Hm) as H1.
    pose proof (Qabs_mult_le_half_squares (a l) (a m)) as H2.
    pose proof (Qabs_nonneg (B k l m)) as H3.
    pose proof (Qabs_nonneg (a l * a m)) as H4.
    assert (E2 : M * (1#2) * (a l * a l + a m * a m)
                 == M * ((1#2) * (a l * a l + a m * a m))) by ring.
    rewrite E2.
    apply Qle_trans with (M * Qabs (a l * a m)).
    + apply Qmult_le_compat_r; assumption.
    + apply qmul_le_l; [ exact H2 | lra ].
  - rewrite (double_sum_sq_eval (M * (1#2)) K a).
    assert (E : 2 * (M * (1#2)) * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K
                == M * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K) by ring.
    rewrite E. apply Qle_refl.
Qed.

Lemma wgt_ge_1 : forall k, 1 <= wgt k.
Proof.
  intro k. unfold wgt. change 1 with (inject_Z 1). rewrite <- Zle_Qle. lia.
Qed.

Lemma wgt_le_K2 : forall K k, (k < K)%nat -> wgt k <= inject_Z (Z.of_nat (K * K)).
Proof.
  intros K k Hk. unfold wgt. rewrite <- Zle_Qle. apply Nat2Z.inj_le. nia.
Qed.

(** The square sum of the right-hand side:
    sum F_k^2 <= 2 nu^2 K^2 sum w_k a_k^2 + 2 K (M K sum a_l^2)^2. *)
Lemma rhs_sq_sum_bound : forall nu B K M (a : nat -> Q),
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  sum_Q_ns (fun k => grhs nu B K a k * grhs nu B K a k) K
  <= 2 * (nu * nu) * inject_Z (Z.of_nat (K * K))
       * sum_Q_ns (fun k => wgt k * a k * a k) K
     + 2 * inject_Z (Z.of_nat K)
       * ((M * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K)
          * (M * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K)).
Proof.
  intros nu B K M a HB.
  set (W := inject_Z (Z.of_nat (K * K))).
  set (Kq := inject_Z (Z.of_nat K)).
  set (S2 := sum_Q_ns (fun l => a l * a l) K).
  set (R := M * Kq * S2).
  apply Qle_trans with
    (sum_Q_ns (fun k => (2 * (nu * nu) * W) * (wgt k * a k * a k) + 2 * (R * R)) K).
  - apply sum_ns_le. intros k Hk. unfold grhs.
    eapply Qle_trans; [ apply sq_add_bound | ].
    pose proof (nl_bound B K M a k (fun l m Hl Hm => HB k l m Hk Hl Hm)) as Hn.
    fold Kq in Hn. fold S2 in Hn. fold R in Hn.
    pose proof (sq_le_of_abs_le _ _ Hn) as Hn2.
    pose proof (wgt_le_K2 K k Hk) as Hw. fold W in Hw.
    pose proof (wgt_pos k) as Hw0.
    assert (Hq : 0 <= wgt k * a k * a k).
    { assert (E : wgt k * a k * a k == wgt k * (a k * a k)) by ring. rewrite E.
      apply Qmult_le_0_compat; [ lra | apply Qsq_nonneg ]. }
    assert (Hnn : 0 <= nu * nu) by apply Qsq_nonneg.
    assert (E1 : (- nu * wgt k * a k) * (- nu * wgt k * a k)
                 == (nu * nu) * (wgt k * (wgt k * a k * a k))) by ring.
    assert (H1 : wgt k * (wgt k * a k * a k) <= W * (wgt k * a k * a k)).
    { apply Qmult_le_compat_r; assumption. }
    assert (H2 : (nu * nu) * (wgt k * (wgt k * a k * a k))
                 <= (nu * nu) * (W * (wgt k * a k * a k))).
    { apply qmul_le_l; assumption. }
    rewrite E1.
    set (X := (nu * nu) * (wgt k * (wgt k * a k * a k))) in *.
    set (Y := (nu * nu) * (W * (wgt k * a k * a k))) in *.
    assert (E2 : 2 * (nu * nu) * W * (wgt k * a k * a k) == 2 * Y) by (unfold Y; ring).
    rewrite E2.
    set (n2 := nl B K a k * nl B K a k) in *.
    set (r2 := R * R) in *.
    lra.
  - rewrite (sum_ns_add (fun k => (2 * (nu * nu) * W) * (wgt k * a k * a k))
                        (fun _ => 2 * (R * R)) K).
    rewrite (sum_ns_scale (2 * (nu * nu) * W) (fun k => wgt k * a k * a k) K).
    rewrite (sum_ns_constant (2 * (R * R)) K).
    fold Kq.
    assert (E : Kq * (2 * (R * R)) == 2 * Kq * (R * R)) by ring.
    rewrite E. apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  4. The estimate with a condition on the step fixed in advance          *)
(* ===================================================================== *)

(** One step: while the energy is not above E0, the two conditions on the step
    make the energy not grow. *)
Lemma small_step_energy_le : forall nu B K dt M E0 (a : nat -> Q),
  energy_conserving B K -> 0 <= nu -> 0 <= dt ->
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  4 * dt * (M * M)
    * (inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K)) * E0 <= nu ->
  modal_energy K a <= E0 ->
  modal_energy K (gstep nu B K dt a) <= modal_energy K a.
Proof.
  intros nu B K dt M E0 a HB Hnu Hdt Hbd Hc1 Hc2 HE.
  apply (conserving_step_energy_le nu B K dt a HB Hdt).
  pose proof (rhs_sq_sum_bound nu B K M a Hbd) as HF.
  pose proof (enstrophy_ge_energy K a) as HEO.
  unfold modal_enstrophy. unfold modal_energy in HE, HEO. unfold modal_enstrophy in HEO.
  assert (EW : sum_Q_ns (fun k => inject_Z (Z.of_nat ((k + 1) * (k + 1))) * a k * a k) K
               == sum_Q_ns (fun k => wgt k * a k * a k) K).
  { apply sum_ns_ext. intros k _. unfold wgt. reflexivity. }
  rewrite EW in HEO. rewrite EW.
  assert (HS0 : 0 <= sum_Q_ns (fun l => a l * a l) K) by apply sum_ns_sq_nonneg.
  pose proof (inject_nat_nonneg_ns K) as HK0.
  pose proof (inject_nat_nonneg_ns (K * K)) as HW0.
  set (W := inject_Z (Z.of_nat (K * K))) in *.
  set (Kq := inject_Z (Z.of_nat K)) in *.
  set (S2 := sum_Q_ns (fun l => a l * a l) K) in *.
  set (W2 := sum_Q_ns (fun k => wgt k * a k * a k) K) in *.
  set (SF := sum_Q_ns (fun k => grhs nu B K a k * grhs nu B K a k) K) in *.
  assert (HS2W2 : S2 <= W2) by lra.
  assert (HW20 : 0 <= W2) by lra.
  set (c1 := dt * (M * M) * (Kq * Kq * Kq)).
  assert (Hc10 : 0 <= c1).
  { unfold c1. apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat; [ exact Hdt | apply Qsq_nonneg ].
    - apply Qmult_le_0_compat; [ apply Qsq_nonneg | exact HK0 ]. }
  assert (Hc2' : 4 * c1 * E0 <= nu).
  { assert (E : 4 * c1 * E0 == 4 * dt * (M * M) * (Kq * Kq * Kq) * E0) by (unfold c1; ring).
    rewrite E. exact Hc2. }
  (* term B: (2 c1 S2) S2 <= nu W2 *)
  assert (HA1 : c1 * S2 <= c1 * (2 * E0)) by (apply qmul_le_l; lra).
  assert (HA2 : 2 * c1 * S2 <= nu).
  { assert (E : c1 * (2 * E0) == 2 * c1 * E0) by ring. rewrite E in HA1.
    set (x := c1 * S2) in *. set (y := c1 * E0) in *.
    assert (E3 : 2 * c1 * S2 == 2 * x) by (unfold x; ring).
    assert (E4 : 4 * c1 * E0 == 4 * y) by (unfold y; ring).
    rewrite E4 in Hc2'. assert (E5 : 2 * c1 * E0 == 2 * y) by (unfold y; ring).
    rewrite E5 in HA1. rewrite E3. lra. }
  assert (HB1 : (2 * c1 * S2) * S2 <= nu * S2) by (apply Qmult_le_compat_r; assumption).
  assert (HB2 : nu * S2 <= nu * W2) by (apply qmul_le_l; assumption).
  (* term A: (2 dt nu W) (nu W2) <= nu W2 *)
  assert (HnW : 0 <= nu * W2) by (apply Qmult_le_0_compat; assumption).
  assert (HA : (2 * dt * nu * W) * (nu * W2) <= 1 * (nu * W2))
    by (apply Qmult_le_compat_r; assumption).
  (* assemble *)
  assert (HF' : dt * SF <= dt * (2 * (nu * nu) * W * W2
                                 + 2 * Kq * ((M * Kq * S2) * (M * Kq * S2))))
    by (apply qmul_le_l; assumption).
  assert (Eid : dt * (2 * (nu * nu) * W * W2 + 2 * Kq * ((M * Kq * S2) * (M * Kq * S2)))
                == (2 * dt * nu * W) * (nu * W2) + (2 * c1 * S2) * S2) by (unfold c1; ring).
  rewrite Eid in HF'.
  assert (Eg : 4 * nu * ((1#2) * W2) == 2 * (nu * W2)) by ring.
  rewrite Eg.
  set (t1 := (2 * dt * nu * W) * (nu * W2)) in *.
  set (t2 := (2 * c1 * S2) * S2) in *.
  set (v1 := nu * W2) in *. set (v2 := nu * S2) in *.
  lra.
Qed.

(** THE ESTIMATE. For a bounded energy-conserving coupling and a step that
    satisfies two conditions known in advance, the energy does not grow from
    step to step and never exceeds the initial one. *)
Theorem galerkin_traj_energy_apriori : forall nu B K dt M (a0 : modal_state),
  energy_conserving B K -> 0 <= nu -> 0 <= dt ->
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  4 * dt * (M * M)
    * (inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K))
    * modal_energy K a0 <= nu ->
  energy_decreasing K (gtraj nu B K dt a0) /\
  (forall n, modal_energy K (gtraj nu B K dt a0 n) <= modal_energy K a0).
Proof.
  intros nu B K dt M a0 HB Hnu Hdt Hbd Hc1 Hc2.
  assert (Hall : forall n,
    modal_energy K (gtraj nu B K dt a0 n) <= modal_energy K a0 /\
    modal_energy K (gtraj nu B K dt a0 (S n)) <= modal_energy K (gtraj nu B K dt a0 n)).
  { induction n as [|n [IH1 IH2]].
    - split; [ cbn [gtraj]; apply Qle_refl | ].
      cbn [gtraj].
      apply (small_step_energy_le nu B K dt M (modal_energy K a0) a0 HB Hnu Hdt Hbd Hc1 Hc2).
      apply Qle_refl.
    - assert (H1 : modal_energy K (gtraj nu B K dt a0 (S n)) <= modal_energy K a0)
        by (eapply Qle_trans; [ exact IH2 | exact IH1 ]).
      split; [ exact H1 | ].
      rewrite (gtraj_S nu B K dt a0 (S n)).
      apply (small_step_energy_le nu B K dt M (modal_energy K a0) _ HB Hnu Hdt Hbd Hc1 Hc2).
      exact H1. }
  split.
  - intro n. unfold energy_at. apply (Hall n).
  - intro n. apply (Hall n).
Qed.

Corollary adv_traj_energy_apriori : forall nu T K dt M (a0 : modal_state),
  0 <= nu -> 0 <= dt ->
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (adv T k l m) <= M) ->
  2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  4 * dt * (M * M)
    * (inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K))
    * modal_energy K a0 <= nu ->
  forall n, modal_energy K (gtraj nu (adv T) K dt a0 n) <= modal_energy K a0.
Proof.
  intros nu T K dt M a0 Hnu Hdt Hbd Hc1 Hc2.
  apply (galerkin_traj_energy_apriori nu (adv T) K dt M a0
           (adv_energy_conserving T K) Hnu Hdt Hbd Hc1 Hc2).
Qed.

(* ===================================================================== *)
(*  5. The system with the coefficient of GalerkinSystem.v; the viscous    *)
(*     polygon of ResolutionRegularity.v                                   *)
(* ===================================================================== *)

Lemma sq_contract : forall c x : Q,
  0 <= c -> c <= 1 -> ((1 - c) * x) * ((1 - c) * x) <= x * x.
Proof.
  intros c x H0 H1.
  assert (Hx : 0 <= x * x) by apply Qsq_nonneg.
  assert (Hc : (1 - c) * (1 - c) <= 1) by nra.
  assert (E : ((1 - c) * x) * ((1 - c) * x) == ((1 - c) * (1 - c)) * (x * x)) by ring.
  rewrite E.
  apply Qle_trans with (1 * (x * x)); [ apply Qmult_le_compat_r; assumption | lra ].
Qed.

(** The system with B_coeff is viscous, so its energy does not grow under the
    condition dt nu K^2 <= 1 alone. *)
Theorem formal_traj_energy_decreasing : forall (nsc : NSCoupling) nu K dt (a0 : modal_state),
  0 <= nu -> 0 <= dt -> dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  energy_decreasing K (gtraj nu B_coeff K dt a0).
Proof.
  intros nsc nu K dt a0 Hnu Hdt Hc n. unfold energy_at. cbn [gtraj].
  set (a := gtraj nu B_coeff K dt a0 n).
  unfold modal_energy.
  assert (Hs : sum_Q_ns (fun k => gstep nu B_coeff K dt a k * gstep nu B_coeff K dt a k) K
               <= sum_Q_ns (fun k => a k * a k) K).
  { apply sum_ns_le. intros k Hk.
    assert (E : gstep nu B_coeff K dt a k == (1 - dt * nu * wgt k) * a k).
    { unfold gstep. rewrite (grhs_formal_is_viscous nsc nu K a k). ring. }
    rewrite E.
    pose proof (wgt_le_K2 K k Hk) as Hw. pose proof (wgt_pos k) as Hw0.
    assert (Hdn : 0 <= dt * nu) by (apply Qmult_le_0_compat; assumption).
    apply sq_contract.
    - apply Qmult_le_0_compat; [ exact Hdn | lra ].
    - apply Qle_trans with (dt * nu * inject_Z (Z.of_nat (K * K))); [ | exact Hc ].
      apply qmul_le_l; assumption. }
  lra.
Qed.

Lemma visc_factor : forall nu K N i,
  0 <= nu -> (0 < N)%nat -> (i < K)%nat ->
  nu * inject_Z (Z.of_nat (K * K)) <= inject_Z (Z.of_nat N) ->
  0 <= (1 / inject_Z (Z.of_nat N)) * (nu * inject_Z (Z.of_nat (i * i))) /\
  (1 / inject_Z (Z.of_nat N)) * (nu * inject_Z (Z.of_nat (i * i))) <= 1.
Proof.
  intros nu K N i Hnu HN Hi Hcfl.
  assert (Hn : 0 < inject_Z (Z.of_nat N)).
  { change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. }
  assert (Hi0 : 0 <= inject_Z (Z.of_nat (i * i))) by apply inject_nat_nonneg_ns.
  assert (HiK : inject_Z (Z.of_nat (i * i)) <= inject_Z (Z.of_nat (K * K))).
  { rewrite <- Zle_Qle. apply Nat2Z.inj_le. nia. }
  assert (Hq0 : 0 <= nu * inject_Z (Z.of_nat (i * i))) by (apply Qmult_le_0_compat; assumption).
  assert (Hq1 : nu * inject_Z (Z.of_nat (i * i)) <= inject_Z (Z.of_nat N)).
  { apply Qle_trans with (nu * inject_Z (Z.of_nat (K * K))); [ | exact Hcfl ].
    apply qmul_le_l; assumption. }
  assert (E : (1 / inject_Z (Z.of_nat N)) * (nu * inject_Z (Z.of_nat (i * i)))
              == (nu * inject_Z (Z.of_nat (i * i))) / inject_Z (Z.of_nat N)).
  { unfold Qdiv. ring. }
  rewrite E. split.
  - apply Qle_shift_div_l; [ exact Hn | lra ].
  - apply Qle_shift_div_r; [ exact Hn | lra ].
Qed.

(** The viscous polygon euler_evolve of ResolutionRegularity.v: under
    nu K^2 <= N the premise energy_decreasing holds for it. *)
Theorem viscous_euler_energy_decreasing : forall nu K N (a0 : modal_state),
  0 <= nu -> (0 < N)%nat ->
  nu * inject_Z (Z.of_nat (K * K)) <= inject_Z (Z.of_nat N) ->
  energy_decreasing K (fun n => ResolutionRegularity.euler_evolve nu K N n a0).
Proof.
  intros nu K N a0 Hnu HN Hcfl n. unfold energy_at.
  cbn [ResolutionRegularity.euler_evolve].
  set (a := ResolutionRegularity.euler_evolve nu K N n a0).
  unfold modal_energy.
  assert (Hs : sum_Q_ns (fun k => ResolutionRegularity.euler_step nu K N a k
                                  * ResolutionRegularity.euler_step nu K N a k) K
               <= sum_Q_ns (fun k => a k * a k) K).
  { apply sum_ns_le. intros i Hi.
    unfold ResolutionRegularity.euler_step.
    assert (Hlt : Nat.ltb i K = true) by (apply Nat.ltb_lt; exact Hi).
    rewrite Hlt.
    destruct (visc_factor nu K N i Hnu HN Hi Hcfl) as [Hc0 Hc1].
    set (c := (1 / inject_Z (Z.of_nat N)) * (nu * inject_Z (Z.of_nat (i * i)))) in *.
    assert (E : a i + 1 / inject_Z (Z.of_nat N) * (- nu * inject_Z (Z.of_nat (i * i)) * a i)
                == (1 - c) * a i) by (unfold c; ring).
    rewrite E. apply sq_contract; assumption. }
  lra.
Qed.

Corollary viscous_euler_energy_bounded : forall nu K N (a0 : modal_state),
  0 <= nu -> (0 < N)%nat ->
  nu * inject_Z (Z.of_nat (K * K)) <= inject_Z (Z.of_nat N) ->
  forall n, modal_energy K (ResolutionRegularity.euler_evolve nu K N n a0)
            <= modal_energy K a0.
Proof.
  intros nu K N a0 Hnu HN Hcfl n.
  exact (energy_bounded_by_initial K
           (fun n => ResolutionRegularity.euler_evolve nu K N n a0)
           (viscous_euler_energy_decreasing nu K N a0 Hnu HN Hcfl) n).
Qed.

Print Assumptions galerkin_traj_energy_apriori.
Print Assumptions formal_traj_energy_decreasing.
Print Assumptions viscous_euler_energy_decreasing.
Print Assumptions energy_bound_needs_premise.
