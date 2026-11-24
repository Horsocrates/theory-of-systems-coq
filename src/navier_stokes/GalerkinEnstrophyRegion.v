(** * GalerkinEnstrophyRegion.v — The higher norm of the Galerkin system in time:
      stretching as the nonlinear production of enstrophy; couplings without
      stretching keep the enstrophy bounded on the whole trajectory; the invariant
      region as a theorem about the step of the scheme (Part IX, chapter 5)

    Elements: rational amplitudes of finitely many modes on every step; the
              coupling B; the viscosity nu; the step dt; the region of amplitudes
              |a_k| <= A / k of InvariantRegion.v.
    Roles:    stretch B K a = sum_k w_k a_k nl_k = role-production of enstrophy by
              the nonlinear term (zero for every state = the "two-dimensional"
              type; nonzero = the "three-dimensional" type);
              Omega = role-higher norm; P (palinstrophy) = role-its dissipation;
              the region = role-invariant set; the bound of the nonlinear term in
              the region = role-condition of the conditional theorem;
              the triad (-5, 8, -3) = role-witness that couplings without
              stretching exist; the record ex_coupling = role-witness that the
              condition does not follow from the record of premises.
    Rules:    the enstrophy rate along the right-hand side is
              - 2 nu P + stretch; without stretching the enstrophy obeys the same
              step identity as the energy, with one more weight. A step
              (1 - c) a_k + dt N_k with c = dt nu k^2 in [0, 1] keeps
              |a_k| <= A / k when |N_k| <= nu k A.

    ============ E/R/R разбор ============
      Rules (L5): скорость энстрофии вдоль правой части равна −2 nu P + stretch;
                  без вытяжения энстрофия подчиняется тому же тождеству шага, что
                  и энергия, с лишним весом. Шаг (1 − c) a_k + dt N_k при
                  c = dt nu k^2 из [0, 1] сохраняет |a_k| <= A / k, если
                  |N_k| <= nu k A.
      Roles (L4): stretch — роль-производство энстрофии нелинейным членом; Omega —
                  роль-высшая норма; P — роль-её диссипация; область — роль-
                  инвариантное множество; оценка нелинейного члена в области —
                  роль-условие условной теоремы; триада и запись-пример —
                  роль-свидетели.
      Elements  : рациональные амплитуды конечного числа мод на каждом конечном
                  шаге (L1 + P4).
    ДИАГНОСТИКА P4: «регулярность» здесь — «энстрофия состояния после всякого
    конечного числа шагов не больше начальной» или «состояние после всякого
    конечного числа шагов лежит в области»; размерности пространства, завихренности
    как поля и предела по числу мод в утверждениях нет.

    PROVED (all closed under the global context):
      - stretching_2d of Vorticity.v is the number zero by definition
        ([stretching_2d_is_literal_zero]);
      - the enstrophy rate along the right-hand side: - 2 nu P + stretch
        ([galerkin_enstrophy_rate]); the step identity of the enstrophy
        ([galerkin_step_enstrophy]);
      - a coupling with stretching: the nonlinear term produces enstrophy
        ([pair_stretching_values]); a coupling without stretching that conserves
        energy and transports: the triad ([Btri_nl], [Btri_energy_conserving],
        [Btri_no_stretching]);
      - WITHOUT STRETCHING: for a bounded energy-conserving coupling with zero
        stretching, under two conditions on the step fixed in advance, the energy
        and the enstrophy do not grow from step to step on the whole trajectory —
        both premises of full_regularity_2d of EnergyEstimate.v are proved
        ([no_stretching_traj_apriori]; for the triad — [triad_traj_regular]);
      - THE REGION: if in the region the nonlinear term of every mode does not
        exceed the boundary damping and dt nu K^2 <= 1, the step of the scheme
        keeps the region, and so does the whole trajectory
        ([region_invariant_step], [region_invariant_iter],
        [region_iter_mode_enstrophy]); for the nonlinear term with B_coeff the
        condition holds trivially ([formal_region_invariant]);
      - the condition does not follow from the record of premises: a record, a
        state in the region and a mode for which the majorant of the nonlinear
        term exceeds the number forcing_in_region
        ([forcing_in_region_not_a_bound]).

    NOT claimed: that a flow in two dimensions gives a coupling without
    stretching (no dimension is formalized); a family of such couplings for every
    K; a bound of the enstrophy uniform in K; that the bound of the nonlinear term
    in the region follows from a bound of the coupling (it needs a selection rule
    of triads — not formalized); unconditional regularity for a coupling with
    stretching.

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.
From ToS Require Import navier_stokes.EnergyEstimate.
From ToS Require Import navier_stokes.TriadicInteraction.
From ToS Require Import navier_stokes.InvariantRegion.
From ToS Require Import navier_stokes.GalerkinAdvection.
From ToS Require Import navier_stokes.GalerkinEnergyEstimate.
From ToS Require navier_stokes.Vorticity.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. Stretching: the nonlinear production of enstrophy                   *)
(* ===================================================================== *)

(** stretching_2d of Vorticity.v is the constant 0 by definition. *)
Lemma stretching_2d_is_literal_zero : Vorticity.stretching_2d = 0.
Proof. reflexivity. Qed.

(** What the nonlinear term contributes to the rate of the enstrophy
    Omega = (1/2) sum w_k a_k^2. *)
Definition stretch (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) : Q :=
  sum_Q_ns (fun k => wgt k * a k * nl B K a k) K.

(** The enstrophy rate along the right-hand side: - 2 nu P + stretch. *)
Theorem galerkin_enstrophy_rate : forall nu B K (a : nat -> Q),
  sum_Q_ns (fun k => wgt k * a k * grhs nu B K a k) K
  == - (2) * nu * Vorticity.palinstrophy K a + stretch B K a.
Proof.
  intros nu B K a. unfold grhs.
  transitivity (sum_Q_ns (fun k => (- nu) * (wgt k * wgt k * a k * a k)
                                   + wgt k * a k * nl B K a k) K).
  { apply sum_ns_ext. intros k _. ring. }
  rewrite (sum_ns_add (fun k => (- nu) * (wgt k * wgt k * a k * a k))
                      (fun k => wgt k * a k * nl B K a k) K).
  rewrite (sum_ns_scale (- nu) (fun k => wgt k * wgt k * a k * a k) K).
  unfold stretch, Vorticity.palinstrophy, wgt. cbv zeta. ring.
Qed.

Corollary no_stretching_enstrophy_rate : forall nu B K (a : nat -> Q),
  stretch B K a == 0 ->
  sum_Q_ns (fun k => wgt k * a k * grhs nu B K a k) K
  == - (2) * nu * Vorticity.palinstrophy K a.
Proof.
  intros nu B K a Hs. rewrite galerkin_enstrophy_rate, Hs. ring.
Qed.

Lemma enstrophy_step_identity : forall K (a F : nat -> Q) dt,
  modal_enstrophy K (fun k => a k + dt * F k) ==
  modal_enstrophy K a + dt * sum_Q_ns (fun k => wgt k * a k * F k) K
  + (1#2) * dt * dt * sum_Q_ns (fun k => wgt k * F k * F k) K.
Proof.
  intros K a F dt. unfold modal_enstrophy, wgt.
  set (w := fun k : nat => inject_Z (Z.of_nat ((k + 1) * (k + 1)))).
  assert (E : sum_Q_ns (fun k => w k * (a k + dt * F k) * (a k + dt * F k)) K ==
              sum_Q_ns (fun k => w k * a k * a k) K
              + ((2 * dt) * sum_Q_ns (fun k => w k * a k * F k) K
                 + (dt * dt) * sum_Q_ns (fun k => w k * F k * F k) K)).
  { transitivity (sum_Q_ns (fun k => w k * a k * a k
                    + ((2 * dt) * (w k * a k * F k) + (dt * dt) * (w k * F k * F k))) K).
    { apply sum_ns_ext. intros k _. ring. }
    rewrite (sum_ns_add (fun k => w k * a k * a k)
               (fun k => (2 * dt) * (w k * a k * F k) + (dt * dt) * (w k * F k * F k)) K).
    rewrite (sum_ns_add (fun k => (2 * dt) * (w k * a k * F k))
               (fun k => (dt * dt) * (w k * F k * F k)) K).
    rewrite (sum_ns_scale (2 * dt) (fun k => w k * a k * F k) K).
    rewrite (sum_ns_scale (dt * dt) (fun k => w k * F k * F k) K).
    reflexivity. }
  change (sum_Q_ns (fun k => inject_Z (Z.of_nat ((k + 1) * (k + 1)))
                             * (a k + dt * F k) * (a k + dt * F k)) K)
    with (sum_Q_ns (fun k => w k * (a k + dt * F k) * (a k + dt * F k)) K).
  rewrite E. unfold w. ring.
Qed.

(** The exact identity of one step for the enstrophy. *)
Theorem galerkin_step_enstrophy : forall nu B K dt (a : nat -> Q),
  modal_enstrophy K (gstep nu B K dt a) ==
  modal_enstrophy K a
  + dt * (- (2) * nu * Vorticity.palinstrophy K a + stretch B K a)
  + (1#2) * dt * dt
    * sum_Q_ns (fun k => wgt k * grhs nu B K a k * grhs nu B K a k) K.
Proof.
  intros nu B K dt a. unfold gstep.
  rewrite (enstrophy_step_identity K a (grhs nu B K a) dt).
  rewrite (galerkin_enstrophy_rate nu B K a). ring.
Qed.

Corollary no_stretching_step_enstrophy_le : forall nu B K dt (a : nat -> Q),
  stretch B K a == 0 -> 0 <= dt ->
  dt * sum_Q_ns (fun k => wgt k * grhs nu B K a k * grhs nu B K a k) K
    <= 4 * nu * Vorticity.palinstrophy K a ->
  modal_enstrophy K (gstep nu B K dt a) <= modal_enstrophy K a.
Proof.
  intros nu B K dt a Hs Hdt Hcond.
  rewrite (galerkin_step_enstrophy nu B K dt a), Hs.
  set (S := sum_Q_ns (fun k => wgt k * grhs nu B K a k * grhs nu B K a k) K) in *.
  set (P := Vorticity.palinstrophy K a) in *.
  set (Om := modal_enstrophy K a) in *.
  assert (H : 0 <= dt * (4 * nu * P - dt * S)).
  { apply Qmult_le_0_compat; lra. }
  lra.
Qed.

(* ===================================================================== *)
(*  2. With stretching and without it: two couplings                       *)
(* ===================================================================== *)

(** The coupling adv T_pair has stretching: on the state (1, -1) the nonlinear
    term produces enstrophy, on the state (1, 1) it removes it. *)
Definition a_pm : nat -> Q := fun k => match k with O => 1 | _ => - (1) end.

Lemma pair_stretching_values :
  stretch (adv T_pair) 2 a_unit == - (3) /\ stretch (adv T_pair) 2 a_pm == 3.
Proof. split; vm_compute; reflexivity. Qed.

(** A triad on the modes 0, 1, 2 (the weights 1, 4, 9):
    da_0 = -5 a_1 a_2,  da_1 = 8 a_0 a_2,  da_2 = -3 a_0 a_1.
    The coefficients are (w_1 - w_2, w_2 - w_0, w_0 - w_1). *)
Definition Btri (k l m : nat) : Q :=
  match k, l, m with
  | O, S O, S (S O) => - (5)
  | S O, O, S (S O) => 8
  | S (S O), O, S O => - (3)
  | _, _, _ => 0
  end.

Lemma Btri_nl : forall a : nat -> Q,
  nl Btri 3 a 0%nat == - (5) * a 1%nat * a 2%nat /\
  nl Btri 3 a 1%nat == 8 * a 0%nat * a 2%nat /\
  nl Btri 3 a 2%nat == - (3) * a 0%nat * a 1%nat.
Proof.
  intro a. unfold nl. cbn [sum_Q_ns Btri]. split; [ ring | split; ring ].
Qed.

Lemma Btri_energy_conserving : energy_conserving Btri 3.
Proof.
  intro a. destruct (Btri_nl a) as [H0 [H1 H2]].
  cbn [sum_Q_ns]. rewrite H0, H1, H2. ring.
Qed.

Lemma Btri_no_stretching : forall a : nat -> Q, stretch Btri 3 a == 0.
Proof.
  intro a. destruct (Btri_nl a) as [H0 [H1 H2]].
  unfold stretch. cbn [sum_Q_ns]. rewrite H0, H1, H2.
  unfold wgt. cbn. ring.
Qed.

Lemma Btri_bound : forall k l m, Qabs (Btri k l m) <= 8.
Proof.
  intros k l m. unfold Btri.
  destruct k as [|[|[|k]]]; destruct l as [|[|[|l]]]; destruct m as [|[|[|m]]];
    vm_compute; discriminate.
Qed.

(* ===================================================================== *)
(*  3. Without stretching: the enstrophy on the whole trajectory           *)
(* ===================================================================== *)

(** The weighted square sum of the right-hand side. *)
Lemma rhs_wsq_sum_bound : forall nu B K M (a : nat -> Q),
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  sum_Q_ns (fun k => wgt k * grhs nu B K a k * grhs nu B K a k) K
  <= 2 * (nu * nu) * inject_Z (Z.of_nat (K * K))
       * sum_Q_ns (fun k => wgt k * wgt k * a k * a k) K
     + 2 * inject_Z (Z.of_nat (K * K)) * inject_Z (Z.of_nat K)
       * ((M * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K)
          * (M * inject_Z (Z.of_nat K) * sum_Q_ns (fun l => a l * a l) K)).
Proof.
  intros nu B K M a HB.
  set (W := inject_Z (Z.of_nat (K * K))).
  set (Kq := inject_Z (Z.of_nat K)).
  set (S2 := sum_Q_ns (fun l => a l * a l) K).
  set (R := M * Kq * S2).
  apply Qle_trans with
    (sum_Q_ns (fun k => (2 * (nu * nu) * W) * (wgt k * wgt k * a k * a k)
                        + 2 * (W * (R * R))) K).
  - apply sum_ns_le. intros k Hk.
    pose proof (nl_bound B K M a k (fun l m Hl Hm => HB k l m Hk Hl Hm)) as Hn.
    fold Kq in Hn. fold S2 in Hn. fold R in Hn.
    pose proof (sq_le_of_abs_le _ _ Hn) as Hn2.
    pose proof (wgt_le_K2 K k Hk) as Hw. fold W in Hw.
    pose proof (wgt_pos k) as Hw0.
    assert (Hw0' : 0 <= wgt k) by lra.
    assert (HW0 : 0 <= W) by lra.
    unfold grhs.
    pose proof (sq_add_bound (- nu * wgt k * a k) (nl B K a k)) as Hsq.
    assert (E0 : wgt k * (- nu * wgt k * a k + nl B K a k) * (- nu * wgt k * a k + nl B K a k)
                 == wgt k * ((- nu * wgt k * a k + nl B K a k)
                             * (- nu * wgt k * a k + nl B K a k))) by ring.
    rewrite E0.
    eapply Qle_trans; [ apply (qmul_le_l _ _ (wgt k) Hsq Hw0') | ].
    assert (Hq : 0 <= wgt k * wgt k * a k * a k).
    { assert (E : wgt k * wgt k * a k * a k == (wgt k * a k) * (wgt k * a k)) by ring.
      rewrite E. apply Qsq_nonneg. }
    assert (Hnn : 0 <= nu * nu) by apply Qsq_nonneg.
    assert (HRR : 0 <= R * R) by apply Qsq_nonneg.
    assert (H1 : wgt k * (wgt k * wgt k * a k * a k) <= W * (wgt k * wgt k * a k * a k))
      by (apply Qmult_le_compat_r; assumption).
    assert (H2 : (nu * nu) * (wgt k * (wgt k * wgt k * a k * a k))
                 <= (nu * nu) * (W * (wgt k * wgt k * a k * a k)))
      by (apply qmul_le_l; assumption).
    assert (H3 : wgt k * (nl B K a k * nl B K a k) <= wgt k * (R * R))
      by (apply qmul_le_l; assumption).
    assert (H4 : wgt k * (R * R) <= W * (R * R))
      by (apply Qmult_le_compat_r; assumption).
    assert (E1 : wgt k * (2 * ((- nu * wgt k * a k) * (- nu * wgt k * a k))
                          + 2 * (nl B K a k * nl B K a k))
                 == 2 * ((nu * nu) * (wgt k * (wgt k * wgt k * a k * a k)))
                    + 2 * (wgt k * (nl B K a k * nl B K a k))) by ring.
    rewrite E1.
    assert (E2 : 2 * (nu * nu) * W * (wgt k * wgt k * a k * a k)
                 == 2 * ((nu * nu) * (W * (wgt k * wgt k * a k * a k)))) by ring.
    rewrite E2.
    set (X := (nu * nu) * (wgt k * (wgt k * wgt k * a k * a k))) in *.
    set (Y := (nu * nu) * (W * (wgt k * wgt k * a k * a k))) in *.
    set (n2 := wgt k * (nl B K a k * nl B K a k)) in *.
    set (r1 := wgt k * (R * R)) in *.
    set (r2 := W * (R * R)) in *.
    lra.
  - rewrite (sum_ns_add (fun k => (2 * (nu * nu) * W) * (wgt k * wgt k * a k * a k))
                        (fun _ => 2 * (W * (R * R))) K).
    rewrite (sum_ns_scale (2 * (nu * nu) * W) (fun k => wgt k * wgt k * a k * a k) K).
    rewrite (sum_ns_constant (2 * (W * (R * R))) K).
    fold Kq.
    assert (E : Kq * (2 * (W * (R * R))) == 2 * W * Kq * (R * R)) by ring.
    rewrite E. apply Qle_refl.
Qed.

(** One step: while the energy is not above E0, the conditions on the step make
    the enstrophy not grow — for a state without stretching. *)
Lemma small_step_enstrophy_le : forall nu B K dt M E0 (a : nat -> Q),
  stretch B K a == 0 -> 0 <= nu -> 0 <= dt ->
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  4 * dt * (M * M)
    * (inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K))
    * inject_Z (Z.of_nat (K * K)) * E0 <= nu ->
  modal_energy K a <= E0 ->
  modal_enstrophy K (gstep nu B K dt a) <= modal_enstrophy K a.
Proof.
  intros nu B K dt M E0 a Hs Hnu Hdt Hbd Hc1 Hc2 HE.
  apply (no_stretching_step_enstrophy_le nu B K dt a Hs Hdt).
  pose proof (rhs_wsq_sum_bound nu B K M a Hbd) as HF.
  pose proof (enstrophy_ge_energy K a) as HEO.
  pose proof (Vorticity.palinstrophy_ge_enstrophy K a) as HPO.
  assert (EP : Vorticity.palinstrophy K a
               == (1#2) * sum_Q_ns (fun k => wgt k * wgt k * a k * a k) K).
  { unfold Vorticity.palinstrophy.
    rewrite (sum_ns_ext
      (fun k => let kk := inject_Z (Z.of_nat ((k + 1) * (k + 1))) in kk * kk * a k * a k)
      (fun k => wgt k * wgt k * a k * a k) K); [ reflexivity | ].
    intros k _. unfold wgt. cbv zeta. reflexivity. }
  rewrite EP in HPO. rewrite EP.
  unfold modal_energy in HE, HEO.
  assert (HS0 : 0 <= sum_Q_ns (fun l => a l * a l) K) by apply sum_ns_sq_nonneg.
  pose proof (inject_nat_nonneg_ns K) as HK0.
  pose proof (inject_nat_nonneg_ns (K * K)) as HW0.
  set (W := inject_Z (Z.of_nat (K * K))) in *.
  set (Kq := inject_Z (Z.of_nat K)) in *.
  set (S2 := sum_Q_ns (fun l => a l * a l) K) in *.
  set (P2 := sum_Q_ns (fun k => wgt k * wgt k * a k * a k) K) in *.
  set (SF := sum_Q_ns (fun k => wgt k * grhs nu B K a k * grhs nu B K a k) K) in *.
  set (Om := modal_enstrophy K a) in *.
  assert (HS2P2 : S2 <= P2) by lra.
  assert (HP20 : 0 <= P2) by lra.
  set (c1 := dt * (M * M) * (Kq * Kq * Kq) * W).
  assert (Hc10 : 0 <= c1).
  { unfold c1. apply Qmult_le_0_compat; [ | exact HW0 ].
    apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat; [ exact Hdt | apply Qsq_nonneg ].
    - apply Qmult_le_0_compat; [ apply Qsq_nonneg | exact HK0 ]. }
  assert (Hc2' : 4 * c1 * E0 <= nu).
  { assert (E : 4 * c1 * E0 == 4 * dt * (M * M) * (Kq * Kq * Kq) * W * E0)
      by (unfold c1; ring).
    rewrite E. exact Hc2. }
  assert (HA1 : c1 * S2 <= c1 * (2 * E0)) by (apply qmul_le_l; lra).
  assert (HA2 : 2 * c1 * S2 <= nu).
  { set (x := c1 * S2) in *.
    assert (E3 : 2 * c1 * S2 == 2 * x) by (unfold x; ring).
    assert (E4 : 4 * c1 * E0 == 2 * (c1 * (2 * E0))) by ring.
    rewrite E4 in Hc2'. set (y := c1 * (2 * E0)) in *.
    rewrite E3. lra. }
  assert (HB1 : (2 * c1 * S2) * S2 <= nu * S2) by (apply Qmult_le_compat_r; assumption).
  assert (HB2 : nu * S2 <= nu * P2) by (apply qmul_le_l; assumption).
  assert (HnP : 0 <= nu * P2) by (apply Qmult_le_0_compat; assumption).
  assert (HA : (2 * dt * nu * W) * (nu * P2) <= 1 * (nu * P2))
    by (apply Qmult_le_compat_r; assumption).
  assert (HF' : dt * SF <= dt * (2 * (nu * nu) * W * P2
                                 + 2 * W * Kq * ((M * Kq * S2) * (M * Kq * S2))))
    by (apply qmul_le_l; assumption).
  assert (Eid : dt * (2 * (nu * nu) * W * P2 + 2 * W * Kq * ((M * Kq * S2) * (M * Kq * S2)))
                == (2 * dt * nu * W) * (nu * P2) + (2 * c1 * S2) * S2) by (unfold c1; ring).
  rewrite Eid in HF'.
  assert (Eg : 4 * nu * ((1#2) * P2) == 2 * (nu * P2)) by ring.
  rewrite Eg.
  set (t1 := (2 * dt * nu * W) * (nu * P2)) in *.
  set (t2 := (2 * c1 * S2) * S2) in *.
  set (v1 := nu * P2) in *. set (v2 := nu * S2) in *.
  lra.
Qed.

(** WITHOUT STRETCHING. For a bounded energy-conserving coupling with zero
    stretching, under two conditions on the step known in advance, the energy
    and the enstrophy do not grow from step to step on the whole trajectory. *)
Theorem no_stretching_traj_apriori : forall nu B K dt M (a0 : modal_state),
  energy_conserving B K -> (forall a : nat -> Q, stretch B K a == 0) ->
  0 <= nu -> 0 <= dt ->
  (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) ->
  2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  4 * dt * (M * M)
    * (inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K))
    * inject_Z (Z.of_nat (K * K)) * modal_energy K a0 <= nu ->
  energy_decreasing K (gtraj nu B K dt a0) /\
  enstrophy_decreasing K (gtraj nu B K dt a0) /\
  (forall n, energy_at K (gtraj nu B K dt a0) n <= energy_at K (gtraj nu B K dt a0) 0 /\
             enstrophy_at K (gtraj nu B K dt a0) n <= enstrophy_at K (gtraj nu B K dt a0) 0).
Proof.
  intros nu B K dt M a0 HB Hs Hnu Hdt Hbd Hc1 Hc2.
  (* the condition of the energy estimate follows *)
  assert (Hc3 : 4 * dt * (M * M)
                * (inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K))
                * modal_energy K a0 <= nu).
  { pose proof (modal_energy_nonneg K a0) as HE0.
    pose proof (inject_nat_nonneg_ns K) as HK0.
    destruct (Nat.eq_dec K 0) as [HK | HK].
    - assert (EK : inject_Z (Z.of_nat K) == 0) by (rewrite HK; reflexivity).
      rewrite EK.
      assert (E : 4 * dt * (M * M) * (0 * 0 * 0) * modal_energy K a0 == 0) by ring.
      rewrite E. exact Hnu.
    - assert (HW1 : 1 <= inject_Z (Z.of_nat (K * K))).
      { change 1 with (inject_Z 1). rewrite <- Zle_Qle.
        change 1%Z with (Z.of_nat 1). apply Nat2Z.inj_le. nia. }
      set (W := inject_Z (Z.of_nat (K * K))) in *.
      set (Kq := inject_Z (Z.of_nat K)) in *.
      set (x := 4 * dt * (M * M) * (Kq * Kq * Kq) * modal_energy K a0).
      assert (Hx0 : 0 <= x).
      { unfold x. apply Qmult_le_0_compat; [ | exact HE0 ].
        apply Qmult_le_0_compat.
        - apply Qmult_le_0_compat; [ lra | apply Qsq_nonneg ].
        - apply Qmult_le_0_compat; [ apply Qsq_nonneg | exact HK0 ]. }
      assert (Hx : x * 1 <= x * W) by (apply qmul_le_l; assumption).
      assert (E : x * W == 4 * dt * (M * M) * (Kq * Kq * Kq) * W * modal_energy K a0)
        by (unfold x; ring).
      rewrite E in Hx. lra. }
  destruct (galerkin_traj_energy_apriori nu B K dt M a0 HB Hnu Hdt Hbd Hc1 Hc3)
    as [Hdec HEn].
  assert (Hdec2 : enstrophy_decreasing K (gtraj nu B K dt a0)).
  { intro n. unfold enstrophy_at. cbn [gtraj].
    apply (small_step_enstrophy_le nu B K dt M (modal_energy K a0) _
             (Hs _) Hnu Hdt Hbd Hc1 Hc2).
    apply HEn. }
  split; [ exact Hdec | split; [ exact Hdec2 | ] ].
  apply full_regularity_2d; assumption.
Qed.

(** The triad: for every initial state and every step with
    18 dt nu <= 1 and 62208 dt E(a0) <= nu. *)
Corollary triad_traj_regular : forall nu dt (a0 : modal_state),
  0 <= nu -> 0 <= dt ->
  2 * dt * nu * 9 <= 1 ->
  4 * dt * (8 * 8) * (3 * 3 * 3) * 9 * modal_energy 3 a0 <= nu ->
  forall n, energy_at 3 (gtraj nu Btri 3 dt a0) n <= energy_at 3 (gtraj nu Btri 3 dt a0) 0 /\
            enstrophy_at 3 (gtraj nu Btri 3 dt a0) n
            <= enstrophy_at 3 (gtraj nu Btri 3 dt a0) 0.
Proof.
  intros nu dt a0 Hnu Hdt Hc1 Hc2.
  apply (no_stretching_traj_apriori nu Btri 3 dt 8 a0
           Btri_energy_conserving Btri_no_stretching Hnu Hdt
           (fun k l m _ _ _ => Btri_bound k l m) Hc1 Hc2).
Qed.

(* ===================================================================== *)
(*  4. The invariant region: a theorem about the step of the scheme        *)
(* ===================================================================== *)

(** The Euler step of the system with an arbitrary nonlinear term Nl, in the
    numbering of InvariantRegion.v: the modes k = 1..K, the damping nu k^2. *)
Definition gstep_gen (nu dt : Q) (Nl : modal_state -> nat -> Q) (a : modal_state)
  : modal_state :=
  fun k => a k + dt * (- (nu * inject_Z (Z.of_nat (k * k)) * a k) + Nl a k).

Fixpoint giter (nu dt : Q) (Nl : modal_state -> nat -> Q) (a : modal_state) (n : nat)
  : modal_state :=
  match n with
  | O => a
  | S m => gstep_gen nu dt Nl (giter nu dt Nl a m)
  end.

(** If in the region the nonlinear term of the mode k does not exceed the
    boundary damping, and dt nu K^2 <= 1, the step keeps the region. *)
Theorem region_invariant_step :
  forall (nsc : NSCoupling) nu dt K (Nl : modal_state -> nat -> Q) (a : modal_state),
  0 < nu -> 0 <= dt ->
  dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  (forall k, (1 <= k)%nat -> (k <= K)%nat ->
     Qabs (Nl a k) <= boundary_damping nu k) ->
  in_region nu K a ->
  in_region nu K (gstep_gen nu dt Nl a).
Proof.
  intros nsc nu dt K Nl a Hnu Hdt Hcfl HN Hin k Hk1 HkK.
  unfold gstep_gen.
  pose proof (Hin k Hk1 HkK) as Ha.
  pose proof (HN k Hk1 HkK) as HNk. unfold boundary_damping in HNk.
  pose proof (A_inv_positive nu Hnu) as HA.
  remember (inject_Z (Z.of_nat k)) as kq eqn:Ekq.
  assert (Hkq : 1 <= kq).
  { subst kq. change 1 with (inject_Z 1). rewrite <- Zle_Qle. lia. }
  assert (Hk2 : inject_Z (Z.of_nat (k * k)) == kq * kq).
  { subst kq. rewrite Nat2Z.inj_mul. rewrite inject_Z_mult. reflexivity. }
  assert (HKK : inject_Z (Z.of_nat (k * k)) <= inject_Z (Z.of_nat (K * K))).
  { rewrite <- Zle_Qle. apply Nat2Z.inj_le. nia. }
  assert (Hk20 : 0 <= inject_Z (Z.of_nat (k * k))) by apply inject_nat_nonneg_ns.
  remember (dt * nu * inject_Z (Z.of_nat (k * k))) as c eqn:Ec.
  assert (Hc0 : 0 <= c).
  { subst c. apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; lra | exact Hk20 ]. }
  assert (Hc1 : c <= 1).
  { subst c. apply Qle_trans with (dt * nu * inject_Z (Z.of_nat (K * K))); [ | exact Hcfl ].
    apply qmul_le_l; [ exact HKK | apply Qmult_le_0_compat; lra ]. }
  assert (E : a k + dt * (- (nu * inject_Z (Z.of_nat (k * k)) * a k) + Nl a k)
              == (1 - c) * a k + dt * Nl a k) by (subst c; ring).
  rewrite E.
  eapply Qle_trans; [ apply Qabs_triangle | ].
  rewrite !Qabs_Qmult.
  rewrite (Qabs_pos (1 - c)) by lra.
  rewrite (Qabs_pos dt) by exact Hdt.
  assert (B1 : (1 - c) * Qabs (a k) <= (1 - c) * (A_inv nu / kq)).
  { apply qmul_le_l; [ exact Ha | lra ]. }
  assert (B2 : dt * Qabs (Nl a k) <= dt * (nu * kq * A_inv nu)).
  { apply qmul_le_l; [ exact HNk | exact Hdt ]. }
  assert (Hfin : (1 - c) * (A_inv nu / kq) + dt * (nu * kq * A_inv nu) == A_inv nu / kq).
  { subst c. rewrite Hk2. field. lra. }
  lra.
Qed.

(** The conditional theorem on the trajectory: an initial state in the region,
    a bound of the nonlinear term in the region, a condition on the step — and
    the whole trajectory of the scheme stays in the region. *)
Theorem region_invariant_iter :
  forall (nsc : NSCoupling) nu dt K (Nl : modal_state -> nat -> Q) (a0 : modal_state),
  0 < nu -> 0 <= dt ->
  dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  (forall b, in_region nu K b ->
     forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (Nl b k) <= boundary_damping nu k) ->
  in_region nu K a0 ->
  forall n, in_region nu K (giter nu dt Nl a0 n).
Proof.
  intros nsc nu dt K Nl a0 Hnu Hdt Hcfl HN Hin n.
  induction n as [|m IH].
  - exact Hin.
  - cbn [giter]. apply region_invariant_step; try assumption.
    apply HN. exact IH.
Qed.

(** The contribution of every mode to the enstrophy on the whole trajectory
    does not exceed A^2. *)
Corollary region_iter_mode_enstrophy :
  forall (nsc : NSCoupling) nu dt K (Nl : modal_state -> nat -> Q) (a0 : modal_state),
  0 < nu -> 0 <= dt ->
  dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  (forall b, in_region nu K b ->
     forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (Nl b k) <= boundary_damping nu k) ->
  in_region nu K a0 ->
  forall n k, (1 <= k)%nat -> (k <= K)%nat ->
    inject_Z (Z.of_nat (k * k)) * (giter nu dt Nl a0 n k * giter nu dt Nl a0 n k)
    <= A_inv nu * A_inv nu.
Proof.
  intros nsc nu dt K Nl a0 Hnu Hdt Hcfl HN Hin n k Hk1 HkK.
  pose proof (region_invariant_iter nsc nu dt K Nl a0 Hnu Hdt Hcfl HN Hin n) as Hreg.
  pose proof (region_implies_sq_bound nu K _ k Hnu Hreg Hk1 HkK) as Hsq.
  remember (inject_Z (Z.of_nat k)) as kq eqn:Ekq.
  assert (Hkq : 1 <= kq).
  { subst kq. change 1 with (inject_Z 1). rewrite <- Zle_Qle. lia. }
  assert (Hk2 : inject_Z (Z.of_nat (k * k)) == kq * kq).
  { subst kq. rewrite Nat2Z.inj_mul. rewrite inject_Z_mult. reflexivity. }
  rewrite Hk2.
  assert (Hpos : 0 <= kq * kq) by (apply Qmult_le_0_compat; lra).
  apply Qle_trans with (kq * kq * ((A_inv nu / kq) * (A_inv nu / kq))).
  - apply qmul_le_l; [ exact Hsq | exact Hpos ].
  - assert (E : kq * kq * ((A_inv nu / kq) * (A_inv nu / kq)) == A_inv nu * A_inv nu).
    { field. lra. }
    rewrite E. apply Qle_refl.
Qed.

(** For the nonlinear term with B_coeff the bound holds trivially: it is zero. *)
Corollary formal_region_invariant :
  forall (nsc : NSCoupling) nu dt K (a0 : modal_state),
  0 < nu -> 0 <= dt ->
  dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  in_region nu K a0 ->
  forall n, in_region nu K (giter nu dt (fun b k => inner_double_sum K k b) a0 n).
Proof.
  intros nsc nu dt K a0 Hnu Hdt Hcfl Hin n.
  apply region_invariant_iter; try assumption.
  intros b _ k Hk1 _.
  assert (E : Qabs (inner_double_sum K k b) == 0).
  { rewrite (nl_mode_zero nsc K k b). reflexivity. }
  rewrite E. apply Qlt_le_weak. apply boundary_damping_positive; assumption.
Qed.

(* ===================================================================== *)
(*  5. The bound of the nonlinear term does not follow from the record     *)
(* ===================================================================== *)

(** A record of premises without a selection rule of triads. *)
Definition B_ex (k l m : nat) : Q :=
  if ((l =? 1) && (m =? 2))%nat then 1 else 0.

Lemma B_ex_bound : forall k l m : nat,
  Qabs (B_ex k l m - B_ex k m l)
  <= 1 * inject_Z (Z.of_nat (Nat.max k (Nat.max l m))).
Proof.
  intros k l m. unfold B_ex.
  assert (Hnn : 0 <= 1 * inject_Z (Z.of_nat (Nat.max k (Nat.max l m)))).
  { rewrite Qmult_1_l. apply inject_nat_nonneg_ns. }
  destruct (Nat.eqb_spec l 1) as [Hl1|Hl1]; destruct (Nat.eqb_spec m 2) as [Hm2|Hm2];
  destruct (Nat.eqb_spec m 1) as [Hm1|Hm1]; destruct (Nat.eqb_spec l 2) as [Hl2|Hl2];
  cbn [andb]; try lia;
  try (assert (E0 : Qabs (0 - 0) == 0) by reflexivity; rewrite E0; exact Hnn).
  - assert (E1 : Qabs (1 - 0) == 1) by reflexivity. rewrite E1.
    rewrite Qmult_1_l. change 1 with (inject_Z 1) at 1. rewrite <- Zle_Qle. lia.
  - assert (E1 : Qabs (0 - 1) == 1) by reflexivity. rewrite E1.
    rewrite Qmult_1_l. change 1 with (inject_Z 1) at 1. rewrite <- Zle_Qle. lia.
Qed.

Definition ex_coupling : NSCoupling.
Proof.
  refine (mkNSCoupling B_ex 1 _ B_ex_bound). reflexivity.
Defined.

Definition a_ex : modal_state :=
  fun k => match k with
           | S O => 1
           | S (S O) => 1 # 2
           | _ => 0
           end.

Lemma a_ex_in_region : @in_region ex_coupling 1 3 a_ex.
Proof.
  intros k Hk1 HkK.
  assert (Hk : k = 1%nat \/ k = 2%nat \/ k = 3%nat) by lia.
  destruct Hk as [-> | [-> | ->]]; vm_compute; discriminate.
Qed.

(** A state in the region and the mode 1: the majorant of the nonlinear term
    (mode_forcing of TriadicInteraction.v) is 1, while the number
    forcing_in_region of InvariantRegion.v is 0. *)
Lemma forcing_in_region_not_a_bound :
  @forcing_in_region ex_coupling 1 1 == 0 /\
  @mode_forcing ex_coupling 1 3 a_ex == 1.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions no_stretching_traj_apriori.
Print Assumptions triad_traj_regular.
Print Assumptions region_invariant_iter.
Print Assumptions forcing_in_region_not_a_bound.
