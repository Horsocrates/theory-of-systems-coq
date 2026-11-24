(** * GalerkinAdvection.v — The Galerkin system of amplitudes with a nonlinear term that
      transports: a coupling antisymmetric in the tested and the transported mode
      conserves energy while moving it between the modes; the right-hand side, the
      step and the trajectory of the system; the energy rate derived from the
      right-hand side (Part IX, chapter 5)

    Elements: rational amplitudes a_k of the modes k < K; a raw coupling T k l m;
              the viscosity nu; the time step dt; natural numbers n (steps).
    Roles:    nl B K a k = role-nonlinear term of the mode k (k — the tested mode,
              l — the transporting one, m — the transported one);
              adv T k l m = T k l m - T m l k = role-transporting part of the raw
              coupling; grhs = role-right-hand side (the law of velocity of the
              amplitudes); gstep = role-step; gtraj = role-trajectory;
              sum_k a_k F_k(a) = role-energy rate along the right-hand side.
    Rules:    a coupling antisymmetric in (k, m) gives a cubic sum
              sum_k a_k nl_k equal to zero — for every raw coupling and every
              state — while the nonlinear term of a single mode need not vanish.
              A coupling antisymmetric in (l, m) gives nl_k = 0 for every mode:
              the factor a_l a_m is symmetric in (l, m).

    ============ E/R/R разбор ============
      Rules (L5): связь, антисимметричная по проверяемой и переносимой модам
                  (k, m), даёт нулевую кубическую сумму sum_k a_k nl_k при всяком
                  сыром коэффициенте и всяком состоянии — энергия сохраняется, а
                  нелинейный член отдельной моды не обязан быть нулём. Связь,
                  антисимметричная по (l, m), даёт nl_k = 0 для каждой моды.
      Roles (L4): nl — роль-нелинейный член моды; adv T — роль-переносящая часть
                  сырой связи; grhs — роль-правая часть (закон скорости амплитуд);
                  gstep — роль-шаг; gtraj — роль-траектория; sum_k a_k F_k —
                  роль-скорость энергии вдоль правой части.
      Elements  : рациональные амплитуды конечного числа мод на каждом конечном
                  шаге (L1 + P4).
    ДИАГНОСТИКА P4: система — конечный набор рациональных амплитуд и конечные суммы;
    «скорость энергии» — конечная сумма sum_k a_k F_k(a), а не производная;
    траектория — состояние после конечного числа шагов.

    PROVED (all closed under the global context):
      - with the coefficient B_coeff of GalerkinSystem.v (antisymmetric in (l, m))
        the nonlinear term of every mode is zero ([nl_mode_zero],
        [antisym_quadratic_form_zero], [lm_antisym_nl_zero]), and the right-hand
        side of the system is the viscous one ([grhs_formal_is_viscous]);
      - for every raw coupling T the cubic energy sum with adv T is zero
        ([adv_energy_zero]; for the raw coupling of the record NSCoupling —
        [raw_coupling_adv_energy_zero]);
      - the transport between the modes is nonzero: on two modes the system is
        da_0 = a_0 a_1, da_1 = - a_0^2 ([adv_pair_nl], [adv_nl_nonzero]);
      - the right-hand side, the step and the trajectory of the system ([grhs],
        [gstep], [gtraj]); without coupling the step is the viscous one
        ([gstep_zero_coupling]);
      - the energy rate along the right-hand side is DERIVED:
        sum_k a_k F_k(a) = - 2 nu Omega(a) ([galerkin_energy_rate]); it is
        nonpositive for nu >= 0 and zero for nu = 0;
      - the exact energy identity of one step of the explicit scheme
        ([energy_step_identity], [galerkin_step_energy]);
      - one computed step: a mode gains what the other loses to first order
        ([galerkin_transfer_example]).

    NOT claimed: that the coefficients of real advection (a projection of
    (u . grad) u onto a basis) are an instance; a selection rule of triads;
    pressure and incompressibility; any bound of the coupling; estimates in time
    (they are the subject of the next file); a continuous-time solution.

    STATUS: 23 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The nonlinear term of a mode for an arbitrary coupling              *)
(* ===================================================================== *)

(** k — the tested mode, l — the transporting one, m — the transported one. *)
Definition nl (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) (k : nat) : Q :=
  sum_Q_ns (fun l => sum_Q_ns (fun m => B k l m * a l * a m) K) K.

Lemma nl_zero_coupling : forall K (a : nat -> Q) k, nl (fun _ _ _ => 0) K a k == 0.
Proof.
  intros K a k. unfold nl.
  rewrite (sum_ns_ext (fun l => sum_Q_ns (fun m => 0 * a l * a m) K) (fun _ => 0) K).
  - apply sum_ns_zero_fn.
  - intros l _.
    rewrite (sum_ns_ext (fun m => 0 * a l * a m) (fun _ => 0) K) by (intros; ring).
    apply sum_ns_zero_fn.
Qed.

(* ===================================================================== *)
(*  2. The coupling antisymmetric in (l, m): every mode gets zero          *)
(* ===================================================================== *)

(** A quadratic form with a coefficient antisymmetric in its two indices is zero. *)
Lemma antisym_quadratic_form_zero : forall (B : nat -> nat -> Q) K (a : nat -> Q),
  (forall l m, B l m == - B m l) ->
  sum_Q_ns (fun l => sum_Q_ns (fun m => B l m * a l * a m) K) K == 0.
Proof.
  intros B K a HB.
  set (S := sum_Q_ns (fun l => sum_Q_ns (fun m => B l m * a l * a m) K) K).
  assert (H1 : S == - sum_Q_ns (fun m => sum_Q_ns (fun l => B l m * a l * a m) K) K).
  { unfold S. rewrite <- sum_ns_neg.
    apply sum_ns_ext. intros m _. rewrite <- sum_ns_neg.
    apply sum_ns_ext. intros l _. rewrite (HB m l). ring. }
  assert (H2 : sum_Q_ns (fun m => sum_Q_ns (fun l => B l m * a l * a m) K) K == S).
  { unfold S. apply (sum_ns_swap K K (fun m l => B l m * a l * a m)). }
  lra.
Qed.

(** Any raw coupling antisymmetrized in (l, m) — as in B_coeff — gives a zero
    nonlinear term of every mode. *)
Lemma lm_antisym_nl_zero : forall (T : nat -> nat -> nat -> Q) K (a : nat -> Q) k,
  nl (fun k l m => T k l m - T k m l) K a k == 0.
Proof.
  intros T K a k. unfold nl.
  apply (antisym_quadratic_form_zero (fun l m => T k l m - T k m l) K a).
  intros l m. ring.
Qed.

(** The same for the coefficient of GalerkinSystem.v, for every record of
    premises: the sum over (l, m) in the equation of the mode k is zero. *)
Lemma nl_Bcoeff_is_inner : forall (nsc : NSCoupling) K (a : modal_state) k,
  nl B_coeff K a k == inner_double_sum K k a.
Proof. intros. reflexivity. Qed.

Lemma nl_mode_zero : forall (nsc : NSCoupling) K k (a : modal_state),
  inner_double_sum K k a == 0.
Proof.
  intros nsc K k a.
  pose proof (inner_double_sum_self_neg K k a) as H. lra.
Qed.

(* ===================================================================== *)
(*  3. The coupling antisymmetric in (k, m): energy is conserved,          *)
(*     the transport is nonzero                                            *)
(* ===================================================================== *)

(** Antisymmetrization in the first and the third index: the form of
    ((u . grad) v, w) = - ((u . grad) w, v). *)
Definition adv (T : nat -> nat -> nat -> Q) (k l m : nat) : Q := T k l m - T m l k.

Lemma adv_antisym : forall T k l m, adv T k l m == - adv T m l k.
Proof. intros. unfold adv. ring. Qed.

Lemma sum_ns_sub : forall f g n,
  sum_Q_ns (fun i => f i - g i) n == sum_Q_ns f n - sum_Q_ns g n.
Proof.
  intros f g n. induction n as [|n IH]; simpl; [ lra | rewrite IH; lra ].
Qed.

(** Reversal of the outer indices of a triple sum. *)
Lemma sum3_rev : forall K (h : nat -> nat -> nat -> Q),
  sum_Q_ns (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => h k l m) K) K) K ==
  sum_Q_ns (fun m => sum_Q_ns (fun l => sum_Q_ns (fun k => h k l m) K) K) K.
Proof.
  intros K h.
  transitivity (sum_Q_ns (fun l => sum_Q_ns (fun k => sum_Q_ns (fun m => h k l m) K) K) K).
  { apply (sum_ns_swap K K (fun k l => sum_Q_ns (fun m => h k l m) K)). }
  transitivity (sum_Q_ns (fun l => sum_Q_ns (fun m => sum_Q_ns (fun k => h k l m) K) K) K).
  { apply sum_ns_ext. intros l _. apply (sum_ns_swap K K (fun k m => h k l m)). }
  apply (sum_ns_swap K K (fun l m => sum_Q_ns (fun k => h k l m) K)).
Qed.

Lemma sum3_sub : forall K (f h : nat -> nat -> nat -> Q),
  sum_Q_ns (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => f k l m - h k l m) K) K) K ==
  sum_Q_ns (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => f k l m) K) K) K
  - sum_Q_ns (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => h k l m) K) K) K.
Proof.
  intros K f h.
  transitivity (sum_Q_ns (fun k =>
      sum_Q_ns (fun l => sum_Q_ns (fun m => f k l m) K) K
      - sum_Q_ns (fun l => sum_Q_ns (fun m => h k l m) K) K) K).
  { apply sum_ns_ext. intros k _.
    transitivity (sum_Q_ns (fun l =>
        sum_Q_ns (fun m => f k l m) K - sum_Q_ns (fun m => h k l m) K) K).
    { apply sum_ns_ext. intros l _. apply sum_ns_sub. }
    apply (sum_ns_sub (fun l => sum_Q_ns (fun m => f k l m) K)
                      (fun l => sum_Q_ns (fun m => h k l m) K) K). }
  apply (sum_ns_sub (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => f k l m) K) K)
                    (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => h k l m) K) K) K).
Qed.

(** Conservation of energy by the nonlinear term: for EVERY raw coupling T and
    every state the cubic sum with adv T is zero. No bound of T is used. *)
Theorem adv_energy_zero : forall T K (a : nat -> Q),
  sum_Q_ns (fun k => a k * nl (adv T) K a k) K == 0.
Proof.
  intros T K a. unfold nl, adv.
  set (g := fun k l m => T k l m * a k * a l * a m).
  transitivity (sum_Q_ns (fun k => sum_Q_ns (fun l =>
                  sum_Q_ns (fun m => g k l m - g m l k) K) K) K).
  { apply sum_ns_ext. intros k _.
    transitivity (sum_Q_ns (fun l => a k *
        sum_Q_ns (fun m => (T k l m - T m l k) * a l * a m) K) K).
    { symmetry.
      apply (sum_ns_scale (a k)
        (fun l => sum_Q_ns (fun m => (T k l m - T m l k) * a l * a m) K) K). }
    apply sum_ns_ext. intros l _.
    transitivity (sum_Q_ns (fun m => a k * ((T k l m - T m l k) * a l * a m)) K).
    { symmetry.
      apply (sum_ns_scale (a k) (fun m => (T k l m - T m l k) * a l * a m) K). }
    apply sum_ns_ext. intros m _. unfold g. ring. }
  rewrite (sum3_sub K (fun k l m => g k l m) (fun k l m => g m l k)).
  pose proof (sum3_rev K (fun k l m => g m l k)) as Hrev. cbv beta in Hrev.
  rewrite Hrev. ring.
Qed.

(** The raw coupling of the record of premises can be taken as T: the bound of
    the record is not needed for the conservation of energy. *)
Corollary raw_coupling_adv_energy_zero : forall (nsc : NSCoupling) K (a : modal_state),
  sum_Q_ns (fun k => a k * nl (adv B_raw) K a k) K == 0.
Proof. intros nsc K a. apply adv_energy_zero. Qed.

(** The transport between the modes is nonzero. A raw coupling of a pair of
    modes: T 0 0 1 = 1, the other values are zero. *)
Definition T_pair (k l m : nat) : Q :=
  match k, l, m with
  | O, O, S O => 1
  | _, _, _ => 0
  end.

(** On two modes the nonlinear term of adv T_pair is the system
    da_0 = a_0 a_1,  da_1 = - a_0^2. *)
Lemma adv_pair_nl : forall a : nat -> Q,
  nl (adv T_pair) 2 a 0%nat == a 0%nat * a 1%nat /\
  nl (adv T_pair) 2 a 1%nat == - (a 0%nat * a 0%nat).
Proof.
  intro a. unfold nl, adv. cbn [sum_Q_ns T_pair]. split; ring.
Qed.

Definition a_unit : nat -> Q := fun _ => 1.

Lemma adv_nl_nonzero :
  nl (adv T_pair) 2 a_unit 0%nat == 1 /\ nl (adv T_pair) 2 a_unit 1%nat == - (1).
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  4. The system: the right-hand side, the step, the trajectory           *)
(* ===================================================================== *)

(** The weight of the mode k in the enstrophy of GalerkinSystem.v: (k+1)^2. *)
Definition wgt (k : nat) : Q := inject_Z (Z.of_nat ((k+1)*(k+1))).

Lemma wgt_pos : forall k, 0 < wgt k.
Proof.
  intro k. unfold wgt. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
Qed.

(** The right-hand side of the equation of the mode k: viscosity + nonlinearity. *)
Definition grhs (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) (k : nat) : Q :=
  - nu * wgt k * a k + nl B K a k.

(** One step of the explicit scheme a^{n+1} = a^n + dt F(a^n). *)
Definition gstep (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (dt : Q) (a : nat -> Q)
  : nat -> Q := fun k => a k + dt * grhs nu B K a k.

(** The state after n steps. *)
Fixpoint gtraj (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (dt : Q)
  (a : modal_state) (n : nat) : modal_state :=
  match n with
  | O => a
  | S m => gstep nu B K dt (gtraj nu B K dt a m)
  end.

Lemma gtraj_S : forall nu B K dt a n,
  gtraj nu B K dt a (S n) = gstep nu B K dt (gtraj nu B K dt a n).
Proof. reflexivity. Qed.

(** With the coefficient of GalerkinSystem.v the right-hand side is the viscous
    one: the nonlinear term does not enter. *)
Lemma grhs_formal_is_viscous : forall (nsc : NSCoupling) nu K (a : modal_state) k,
  grhs nu B_coeff K a k == - nu * wgt k * a k.
Proof.
  intros nsc nu K a k. unfold grhs.
  rewrite (nl_Bcoeff_is_inner nsc K a k), (nl_mode_zero nsc K k a). ring.
Qed.

(** Without coupling the step is the viscous one: every mode is multiplied by
    1 - dt nu (k+1)^2. *)
Lemma gstep_zero_coupling : forall nu K dt (a : nat -> Q) k,
  gstep nu (fun _ _ _ => 0) K dt a k == (1 - dt * nu * wgt k) * a k.
Proof.
  intros nu K dt a k. unfold gstep, grhs. rewrite nl_zero_coupling. ring.
Qed.

(* ===================================================================== *)
(*  5. The energy rate along the right-hand side                           *)
(* ===================================================================== *)

(** The rate of the energy E = (1/2) sum a_k^2 along a right-hand side F is
    sum_k a_k F_k. For the system with adv T it is DERIVED (not put by a
    definition): sum_k a_k F_k(a) = - 2 nu Omega(a). *)
Theorem galerkin_energy_rate : forall nu T K (a : nat -> Q),
  sum_Q_ns (fun k => a k * grhs nu (adv T) K a k) K == - (2) * nu * modal_enstrophy K a.
Proof.
  intros nu T K a. unfold grhs.
  transitivity (sum_Q_ns (fun k => (- nu) * (wgt k * a k * a k)
                                   + a k * nl (adv T) K a k) K).
  { apply sum_ns_ext. intros k _. ring. }
  rewrite (sum_ns_add (fun k => (- nu) * (wgt k * a k * a k))
                      (fun k => a k * nl (adv T) K a k) K).
  rewrite (sum_ns_scale (- nu) (fun k => wgt k * a k * a k) K).
  rewrite (adv_energy_zero T K a).
  unfold modal_enstrophy, wgt. ring.
Qed.

Corollary galerkin_energy_rate_nonpos : forall nu T K (a : nat -> Q),
  0 <= nu -> sum_Q_ns (fun k => a k * grhs nu (adv T) K a k) K <= 0.
Proof.
  intros nu T K a Hnu. rewrite galerkin_energy_rate.
  pose proof (modal_enstrophy_nonneg K a) as HO.
  assert (0 <= 2 * nu * modal_enstrophy K a).
  { apply Qmult_le_0_compat; [ lra | exact HO ]. }
  lra.
Qed.

(** Without viscosity the rate is zero: the nonlinear term alone conserves energy. *)
Corollary galerkin_inviscid_energy_rate : forall T K (a : nat -> Q),
  sum_Q_ns (fun k => a k * grhs 0 (adv T) K a k) K == 0.
Proof. intros T K a. rewrite galerkin_energy_rate. ring. Qed.

(* ===================================================================== *)
(*  6. The energy of one step of the scheme                                *)
(* ===================================================================== *)

Lemma energy_step_identity : forall K (a F : nat -> Q) dt,
  modal_energy K (fun k => a k + dt * F k) ==
  modal_energy K a + dt * sum_Q_ns (fun k => a k * F k) K
  + (1#2) * dt * dt * sum_Q_ns (fun k => F k * F k) K.
Proof.
  intros K a F dt. unfold modal_energy.
  assert (E : sum_Q_ns (fun k => (a k + dt * F k) * (a k + dt * F k)) K ==
              sum_Q_ns (fun k => a k * a k) K
              + ((2 * dt) * sum_Q_ns (fun k => a k * F k) K
                 + (dt * dt) * sum_Q_ns (fun k => F k * F k) K)).
  { transitivity (sum_Q_ns (fun k => a k * a k
                    + ((2 * dt) * (a k * F k) + (dt * dt) * (F k * F k))) K).
    { apply sum_ns_ext. intros k _. ring. }
    rewrite (sum_ns_add (fun k => a k * a k)
               (fun k => (2 * dt) * (a k * F k) + (dt * dt) * (F k * F k)) K).
    rewrite (sum_ns_add (fun k => (2 * dt) * (a k * F k))
               (fun k => (dt * dt) * (F k * F k)) K).
    rewrite (sum_ns_scale (2 * dt) (fun k => a k * F k) K).
    rewrite (sum_ns_scale (dt * dt) (fun k => F k * F k) K).
    reflexivity. }
  rewrite E. ring.
Qed.

(** The exact identity of one step:
    E(a^{n+1}) = E(a^n) - 2 nu dt Omega(a^n) + (1/2) dt^2 sum_k F_k(a^n)^2. *)
Theorem galerkin_step_energy : forall nu T K dt (a : nat -> Q),
  modal_energy K (gstep nu (adv T) K dt a) ==
  modal_energy K a - 2 * nu * dt * modal_enstrophy K a
  + (1#2) * dt * dt
    * sum_Q_ns (fun k => grhs nu (adv T) K a k * grhs nu (adv T) K a k) K.
Proof.
  intros nu T K dt a. unfold gstep.
  rewrite (energy_step_identity K a (grhs nu (adv T) K a) dt).
  rewrite (galerkin_energy_rate nu T K a). ring.
Qed.

(** One computed step without viscosity (two modes, adv T_pair, dt = 1/2, the
    unit state): the mode 0 gets 3/2, the mode 1 gets 1/2; the energy goes from
    1 to 5/4 — the first-order transfer cancels, the second-order term of the
    explicit step remains. *)
Lemma galerkin_transfer_example :
  gtraj 0 (adv T_pair) 2 (1#2) a_unit 1 0%nat == 3#2 /\
  gtraj 0 (adv T_pair) 2 (1#2) a_unit 1 1%nat == 1#2 /\
  modal_energy 2 a_unit == 1 /\
  modal_energy 2 (gtraj 0 (adv T_pair) 2 (1#2) a_unit 1) == 5#4.
Proof.
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; vm_compute; reflexivity.
Qed.

Print Assumptions adv_energy_zero.
Print Assumptions galerkin_energy_rate.
Print Assumptions galerkin_step_energy.
Print Assumptions grhs_formal_is_viscous.
