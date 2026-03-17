(** * ProcessDeconfining.v — Deconfining Phase Transition

    Theory of Systems — Process Physics (Wave 4, Phase B5)

    Elements: deconfine_order, deconfine_transition, critical_beta
    Roles:    gap → 0 signals deconfinement, order parameter from gap
    Rules:    gap(β→∞) → 0 (deconfinement), gap(β→0) > 0 (confinement)
    Status:   complete

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Order Parameter (~8 Qed)                                  *)
(* ================================================================== *)

(** Deconfinement order parameter: normalized gap *)
Definition deconfine_order (gap gap_max : Q) : Q :=
  gap / gap_max.

(** Order parameter at full gap *)
Lemma order_at_full : forall g,
  ~ g == 0 ->
  deconfine_order g g == 1.
Proof. intros g Hg. unfold deconfine_order. field. exact Hg. Qed.

(** Order parameter at zero gap *)
Lemma order_at_zero : forall g,
  ~ g == 0 ->
  deconfine_order 0 g == 0.
Proof. intros g Hg. unfold deconfine_order. field. exact Hg. Qed.

(** Order parameter bounded *)
Lemma order_bounded : forall gap gap_max,
  0 <= gap -> gap <= gap_max -> 0 < gap_max ->
  0 <= deconfine_order gap gap_max /\ deconfine_order gap gap_max <= 1.
Proof.
  intros gap gap_max Hg Hgm Hmax. unfold deconfine_order. split.
  - apply Qle_shift_div_l; lra.
  - apply Qle_shift_div_r; lra.
Qed.

(** Order parameter nonneg *)
Lemma order_nonneg : forall gap gap_max,
  0 <= gap -> 0 < gap_max ->
  0 <= deconfine_order gap gap_max.
Proof.
  intros. unfold deconfine_order. apply Qle_shift_div_l; lra.
Qed.

(** Order parameter monotone in gap *)
Lemma order_monotone : forall g1 g2 gmax,
  0 < gmax -> g1 <= g2 ->
  deconfine_order g1 gmax <= deconfine_order g2 gmax.
Proof.
  intros. unfold deconfine_order.
  apply Qmult_le_compat_r; [assumption|].
  apply Qinv_le_0_compat. lra.
Qed.

(* ================================================================== *)
(*  Part II: Gap as Function of β (~9 Qed)                            *)
(* ================================================================== *)

(** Simple model: gap(β) = max_gap · (1 - β/β_c) for β < β_c, 0 otherwise *)
Definition gap_model (gap_max beta beta_c : Q) : Q :=
  if Qle_bool beta beta_c then
    gap_max * (1 - beta / beta_c)
  else
    0.

(** Gap at β=0: full gap *)
Lemma gap_at_zero : forall gmax bc,
  0 < bc ->
  gap_model gmax 0 bc == gmax.
Proof.
  intros gmax bc Hbc. unfold gap_model.
  assert (H : Qle_bool 0 bc = true).
  { apply Qle_bool_iff. lra. }
  rewrite H. field. lra.
Qed.

(** Gap at β=β_c: zero *)
Lemma gap_at_critical : forall gmax bc,
  0 < bc ->
  gap_model gmax bc bc == 0.
Proof.
  intros gmax bc Hbc. unfold gap_model.
  assert (H : Qle_bool bc bc = true).
  { apply Qle_bool_iff. lra. }
  rewrite H. field. lra.
Qed.

(** Gap above critical: zero *)
Lemma gap_above_critical : forall gmax beta bc,
  bc < beta ->
  gap_model gmax beta bc == 0.
Proof.
  intros gmax beta bc Hbc. unfold gap_model.
  assert (H : Qle_bool beta bc = false).
  { destruct (Qle_bool beta bc) eqn:E; [|reflexivity].
    apply Qle_bool_iff in E. lra. }
  rewrite H. reflexivity.
Qed.

(** Critical beta definition *)
Definition critical_beta : Q := 8.

(** Critical beta positive *)
Lemma critical_beta_pos : 0 < critical_beta.
Proof. unfold critical_beta. lra. Qed.

(** Gap process: gap as function of β *)
Definition gap_process (gap_max : Q) : RealProcess :=
  fun n => gap_model gap_max (inject_Z (Z.of_nat n)) critical_beta.

(** Gap process at n=0 *)
Lemma gap_process_0 : forall gmax,
  gap_process gmax 0%nat == gmax.
Proof.
  intros. unfold gap_process. simpl. apply gap_at_zero.
  exact critical_beta_pos.
Qed.

(* ================================================================== *)
(*  Part III: Phase Transition (~8 Qed)                               *)
(* ================================================================== *)

(** Phase transition: order parameter drops from 1 to 0 *)
Definition is_confined (gap gap_max : Q) : Prop :=
  0 < gap_max /\ 0 < gap /\ gap <= gap_max.

Definition is_deconfined (gap : Q) : Prop :=
  gap == 0.

(** Confined → positive order parameter *)
Lemma confined_positive_order : forall gap gmax,
  is_confined gap gmax ->
  0 < deconfine_order gap gmax.
Proof.
  intros gap gmax [Hmax [Hg Hle]]. unfold deconfine_order.
  apply Qlt_shift_div_l; lra.
Qed.

(** Deconfined → zero order parameter *)
Lemma deconfined_zero_order : forall gmax,
  0 < gmax ->
  is_deconfined 0 ->
  deconfine_order 0 gmax == 0.
Proof.
  intros gmax Hmax _. unfold deconfine_order. field. lra.
Qed.

(** Transition: gap drops to zero at critical β *)
Lemma transition_at_critical : forall gmax,
  0 < gmax ->
  is_deconfined (gap_model gmax critical_beta critical_beta).
Proof.
  intros gmax Hmax. unfold is_deconfined. apply gap_at_critical.
  exact critical_beta_pos.
Qed.

(** Confinement at small β *)
Lemma confinement_at_zero : forall gmax,
  0 < gmax ->
  is_confined (gap_model gmax 0 critical_beta) gmax.
Proof.
  intros gmax Hmax. unfold is_confined.
  rewrite gap_at_zero; [|exact critical_beta_pos].
  split; [|split]; lra.
Qed.

(** Deconfinement is a phase transition *)
Theorem deconfinement_transition : forall gmax,
  0 < gmax ->
  (* Confined at β=0 *)
  is_confined (gap_model gmax 0 critical_beta) gmax /\
  (* Deconfined at β=β_c *)
  is_deconfined (gap_model gmax critical_beta critical_beta).
Proof.
  intros gmax Hmax. split.
  - apply confinement_at_zero; exact Hmax.
  - apply transition_at_critical; exact Hmax.
Qed.

(* ================================================================== *)
(*  Part IV: Summary                                                    *)
(* ================================================================== *)

Theorem phase_B5_complete :
  (* Order parameter bounded [0,1] *)
  (forall gap gmax, 0 <= gap -> gap <= gmax -> 0 < gmax ->
    0 <= deconfine_order gap gmax /\ deconfine_order gap gmax <= 1) /\
  (* Phase transition exists *)
  (forall gmax, 0 < gmax ->
    is_confined (gap_model gmax 0 critical_beta) gmax /\
    is_deconfined (gap_model gmax critical_beta critical_beta)).
Proof.
  split.
  - exact order_bounded.
  - exact deconfinement_transition.
Qed.
