(* ========================================================================= *)
(*         GRADIENT DESCENT CONVERGENCE FOR QUADRATIC LOSS                  *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove gradient descent on quadratic loss converges:            *)
(*    - Weight sequence converges to optimum                                *)
(*    - Loss sequence converges to 0                                        *)
(*    - Geometric convergence rate with contraction factor                  *)
(*    - Optimal learning rate eta = 1/2 gives 1-step convergence           *)
(*                                                                          *)
(*  AXIOMS: classic (inherited from MonotoneConvergence via SeriesConv)     *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import MonotoneConvergence.
From ToS Require Import SeriesConvergence.
From ToS Require Import PowerSeries.

Open Scope Q_scope.

(* ========================================================================= *)
(* DEFINITIONS                                                                *)
(* ========================================================================= *)

(** Valid learning rate: 0 < η < 1 *)
Definition valid_lr (eta : Q) : Prop := 0 < eta /\ eta < 1.

(** Contraction factor: c = 1 - 2η *)
Definition contraction (eta : Q) : Q := 1 - 2 * eta.

(** GD error sequence: e_0 = initial error, e_{n+1} = c · e_n *)
Fixpoint gd_error (e0 : Q) (eta : Q) (n : nat) : Q :=
  match n with
  | 0%nat => e0
  | S k => contraction eta * gd_error e0 eta k
  end.

(** Weight sequence: w_n = w* + e_n *)
Definition gd_weight (w0 wstar eta : Q) (n : nat) : Q :=
  wstar + gd_error (w0 - wstar) eta n.

(** Quadratic loss at step n: L_n = e_n² *)
Definition gd_loss (e0 eta : Q) (n : nat) : Q :=
  gd_error e0 eta n * gd_error e0 eta n.

(* ========================================================================= *)
(* SECTION 1: HELPERS                                                         *)
(* ========================================================================= *)

(** r^n · r^n = (r·r)^n *)
Lemma Qpow_square : forall (c : Q) (n : nat),
  Qpow c n * Qpow c n == Qpow (c * c) n.
Proof.
  intros c n. induction n; cbn [Qpow].
  - ring.
  - transitivity ((c * Qpow c n) * (c * Qpow c n)).
    + reflexivity.
    + transitivity (c * c * (Qpow c n * Qpow c n)).
      * ring.
      * apply Qmult_comp; [reflexivity | exact IHn].
Qed.

(** Scaling a Cauchy sequence by a constant preserves Cauchy *)
Lemma cauchy_scale_const : forall (f : nat -> Q) (c : Q),
  is_cauchy f -> is_cauchy (fun n => f n * c).
Proof.
  intros f c Hf eps Heps.
  destruct (Qeq_dec c 0) as [Hc0 | Hcnz].
  - (* c == 0: sequence is constantly 0 *)
    exists 0%nat. intros m n _ _.
    assert (H1 : f m * c == 0).
    { transitivity (f m * 0). - apply Qmult_comp; [reflexivity | exact Hc0]. - ring. }
    assert (H2 : f n * c == 0).
    { transitivity (f n * 0). - apply Qmult_comp; [reflexivity | exact Hc0]. - ring. }
    assert (H3 : f m * c - f n * c == 0) by lra.
    qabs_rw H3. rewrite Qabs_pos; lra.
  - (* c ≠ 0: use eps / |c| *)
    assert (Hc_pos : 0 < Qabs c).
    { destruct (Qlt_le_dec c 0).
      - rewrite Qabs_neg; lra.
      - rewrite Qabs_pos; [|lra].
        destruct (Qlt_le_dec 0 c); [lra | exfalso; apply Hcnz; lra]. }
    assert (Heps' : 0 < eps * / Qabs c).
    { apply Qmult_lt_0_compat; [exact Heps | apply Qinv_lt_0_compat; exact Hc_pos]. }
    destruct (Hf (eps * / Qabs c) Heps') as [N0 HN0].
    exists N0. intros m n Hm Hn.
    assert (Heq : f m * c - f n * c == (f m - f n) * c) by ring.
    qabs_rw Heq.
    rewrite Qabs_Qmult.
    specialize (HN0 m n Hm Hn).
    assert (Hbound : Qabs (f m - f n) * Qabs c < eps * / Qabs c * Qabs c).
    { apply Qmult_lt_compat_r; [exact Hc_pos | exact HN0]. }
    assert (Hcancel : eps * / Qabs c * Qabs c == eps).
    { field. lra. }
    lra.
Qed.

(** |1 - 2η| < 1 when 0 < η < 1 *)
Lemma contraction_abs_lt_1 : forall (eta : Q),
  valid_lr eta -> Qabs (contraction eta) < 1.
Proof.
  intros eta [Heta_pos Heta_lt1].
  unfold contraction.
  destruct (Qlt_le_dec (1 - 2 * eta) 0) as [Hneg | Hpos].
  - rewrite Qabs_neg; lra.
  - rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: ERROR PROPERTIES                                                *)
(* ========================================================================= *)

(** e_n = c^n · e_0 *)
Lemma gd_error_pow : forall (e0 eta : Q) (n : nat),
  gd_error e0 eta n == Qpow (contraction eta) n * e0.
Proof.
  intros e0 eta n. induction n; cbn [gd_error Qpow].
  - ring.
  - transitivity (contraction eta * (Qpow (contraction eta) n * e0)).
    + apply Qmult_comp; [reflexivity | exact IHn].
    + ring.
Qed.

(** |e_n| = |c|^n · |e_0| *)
Lemma gd_error_abs : forall (e0 eta : Q) (n : nat),
  Qabs (gd_error e0 eta n) == Qpow (Qabs (contraction eta)) n * Qabs e0.
Proof.
  intros e0 eta n.
  assert (Hpow := gd_error_pow e0 eta n).
  assert (Habs := Qabs_wd _ _ Hpow).
  rewrite Qabs_Qmult in Habs.
  rewrite Qabs_Qpow in Habs.
  exact Habs.
Qed.

(** Error vanishes: ∀ε>0, ∃N, |e_N| < ε *)
Lemma gd_error_vanish : forall (e0 eta eps : Q),
  valid_lr eta -> 0 < eps ->
  exists N : nat, Qabs (gd_error e0 eta N) < eps.
Proof.
  intros e0 eta eps Heta Heps.
  assert (Hc := contraction_abs_lt_1 eta Heta).
  assert (Hc_nn : 0 <= Qabs (contraction eta)) by (apply Qabs_nonneg).
  destruct (Qeq_dec e0 0) as [He0 | He0_nz].
  - (* e0 == 0: |e_0| = 0 < eps *)
    exists 0%nat. cbn [gd_error].
    assert (H := Qabs_wd _ _ He0).
    assert (Habs0 : Qabs 0 == 0) by (rewrite Qabs_pos; lra).
    lra.
  - (* e0 /= 0: use Qpow_vanish or direct *)
    assert (He0_pos : 0 < Qabs e0).
    { destruct (Qlt_le_dec e0 0).
      - rewrite Qabs_neg; lra.
      - rewrite Qabs_pos; [|lra].
        destruct (Qlt_le_dec 0 e0); [lra | exfalso; apply He0_nz; lra]. }
    destruct (Qeq_dec (Qabs (contraction eta)) 0) as [Hc0 | Hcnz].
    + (* |c| == 0: e_1 = c * e0, |c| = 0 so |e_1| = 0 < eps *)
      exists 1%nat.
      assert (Habs1 := gd_error_abs e0 eta 1).
      cbn [Qpow] in Habs1.
      assert (H1 : Qabs (contraction eta) * 1 * Qabs e0 == 0).
      { transitivity (0 * 1 * Qabs e0).
        - apply Qmult_comp; [apply Qmult_comp; [exact Hc0 | reflexivity] | reflexivity].
        - ring. }
      lra.
    + (* |c| > 0: use Qpow_vanish *)
      assert (Hc_pos : 0 < Qabs (contraction eta)).
      { destruct (Qlt_le_dec 0 (Qabs (contraction eta))); [lra |].
        exfalso. apply Hcnz. lra. }
      assert (Heps' : 0 < eps * / Qabs e0).
      { apply Qmult_lt_0_compat; [exact Heps | apply Qinv_lt_0_compat; exact He0_pos]. }
      destruct (Qpow_vanish (Qabs (contraction eta)) (eps * / Qabs e0)
                Hc_pos Hc Heps') as [N HN].
      exists N.
      assert (Habs := gd_error_abs e0 eta N).
      assert (Hbound : Qpow (Qabs (contraction eta)) N * Qabs e0 < eps).
      { assert (H1 : Qpow (Qabs (contraction eta)) N * Qabs e0 <
                      eps * / Qabs e0 * Qabs e0).
        { apply Qmult_lt_compat_r; [exact He0_pos | exact HN]. }
        assert (H2 : eps * / Qabs e0 * Qabs e0 == eps).
        { field. lra. }
        lra. }
      lra.
Qed.

(** Error sequence is Cauchy *)
Theorem gd_error_cauchy : forall (e0 eta : Q),
  valid_lr eta -> is_cauchy (gd_error e0 eta).
Proof.
  intros e0 eta Heta eps Heps.
  assert (Hc := contraction_abs_lt_1 eta Heta).
  assert (Hc_nn : 0 <= Qabs (contraction eta)) by (apply Qabs_nonneg).
  (* Get N such that |c|^n * |e0| < eps/2 for n >= N *)
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (gd_error_vanish e0 eta (eps * (1#2)) Heta Heps2) as [N HN].
  exists N. intros m n Hm Hn.
  (* |e_m - e_n| <= |e_m| + |e_n| *)
  assert (Htri : Qabs (gd_error e0 eta m - gd_error e0 eta n) <=
                  Qabs (gd_error e0 eta m) + Qabs (gd_error e0 eta n)).
  { assert (H := Qabs_triangle (gd_error e0 eta m) (-(gd_error e0 eta n))).
    rewrite Qabs_opp in H.
    (* H : |a + (-b)| <= |a| + |b| *)
    assert (Heq : gd_error e0 eta m - gd_error e0 eta n ==
                   gd_error e0 eta m + - gd_error e0 eta n) by ring.
    assert (Habs_eq := Qabs_wd _ _ Heq).
    lra. }
  (* |e_m| < eps/2, |e_n| < eps/2 *)
  assert (Hm' : Qabs (gd_error e0 eta m) < eps * (1#2)).
  { (* Need |e_m| < eps/2 for m >= N *)
    assert (Habs_m := gd_error_abs e0 eta m).
    assert (Habs_N := gd_error_abs e0 eta N).
    (* |e_m| = |c|^m * |e0| <= |c|^N * |e0| = |e_N| < eps/2 *)
    assert (Hdec : Qpow (Qabs (contraction eta)) m <=
                    Qpow (Qabs (contraction eta)) N).
    { apply dec_le; [| exact Hm].
      intros k. apply Qpow_monotone_dec; [exact Hc_nn | lra]. }
    assert (Hann : 0 <= Qabs e0) by (apply Qabs_nonneg).
    assert (Hprod : Qpow (Qabs (contraction eta)) m * Qabs e0 <=
                     Qpow (Qabs (contraction eta)) N * Qabs e0).
    { apply Qmult_le_compat_r; [exact Hdec | exact Hann]. }
    lra. }
  assert (Hn' : Qabs (gd_error e0 eta n) < eps * (1#2)).
  { assert (Habs_n := gd_error_abs e0 eta n).
    assert (Habs_N := gd_error_abs e0 eta N).
    assert (Hdec : Qpow (Qabs (contraction eta)) n <=
                    Qpow (Qabs (contraction eta)) N).
    { apply dec_le; [| exact Hn].
      intros k. apply Qpow_monotone_dec; [exact Hc_nn | lra]. }
    assert (Hann : 0 <= Qabs e0) by (apply Qabs_nonneg).
    assert (Hprod : Qpow (Qabs (contraction eta)) n * Qabs e0 <=
                     Qpow (Qabs (contraction eta)) N * Qabs e0).
    { apply Qmult_le_compat_r; [exact Hdec | exact Hann]. }
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: WEIGHT CONVERGENCE                                              *)
(* ========================================================================= *)

(** w_n - w* = e_n *)
Lemma gd_weight_eq : forall (w0 wstar eta : Q) (n : nat),
  gd_weight w0 wstar eta n - wstar == gd_error (w0 - wstar) eta n.
Proof.
  intros. unfold gd_weight. ring.
Qed.

(** Weight sequence is Cauchy *)
Theorem gd_weight_cauchy : forall (w0 wstar eta : Q),
  valid_lr eta -> is_cauchy (gd_weight w0 wstar eta).
Proof.
  intros w0 wstar eta Heta eps Heps.
  destruct (gd_error_cauchy (w0 - wstar) eta Heta eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  assert (Heq : gd_weight w0 wstar eta m - gd_weight w0 wstar eta n ==
                 gd_error (w0 - wstar) eta m - gd_error (w0 - wstar) eta n).
  { unfold gd_weight. ring. }
  qabs_rw Heq. exact (HN m n Hm Hn).
Qed.

(** Weights converge to w*: |w_n - wstar| -> 0 *)
Theorem gd_weight_converges : forall (w0 wstar eta : Q),
  valid_lr eta ->
  forall eps, 0 < eps ->
  exists N : nat, forall n, (N <= n)%nat ->
    Qabs (gd_weight w0 wstar eta n - wstar) < eps.
Proof.
  intros w0 wstar eta Heta eps Heps.
  destruct (gd_error_vanish (w0 - wstar) eta eps Heta Heps) as [N HN].
  exists N. intros n Hn.
  assert (Heq : gd_weight w0 wstar eta n - wstar ==
                 gd_error (w0 - wstar) eta n).
  { unfold gd_weight. ring. }
  assert (Habs_eq := Qabs_wd _ _ Heq).
  assert (Habs_n := gd_error_abs (w0 - wstar) eta n).
  assert (Habs_N := gd_error_abs (w0 - wstar) eta N).
  assert (Hc := contraction_abs_lt_1 eta Heta).
  assert (Hc_nn : 0 <= Qabs (contraction eta)) by (apply Qabs_nonneg).
  assert (Hdec : Qpow (Qabs (contraction eta)) n <=
                  Qpow (Qabs (contraction eta)) N).
  { apply dec_le; [| exact Hn].
    intros k. apply Qpow_monotone_dec; [exact Hc_nn | lra]. }
  assert (Hann : 0 <= Qabs (w0 - wstar)) by (apply Qabs_nonneg).
  assert (Hprod : Qpow (Qabs (contraction eta)) n * Qabs (w0 - wstar) <=
                   Qpow (Qabs (contraction eta)) N * Qabs (w0 - wstar)).
  { apply Qmult_le_compat_r; [exact Hdec | exact Hann]. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: LOSS PROPERTIES                                                 *)
(* ========================================================================= *)

(** Loss is nonnegative *)
Lemma gd_loss_nonneg : forall (e0 eta : Q) (n : nat),
  0 <= gd_loss e0 eta n.
Proof.
  intros e0 eta n. unfold gd_loss.
  assert (H : 0 <= gd_error e0 eta n * gd_error e0 eta n).
  { destruct (Qlt_le_dec (gd_error e0 eta n) 0).
    - assert (H1 : 0 <= (- gd_error e0 eta n) * (- gd_error e0 eta n)).
      { apply Qmult_le_0_compat; lra. }
      assert (H2 : (- gd_error e0 eta n) * (- gd_error e0 eta n) ==
                     gd_error e0 eta n * gd_error e0 eta n) by ring.
      lra.
    - apply Qmult_le_0_compat; lra. }
  exact H.
Qed.

(** Loss = (c²)^n · e_0² *)
Lemma gd_loss_as_pow : forall (e0 eta : Q) (n : nat),
  gd_loss e0 eta n == Qpow (contraction eta * contraction eta) n * (e0 * e0).
Proof.
  intros e0 eta n. unfold gd_loss.
  assert (Hpow := gd_error_pow e0 eta n).
  assert (H1 : gd_error e0 eta n * gd_error e0 eta n ==
                (Qpow (contraction eta) n * e0) * (Qpow (contraction eta) n * e0)).
  { apply Qmult_comp; exact Hpow. }
  assert (H2 : (Qpow (contraction eta) n * e0) * (Qpow (contraction eta) n * e0) ==
                (Qpow (contraction eta) n * Qpow (contraction eta) n) * (e0 * e0)) by ring.
  assert (Hsq := Qpow_square (contraction eta) n).
  assert (H3 : Qpow (contraction eta) n * Qpow (contraction eta) n * (e0 * e0) ==
                Qpow (contraction eta * contraction eta) n * (e0 * e0)).
  { apply Qmult_comp; [exact Hsq | reflexivity]. }
  lra.
Qed.

(** Loss is decreasing *)
Lemma gd_loss_decreasing : forall (e0 eta : Q) (n : nat),
  valid_lr eta -> gd_loss e0 eta (S n) <= gd_loss e0 eta n.
Proof.
  intros e0 eta n Heta.
  assert (Hc := contraction_abs_lt_1 eta Heta).
  (* gd_loss (S n) = (c · e_n) · (c · e_n) = c² · gd_loss n *)
  assert (Hstep : gd_loss e0 eta (S n) ==
                   contraction eta * contraction eta * gd_loss e0 eta n).
  { unfold gd_loss. cbn [gd_error]. ring. }
  (* c² < 1 *)
  assert (Hc2_lt1 : contraction eta * contraction eta < 1).
  { (* |c| < 1 => c² < 1. Since c² = |c|², use Qabs *)
    assert (Hc2 : contraction eta * contraction eta ==
                   Qabs (contraction eta) * Qabs (contraction eta)).
    { destruct (Qlt_le_dec (contraction eta) 0).
      - rewrite Qabs_neg; [ring | lra].
      - rewrite Qabs_pos; [ring | lra]. }
    assert (Habs_lt1 : Qabs (contraction eta) * Qabs (contraction eta) < 1 * 1).
    { apply Qmult_lt_compat_nonneg.
      - split; [apply Qabs_nonneg | exact Hc].
      - split; [apply Qabs_nonneg | exact Hc]. }
    lra. }
  (* c² * L ≤ L since c² < 1 and L ≥ 0 *)
  assert (Hnn := gd_loss_nonneg e0 eta n).
  assert (Hdiff : 0 <= (1 - contraction eta * contraction eta) * gd_loss e0 eta n).
  { apply Qmult_le_0_compat; lra. }
  lra.
Qed.

(** Loss converges to 0 *)
Theorem gd_loss_converges_zero : forall (e0 eta : Q),
  valid_lr eta ->
  forall eps, 0 < eps ->
  exists N : nat, forall n, (N <= n)%nat -> gd_loss e0 eta n < eps.
Proof.
  intros e0 eta Heta eps Heps.
  assert (Hc := contraction_abs_lt_1 eta Heta).
  (* c² >= 0 and c² < 1 *)
  assert (Hc2_nn : 0 <= contraction eta * contraction eta).
  { destruct (Qlt_le_dec (contraction eta) 0).
    - assert (H : 0 <= (- contraction eta) * (- contraction eta)).
      { apply Qmult_le_0_compat; lra. }
      assert (Heq : (-contraction eta) * (-contraction eta) ==
                      contraction eta * contraction eta) by ring. lra.
    - apply Qmult_le_0_compat; lra. }
  assert (Hc2_lt1 : contraction eta * contraction eta < 1).
  { assert (Hc2 : contraction eta * contraction eta ==
                   Qabs (contraction eta) * Qabs (contraction eta)).
    { destruct (Qlt_le_dec (contraction eta) 0).
      - rewrite Qabs_neg; [ring | lra].
      - rewrite Qabs_pos; [ring | lra]. }
    assert (H1 := Qabs_nonneg (contraction eta)).
    assert (Habs_lt1 : Qabs (contraction eta) * Qabs (contraction eta) < 1 * 1).
    { apply Qmult_lt_compat_nonneg.
      - split; [exact H1 | exact Hc].
      - split; [exact H1 | exact Hc]. }
    lra. }
  destruct (Qeq_dec e0 0) as [He0 | He0_nz].
  - (* e0 == 0: loss is always 0 *)
    exists 0%nat. intros n _.
    assert (Hpow := gd_loss_as_pow e0 eta n).
    assert (He02 : e0 * e0 == 0).
    { transitivity (0 * 0). - apply Qmult_comp; exact He0. - ring. }
    assert (Hz : Qpow (contraction eta * contraction eta) n * (e0 * e0) == 0).
    { transitivity (Qpow (contraction eta * contraction eta) n * 0).
      - apply Qmult_comp; [reflexivity | exact He02].
      - ring. }
    assert (Hnn := gd_loss_nonneg e0 eta n). lra.
  - (* e0 ≠ 0: use Qpow_limit_zero on c² *)
    assert (He02_pos : 0 < e0 * e0).
    { destruct (Qlt_le_dec e0 0).
      - assert (H : 0 < (-e0) * (-e0)).
        { apply Qmult_lt_0_compat; lra. }
        assert (Heq : (-e0)*(-e0) == e0*e0) by ring. lra.
      - destruct (Qlt_le_dec 0 e0).
        + apply Qmult_lt_0_compat; lra.
        + exfalso; apply He0_nz; lra. }
    assert (Heps' : 0 < eps * / (e0 * e0)).
    { apply Qmult_lt_0_compat; [exact Heps | apply Qinv_lt_0_compat; exact He02_pos]. }
    destruct (Qpow_limit_zero (contraction eta * contraction eta) Hc2_nn Hc2_lt1
              (eps * / (e0 * e0)) Heps') as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn).
    assert (Hpow := gd_loss_as_pow e0 eta n).
    assert (Hnn := gd_loss_nonneg e0 eta n).
    assert (Hbound : Qpow (contraction eta * contraction eta) n * (e0 * e0) <
                      eps * / (e0 * e0) * (e0 * e0)).
    { apply Qmult_lt_compat_r; [exact He02_pos | exact HN]. }
    assert (Hcancel : eps * / (e0 * e0) * (e0 * e0) == eps).
    { field. lra. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: CONVERGENCE RATE AND OPTIMAL LR                                 *)
(* ========================================================================= *)

(** Convergence rate: |w_n - w*| ≤ |1-2η|^n · |w_0 - w*| *)
Lemma gd_convergence_rate : forall (w0 wstar eta : Q) (n : nat),
  valid_lr eta ->
  Qabs (gd_weight w0 wstar eta n - wstar) <=
  Qpow (Qabs (contraction eta)) n * Qabs (w0 - wstar).
Proof.
  intros w0 wstar eta n Heta.
  assert (Heq := gd_weight_eq w0 wstar eta n).
  assert (Habs := Qabs_wd _ _ Heq).
  assert (Hrate := gd_error_abs (w0 - wstar) eta n).
  lra.
Qed.

(** Optimal learning rate: η = 1/2 gives contraction = 0 *)
Lemma optimal_lr_contraction : contraction (1#2) == 0.
Proof.
  unfold contraction. ring.
Qed.

(** One-step convergence with optimal LR *)
Lemma optimal_lr_one_step : forall (e0 : Q),
  gd_error e0 (1#2) 1 == 0.
Proof.
  intros e0. cbn [gd_error].
  transitivity (0 * e0).
  - apply Qmult_comp; [exact optimal_lr_contraction | reflexivity].
  - ring.
Qed.

(** Cumulative error bound: Σ|e_k| ≤ |e_0| / (1 - |c|) *)
Lemma gd_cumulative_error : forall (e0 eta : Q) (n : nat),
  valid_lr eta ->
  partial_sum (fun k => Qabs (gd_error e0 eta k)) n <=
  Qabs e0 * / (1 - Qabs (contraction eta)).
Proof.
  intros e0 eta n Heta.
  assert (Hc := contraction_abs_lt_1 eta Heta).
  assert (Hc_nn : 0 <= Qabs (contraction eta)) by (apply Qabs_nonneg).
  (* |e_k| = |c|^k * |e0| *)
  assert (Hterms : partial_sum (fun k => Qabs (gd_error e0 eta k)) n ==
                    partial_sum (fun k => Qabs e0 * Qpow (Qabs (contraction eta)) k) n).
  { apply partial_sum_Qeq. intros k _.
    assert (Habs := gd_error_abs e0 eta k). lra. }
  (* Factor out |e0|: Σ(|e0| * |c|^k) = |e0| * Σ|c|^k *)
  assert (Hscale : partial_sum (fun k => Qabs e0 * Qpow (Qabs (contraction eta)) k) n ==
                    Qabs e0 * partial_sum (fun k => Qpow (Qabs (contraction eta)) k) n).
  { apply partial_sum_scale. }
  (* Geometric bound: Σ|c|^k ≤ 1/(1-|c|) *)
  assert (Hgeo := geometric_partial_sum_bound (Qabs (contraction eta)) n Hc_nn ltac:(lra)).
  (* |e0| * Σ|c|^k ≤ |e0| * 1/(1-|c|) *)
  assert (Hann : 0 <= Qabs e0) by (apply Qabs_nonneg).
  assert (Hinv_pos : 0 < / (1 - Qabs (contraction eta))).
  { apply Qinv_lt_0_compat. lra. }
  assert (Hprod : Qabs e0 * partial_sum (fun k => Qpow (Qabs (contraction eta)) k) n <=
                   Qabs e0 * / (1 - Qabs (contraction eta))).
  { assert (Hdiff : 0 <= Qabs e0 * (/ (1 - Qabs (contraction eta)) -
                    partial_sum (fun k => Qpow (Qabs (contraction eta)) k) n)).
    { apply Qmult_le_0_compat; [exact Hann | lra]. }
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: VERIFICATION                                                    *)
(* ========================================================================= *)

Check Qpow_square.
Check cauchy_scale_const.
Check contraction_abs_lt_1.
Check gd_error_pow.
Check gd_error_abs.
Check gd_error_vanish.
Check gd_error_cauchy.
Check gd_weight_eq.
Check gd_weight_cauchy.
Check gd_weight_converges.
Check gd_loss_nonneg.
Check gd_loss_as_pow.
Check gd_loss_decreasing.
Check gd_loss_converges_zero.
Check gd_convergence_rate.
Check optimal_lr_contraction.
Check optimal_lr_one_step.
Check gd_cumulative_error.

Print Assumptions gd_error_cauchy.
Print Assumptions gd_weight_converges.
Print Assumptions gd_loss_converges_zero.
Print Assumptions gd_cumulative_error.
