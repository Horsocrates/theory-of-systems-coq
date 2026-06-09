(** * LnMulComposition.v — внешняя половина композиционной теоремы ln_mul (домината)
    Elements: коэффициенты log1m/gᵏ ≥0; частичные суммы Pₖₙ=Σ_{m≤n}(gᵏ)_m zᵐ; σₙ=Σ_{m≤n} g_m zᵐ.
    Roles:    домината Pₖₙ≤σₙᵏ (n-я стадия eval(gᵏ) ≤ (n-я стадия eval g)ᵏ) — даёт мажоранту Bᵏ
              для теоремы Таннери; σₙ≤1/(1−z) — рациональная граница.
    Rules:    Pₖₙ≤σₙᵏ индукцией по k: P_{S k}=Σ conv(ĝ)(ĝᵏ) ≤ σₙ·Pₖₙ (conv_le_square) ≤ σₙ·σₙᵏ (IH).

    ЭТА ВЕХА (Tannery-кирпич #3 для ln_mul): домината + неотрицательности.  Вместе с теоремой
    Таннери (Tannery.v) и eval_pow (per-k bracket→0) даёт сборку eval(exp∘log1m)~~exp_R(ln_proc).

    STATUS: 5 Qed, 0 Admitted, 0 axioms (наследует classic через FPSEval/анализ).
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.
From ToS Require Import FormalPowerSeries.
From ToS Require Import FPSEval.

Open Scope Q_scope.

(** Коэффициенты log1m_fps неотрицательны. *)
Lemma log1m_nonneg : forall m, 0 <= log1m_fps m.
Proof.
  intro m. unfold log1m_fps. destruct m as [|k]; [ lra | ].
  apply Qlt_le_weak. apply Qinv_lt_0_compat.
  change (0:Q) with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
Qed.

(** Члены eval неотрицательны при z≥0 и неотрицательных коэффициентах. *)
Lemma eval_terms_nonneg : forall (g : FPS) (z : Q), 0 <= z ->
  (forall m, 0 <= g m) -> forall m, 0 <= eval_terms g z m.
Proof.
  intros g z Hz Hg m. unfold eval_terms.
  apply Qmult_le_0_compat; [ apply Hg | apply Qpow_nonneg; exact Hz ].
Qed.

(** Коэффициенты gᵏ неотрицательны (если g неотрицательны). *)
Lemma fps_pow_nonneg : forall (g : FPS), (forall m, 0 <= g m) ->
  forall k m, 0 <= fps_pow g k m.
Proof.
  intros g Hg. induction k as [|k IH]; intro m.
  - cbn [fps_pow]. unfold fps_one. destruct m as [|m']; lra.
  - change (fps_pow g (S k) m) with (conv g (fps_pow g k) m).
    apply conv_nonneg; [ exact Hg | exact IH ].
Qed.

(** σₙ ≤ 1/(1−z): частичная сумма лог-ряда мажорируется геометрической. *)
Lemma sigma_bound : forall (z : Q) (n : nat), 0 <= z -> z < 1 ->
  partial_sum (eval_terms log1m_fps z) n <= / (1 - z).
Proof.
  intros z n Hz Hz1.
  apply Qle_trans with (partial_sum (fun m => Qpow z m) n).
  - apply partial_sum_monotone. intro m. unfold eval_terms.
    destruct m as [|k].
    + cbn [log1m_fps Qpow]. lra.
    + cbn [log1m_fps].
      assert (Hge1 : 1 <= inject_Z (Z.of_nat (S k)))
        by (change (1:Q) with (inject_Z 1); rewrite <- Zle_Qle; lia).
      assert (Hpos : 0 < inject_Z (Z.of_nat (S k))) by lra.
      assert (Hinv1 : / inject_Z (Z.of_nat (S k)) <= 1).
      { apply (Qmult_le_l _ _ (inject_Z (Z.of_nat (S k))) Hpos).
        rewrite Qmult_inv_r by lra. lra. }
      rewrite <- (Qmult_1_l (Qpow z (S k))) at 2.
      apply Qmult_le_compat_r; [ exact Hinv1 | apply Qpow_nonneg; exact Hz ].
  - apply geom_partial_bound; assumption.
Qed.

(** ★★ ДОМИНАТА Pₖₙ ≤ σₙᵏ: n-я стадия eval(gᵏ) ≤ (n-я стадия eval g)ᵏ.
    Индукция по k: P_{S k}=Σ conv(ĝ)(ĝᵏ) ≤ σₙ·Pₖₙ (conv_le_square) ≤ σₙ·σₙᵏ (IH). *)
Lemma P_le_sigma_pow : forall (g : FPS), (forall m, 0 <= g m) -> forall (z : Q), 0 <= z ->
  forall (k n : nat),
  partial_sum (eval_terms (fps_pow g k) z) n
  <= Qpow (partial_sum (eval_terms g z) n) k.
Proof.
  intros g Hg z Hz k. induction k as [|k IH]; intro n.
  - cbn [fps_pow Qpow].
    assert (Hone : partial_sum (eval_terms fps_one z) n == 1).
    { induction n as [|m IHm].
      - cbn [partial_sum]. unfold eval_terms. cbn [fps_one Qpow]. ring.
      - rewrite partial_sum_S.
        assert (Hz0 : eval_terms fps_one z (S m) == 0)
          by (unfold eval_terms; cbn [fps_one]; ring).
        rewrite Hz0, IHm. ring. }
    rewrite Hone. apply Qle_refl.
  - apply Qle_trans with (partial_sum (eval_terms g z) n
                          * partial_sum (eval_terms (fps_pow g k) z) n).
    + change (fps_pow g (S k)) with (fps_mul g (fps_pow g k)).
      rewrite (partial_sum_ext_le (eval_terms (fps_mul g (fps_pow g k)) z)
                (conv (eval_terms g z) (eval_terms (fps_pow g k) z)) n).
      2:{ intros m Hm. apply eval_terms_mul. }
      apply conv_le_square.
      * exact (eval_terms_nonneg g z Hz Hg).
      * exact (eval_terms_nonneg (fps_pow g k) z Hz (fps_pow_nonneg g Hg k)).
    + cbn [Qpow].
      apply Qle_trans with (partial_sum (eval_terms g z) n
                            * Qpow (partial_sum (eval_terms g z) n) k).
      * rewrite (Qmult_comm (partial_sum (eval_terms g z) n)
                            (partial_sum (eval_terms (fps_pow g k) z) n)),
                (Qmult_comm (partial_sum (eval_terms g z) n)
                            (Qpow (partial_sum (eval_terms g z) n) k)).
        apply Qmult_le_compat_r; [ apply IH | ].
        apply partial_sum_nonneg. exact (eval_terms_nonneg g z Hz Hg).
      * apply Qle_lteq; right. ring.
Qed.

(** Аудит аксиом. *)
Print Assumptions P_le_sigma_pow.
Print Assumptions sigma_bound.

(* ================================================================== *)
(*  СВОДКА: домината Pₖₙ≤σₙᵏ + σₙ≤1/(1−z) + неотрицательности.          *)
(*  Tannery-кирпич #3.  ДАЛЕЕ (#4): сборка через tannery + eval_pow +    *)
(*  exp_R_stage + eval_compose_swap ⟹ eval(exp∘log1m)~~exp_R(ln_proc).  *)
(* ================================================================== *)
