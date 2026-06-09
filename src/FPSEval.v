(** * FPSEval.v — АНАЛИТИЧЕСКИЙ МОСТ: eval формального ряда → процесс-число
    Elements: коэффициенты aₙ∈Q и значение x∈Q; на каждой стадии — конечная Q-сумма Σ_{k≤n} aₖxᵏ.
    Roles:    eval = роль-ВЫЧИСЛЕНИЕ формального ряда (FPS, объект-в-теории) в ЧИСЛО-ПРОЦЕСС (CauchySeq);
              мост между формальным миром коэффициентов (FormalPowerSeries) и аналитическим миром
              сходящихся процессов (SeriesConvergence/CauchyReal).
    Rules:    eval a x := series_limit (fun n => aₙ·xⁿ); сходимость при |aₙ|≤1, 0≤x<1 —
              абсолютная мажорация геометрическим рядом (absolute_convergence).

    ЭТА ВЕХА (первый анкер моста): определение eval + перенос ФОРМАЛЬНОГО СЕРДЦА E∘L через eval —
    `eval (fps_compose exp_fps log1m_fps) x ~~ geometric_limit x`: формальная композиция exp∘(−ln(1−·)),
    у которой мы 0-аксиомно доказали коэффициенты ≡1 (compose_exp_log1m_is_geom), ВЫЧИСЛЕННАЯ как
    реальное число-процесс, ЕСТЬ геометрический ряд Σxⁿ = 1/(1−x).  Первое аналитическое следствие
    формального сердца.

    ============ E/R/R разбор ============
      Elements: частичные суммы Σ_{k≤n} aₖxᵏ — конечные Q-данные на стадии n.
      Roles:    eval = вычисление-функции-в-точке как процесс; congruence (равные коэф. ⟹ равный eval);
                anchor geom (eval geom = 1/(1−x)).
      Rules:    мажорация |aₙxⁿ|≤xⁿ (при |aₙ|≤1, x≥0) + Σxⁿ Cauchy ⟹ eval Cauchy; series_limit_wd
                (поточечно равные ряды ⟹ ~~ пределы).
    ДИАГНОСТИКА (P4): eval переводит формальную функцию-процесс (коэффициенты) в число-процесс
      (частичные суммы) — оба «конечно-актуальны» на каждой стадии; мост двух процессных слоёв. 0-аксиомно.

    STATUS: 9 Qed, 0 Admitted, 0 axioms (наследует только classic через SeriesConvergence).
            ГОТОВО: eval (ограниченные коэф., |aₙ|≤1) + сходимость через absolute_convergence; eval_congr;
            ★ eval_geom (eval geom_fps = geometric_limit); ★★ eval_compose_exp_log1m_geom (формальное сердце
            E∘L, вычисленное = 1/(1−x)).
            ОСТАЁТСЯ (трудная половина моста): eval-мультипликативность через Мертенса (eval(a·b)=eval a·eval b);
            закон композиции eval(f∘g) x ~~ eval f (eval g x) (Fubini двойного ряда); анкеры exp/log
            (eval exp_fps t ~~ exp_limit t, eval log1m_fps x ~~ ln_proc x — сдвиг индекса) → exp_R(L(x))~~1/(1−x)
            → горизонт ln_mul L(x)+L(y)~~L(x⊕y).
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.
From ToS Require Import PowerSeries.
From ToS Require Import FormalPowerSeries.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  Конгруэнции Cauchy/series_limit по поточечному равенству            *)
(* ================================================================== *)

(** Поточечно равные последовательности: Cauchy переносится. *)
Lemma is_cauchy_ext : forall f g : nat -> Q,
  (forall n, f n == g n) -> is_cauchy f -> is_cauchy g.
Proof.
  intros f g Hfg Hf eps Heps. destruct (Hf eps Heps) as [N HN]. exists N.
  intros m n Hm Hn. rewrite <- (Hfg m), <- (Hfg n). apply HN; assumption.
Qed.

(** Поточечно равные ряды дают ~~-равные пределы. *)
Lemma series_limit_wd : forall (a b : nat -> Q)
    (Ha : is_cauchy (partial_sum a)) (Hb : is_cauchy (partial_sum b)),
  (forall n, a n == b n) -> series_limit a Ha ~~ series_limit b Hb.
Proof.
  intros a b Ha Hb Hab eps Heps. exists 0%nat. intros n _.
  change (cs_seq (series_limit a Ha) n) with (partial_sum a n).
  change (cs_seq (series_limit b Hb) n) with (partial_sum b n).
  assert (Hps : partial_sum a n == partial_sum b n)
    by (apply partial_sum_ext_le; intros i _; apply Hab).
  rewrite Hps.
  assert (Hz : partial_sum b n - partial_sum b n == 0) by ring.
  rewrite Hz. change (Qabs 0) with (0:Q). exact Heps.
Qed.

(* ================================================================== *)
(*  eval: вычисление формального ряда в число-процесс                   *)
(* ================================================================== *)

(** Члены ряда-значения: aₙ·xⁿ. *)
Definition eval_terms (a : FPS) (x : Q) : nat -> Q := fun n => a n * Qpow x n.

(** ★ Сходимость eval при ограниченных |aₙ|≤1 и 0≤x<1: мажорация Σxⁿ (геометрический). *)
Lemma eval_terms_cauchy_le1 : forall (a : FPS) (x : Q),
  0 <= x -> x < 1 -> (forall n, Qabs (a n) <= 1) ->
  is_cauchy (partial_sum (eval_terms a x)).
Proof.
  intros a x Hx Hx1 Hb.
  apply (absolute_convergence (eval_terms a x) (fun n => Qpow x n)).
  - intro n. unfold eval_terms.
    rewrite Qabs_Qmult, (Qabs_pos (Qpow x n) (Qpow_nonneg x n Hx)).
    rewrite <- (Qmult_1_l (Qpow x n)) at 2.
    apply Qmult_le_compat_r; [ apply Hb | apply Qpow_nonneg; exact Hx ].
  - apply geometric_series_cauchy; [ exact Hx | exact Hx1 ].
Qed.

(** eval a x = Σ aₙxⁿ как число-процесс (с свидетелем сходимости). *)
Definition eval (a : FPS) (x : Q)
  (H : is_cauchy (partial_sum (eval_terms a x))) : CauchySeq :=
  series_limit (eval_terms a x) H.

(** Равные коэффициенты ⟹ равный eval. *)
Lemma eval_congr : forall (a b : FPS) (x : Q)
    (Ha : is_cauchy (partial_sum (eval_terms a x)))
    (Hb : is_cauchy (partial_sum (eval_terms b x))),
  (forall n, a n == b n) -> eval a x Ha ~~ eval b x Hb.
Proof.
  intros a b x Ha Hb Hab. unfold eval. apply series_limit_wd.
  intro n. unfold eval_terms. rewrite (Hab n). reflexivity.
Qed.

(* ================================================================== *)
(*  ★ АНКЕР: eval geom_fps = geometric_limit = 1/(1−x)                  *)
(* ================================================================== *)

(** Коэффициенты geom_fps ограничены 1. *)
Lemma geom_coeff_le1 : forall n, Qabs (geom_fps n) <= 1.
Proof. intro n. unfold geom_fps. rewrite (Qabs_pos 1) by lra. lra. Qed.

Lemma geom_eval_cauchy : forall x, 0 <= x -> x < 1 ->
  is_cauchy (partial_sum (eval_terms geom_fps x)).
Proof. intros x Hx Hx1. apply (eval_terms_cauchy_le1 geom_fps x Hx Hx1 geom_coeff_le1). Qed.

(** ★ eval geom_fps x = geometric_limit x: Σ 1·xⁿ = Σ xⁿ = 1/(1−x). *)
Lemma eval_geom : forall (x : Q) (Hx : 0 <= x) (Hx1 : x < 1)
    (H : is_cauchy (partial_sum (eval_terms geom_fps x))),
  eval geom_fps x H ~~ geometric_limit x Hx Hx1.
Proof.
  intros x Hx Hx1 H. unfold eval, geometric_limit.
  apply series_limit_wd. intro n. unfold eval_terms, geom_fps. ring.
Qed.

(* ================================================================== *)
(*  ★★ ПЕРЕНОС ФОРМАЛЬНОГО СЕРДЦА E∘L через eval                        *)
(* ================================================================== *)

(** Коэффициенты формальной композиции exp∘log1m ограничены 1 (они ≡1 по сердцу). *)
Lemma compose_coeff_le1 : forall n, Qabs (fps_compose exp_fps log1m_fps n) <= 1.
Proof.
  intro n. rewrite (compose_exp_log1m_is_geom n). apply geom_coeff_le1.
Qed.

(** ★★ ФОРМАЛЬНОЕ СЕРДЦЕ E∘L, ВЫЧИСЛЕННОЕ: exp∘(−ln(1−x)), как число-процесс, ЕСТЬ 1/(1−x).
    eval(fps_compose exp_fps log1m_fps) x ~~ eval geom_fps x (равные коэф., сердце) ~~ geometric_limit x.
    Первое аналитическое следствие формального сердца: формальное тождество коэффициентов перенесено
    в реальное равенство чисел-процессов (для геометрической стороны). *)
Theorem eval_compose_exp_log1m_geom : forall (x : Q) (Hx : 0 <= x) (Hx1 : x < 1)
    (H : is_cauchy (partial_sum (eval_terms (fps_compose exp_fps log1m_fps) x))),
  eval (fps_compose exp_fps log1m_fps) x H ~~ geometric_limit x Hx Hx1.
Proof.
  intros x Hx Hx1 H.
  eapply cauchy_equiv_trans.
  - apply (eval_congr (fps_compose exp_fps log1m_fps) geom_fps x H
             (geom_eval_cauchy x Hx Hx1) compose_exp_log1m_is_geom).
  - apply eval_geom.
Qed.

(** Аудит аксиом. *)
Print Assumptions eval_geom.
Print Assumptions eval_compose_exp_log1m_geom.

(* ================================================================== *)
(*  СВОДКА: eval — первый анкер аналитического моста.  Формальное сердце *)
(*  E∘L (compose_exp_log1m_is_geom, 0-аксиомно) перенесено в число-      *)
(*  процесс: вычисленная композиция = 1/(1−x).  ДАЛЕЕ: eval как кольцевой *)
(*  гомоморфизм (через Мертенса) + закон композиции → exp_R(L(x))~~1/(1−x)*)
(*  → горизонт ln_mul.                                                    *)
(* ================================================================== *)
