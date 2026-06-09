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

    STATUS: 17 Qed, 0 Admitted, 0 axioms (наследует только classic через SeriesConvergence).
            ГОТОВО: eval (ограниченные коэф.) + сходимость через absolute_convergence; eval_congr;
            ★ eval_geom (eval geom_fps = geometric_limit); ★★ eval_compose_exp_log1m_geom (формальное сердце
            E∘L, вычисленное = 1/(1−x)); ★★ eval_mul (eval МУЛЬТИПЛИКАТИВЕН: eval(a·b) ~~ eval a · eval b —
            через mertens_cauchy_product + тождество (a·b)ₙxⁿ = conv(aᵢxⁱ)(bⱼxʲ)ₙ [eval_terms_mul]);
            ★ АНКЕРЫ exp/log: eval_exp (eval exp_fps t ~~ exp_limit t — члены совпадают по Qmult_comm) и
            eval_log1m (eval log1m_fps x ~~ ln_proc x — СДВИГ индекса: лишний 0 в начале, partial_sum (S n)=
            log_series_partial n, эквивалентность Cauchy-сдвигов).  Формальные базис-объекты привязаны к
            существующим процессам exp_limit/ln_proc.
            ОСТАЁТСЯ (трудная половина моста): eval-аддитивность (тривиально) + закон композиции
            eval(f∘g) x ~~ Σ fₖ(eval g x)ᵏ (Fubini двойного ряда; внутр. сумма конечна по занулению) →
            exp_R(L(x))~~1/(1−x) → горизонт ln_mul L(x)+L(y)~~L(x⊕y).
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.
From ToS Require Import ExpFunctionalEquation.
From ToS Require Import PowerSeries.
From ToS Require Import zeta.LogZeta.
From ToS Require Import Log2Process.
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

(* ================================================================== *)
(*  ★★ eval — КОЛЬЦЕВОЙ ГОМОМОРФИЗМ (мультипликативность через Мертенса) *)
(* ================================================================== *)

(** Аддитивность степени: x^{i+j} = x^i·x^j. *)
Lemma Qpow_add : forall (x : Q) (i j : nat), Qpow x (i + j) == Qpow x i * Qpow x j.
Proof.
  intros x i j. induction i as [|i IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** ★ Ключевое тождество: (a·b)ₙ·xⁿ = свёртка взвешенных рядов.
    eval_terms (a·b) = conv (eval_terms a) (eval_terms b), т.к. x^i·x^{n−i}=x^n. *)
Lemma eval_terms_mul : forall (a b : FPS) (x : Q) (n : nat),
  eval_terms (fps_mul a b) x n == conv (eval_terms a x) (eval_terms b x) n.
Proof.
  intros a b x n. unfold eval_terms, fps_mul, conv.
  rewrite <- (partial_sum_scale_r (fun i => a i * b (n - i)%nat) (Qpow x n) n).
  apply partial_sum_ext_le. intros i Hi.
  assert (Hpow : Qpow x n == Qpow x i * Qpow x (n - i)%nat).
  { rewrite <- Qpow_add. replace (i + (n - i))%nat with n by lia. reflexivity. }
  rewrite Hpow. ring.
Qed.

(** Геометрическая оценка частичной суммы: Σ_{k≤N} xᵏ ≤ 1/(1−x). *)
Lemma geom_partial_bound : forall (x : Q) (N : nat), 0 <= x -> x < 1 ->
  partial_sum (fun k => Qpow x k) N <= / (1 - x).
Proof.
  intros x N Hx Hx1.
  assert (H1x : 0 < 1 - x) by lra.
  assert (Hr : (1 - x) * partial_sum (fun k => Qpow x k) N <= (1 - x) * / (1 - x)).
  { rewrite geometric_sum_identity, Qmult_inv_r by lra.
    assert (0 <= Qpow x (S N)) by (apply Qpow_nonneg; exact Hx). lra. }
  apply (Qmult_le_l _ _ (1 - x) H1x). exact Hr.
Qed.

(** Абсолютная оценка eval-членов: Σ_{k≤N} |aₖ|xᵏ ≤ B/(1−x) при |aₖ|≤B. *)
Lemma eval_abs_bound : forall (a : FPS) (x B : Q) (N : nat),
  0 <= x -> x < 1 -> (forall n, Qabs (a n) <= B) ->
  partial_sum (fun k => Qabs (eval_terms a x k)) N <= B * / (1 - x).
Proof.
  intros a x B N Hx Hx1 Hb.
  assert (HB0 : 0 <= B).
  { apply Qle_trans with (Qabs (a 0%nat)); [ apply Qabs_nonneg | apply Hb ]. }
  eapply Qle_trans.
  - apply (partial_sum_monotone (fun k => Qabs (eval_terms a x k)) (fun k => B * Qpow x k)).
    intro k. unfold eval_terms.
    rewrite Qabs_Qmult, (Qabs_pos (Qpow x k) (Qpow_nonneg x k Hx)).
    apply Qmult_le_compat_r; [ apply Hb | apply Qpow_nonneg; exact Hx ].
  - rewrite (partial_sum_scale B (fun k => Qpow x k) N).
    rewrite (Qmult_comm B (partial_sum (fun k => Qpow x k) N)), (Qmult_comm B (/ (1 - x))).
    apply Qmult_le_compat_r; [ apply geom_partial_bound; assumption | exact HB0 ].
Qed.

(** Сходимость свёртки eval-рядов (для гипотезы Hconv Мертенса): |conv â b̂|≤conv|â||b̂|,
    а conv|â||b̂| неотрицателен и ограничен ⟹ Cauchy (conv_cauchy). *)
Lemma conv_eval_cauchy : forall (a b : FPS) (x Ba Bb : Q),
  0 <= x -> x < 1 -> (forall n, Qabs (a n) <= Ba) -> (forall n, Qabs (b n) <= Bb) ->
  is_cauchy (partial_sum (conv (eval_terms a x) (eval_terms b x))).
Proof.
  intros a b x Ba Bb Hx Hx1 Ha Hb.
  apply (absolute_convergence
           (conv (eval_terms a x) (eval_terms b x))
           (conv (fun k => Qabs (eval_terms a x k)) (fun k => Qabs (eval_terms b x k)))).
  - intro n. unfold conv.
    eapply Qle_trans; [ apply partial_sum_abs_le | ].
    apply partial_sum_monotone. intro i. rewrite Qabs_Qmult. apply Qle_refl.
  - apply (conv_cauchy (fun k => Qabs (eval_terms a x k))
                       (fun k => Qabs (eval_terms b x k))
                       (Ba * / (1 - x)) (Bb * / (1 - x))).
    + intro n. apply Qabs_nonneg.
    + intro n. apply Qabs_nonneg.
    + intro M. apply eval_abs_bound; assumption.
    + intro M. apply eval_abs_bound; assumption.
Qed.

(** ★★ eval МУЛЬТИПЛИКАТИВЕН: eval(a·b) ~~ eval a · eval b  (через Мертенса).
    eval(a·b) = series_limit (eval_terms(a·b)) ~~ series_limit (conv â b̂) [eval_terms_mul]
    ~~ cauchy_mul (series_limit â)(series_limit b̂) [mertens_cauchy_product] = eval a · eval b. *)
Theorem eval_mul : forall (a b : FPS) (x Ba Bb : Q)
    (Hx : 0 <= x) (Hx1 : x < 1)
    (HBa : forall n, Qabs (a n) <= Ba) (HBb : forall n, Qabs (b n) <= Bb)
    (H : is_cauchy (partial_sum (eval_terms (fps_mul a b) x)))
    (Ha : is_cauchy (partial_sum (eval_terms a x)))
    (Hb : is_cauchy (partial_sum (eval_terms b x))),
  eval (fps_mul a b) x H ~~ cauchy_mul (eval a x Ha) (eval b x Hb).
Proof.
  intros a b x Ba Bb Hx Hx1 HBa HBb H Ha Hb.
  unfold eval.
  set (Hconv := conv_eval_cauchy a b x Ba Bb Hx Hx1 HBa HBb).
  eapply cauchy_equiv_trans.
  - apply (series_limit_wd (eval_terms (fps_mul a b) x)
             (conv (eval_terms a x) (eval_terms b x)) H Hconv).
    intro n. apply eval_terms_mul.
  - apply (mertens_cauchy_product (eval_terms a x) (eval_terms b x)
             (Ba * / (1 - x)) (Bb * / (1 - x))
             (fun N => eval_abs_bound a x Ba N Hx Hx1 HBa)
             (fun N => eval_abs_bound b x Bb N Hx Hx1 HBb)
             Ha Hb Hconv).
Qed.

(* ================================================================== *)
(*  ★ АНКЕРЫ exp/log: формальные базис-объекты ↔ существующие процессы   *)
(* ================================================================== *)

(** ★ eval exp_fps t ~~ exp_limit t: вычисленный формальный exp = рациональная
    экспонента-процесс.  Члены совпадают: (1/n!)·tⁿ = tⁿ·(1/n!) [Qmult_comm].
    Без ограничения на t — exp_limit сходится для всех t. *)
Lemma eval_exp : forall (t : Q) (H : is_cauchy (partial_sum (eval_terms exp_fps t))),
  eval exp_fps t H ~~ exp_limit t.
Proof.
  intros t H. unfold eval, exp_limit. apply series_limit_wd.
  intro n. unfold eval_terms, exp_fps, exp_term. ring.
Qed.

(** ★ eval log1m_fps x ~~ ln_proc x: вычисленный формальный −ln(1−x) = лог-процесс L(x).
    eval_terms log1m имеет ЛИШНИЙ нуль в индексе 0, далее — те же члены, что у ln_proc;
    поэтому partial_sum (eval_terms log1m x) (S n) == log_series_partial x n (СДВИГ на 1).
    Две Cauchy-последовательности-сдвиги эквивалентны (тот же предел). *)
Lemma eval_log1m : forall (x : Q) (Hx : 0 <= x) (Hx1 : x < 1)
    (H : is_cauchy (partial_sum (eval_terms log1m_fps x))),
  eval log1m_fps x H ~~ ln_proc x Hx Hx1.
Proof.
  intros x Hx Hx1 H.
  assert (Hshift : forall n,
    partial_sum (eval_terms log1m_fps x) (S n) == log_series_partial x n).
  { intro n. unfold log_series_partial. rewrite partial_sum_head.
    assert (H0 : eval_terms log1m_fps x 0%nat == 0).
    { unfold eval_terms. cbn [log1m_fps Qpow]. ring. }
    rewrite H0, Qplus_0_l.
    apply partial_sum_ext_le. intros k Hk.
    unfold eval_terms. cbn [log1m_fps log_series_term]. unfold Qdiv. ring. }
  intros eps Heps.
  destruct (ln_series_cauchy x Hx Hx1 eps Heps) as [N HN].
  exists (S N). intros n Hn. destruct n as [|m]; [ lia | ].
  change (cs_seq (eval log1m_fps x H) (S m))
    with (partial_sum (eval_terms log1m_fps x) (S m)).
  change (cs_seq (ln_proc x Hx Hx1) (S m)) with (log_series_partial x (S m)).
  rewrite (Hshift m).
  apply HN; lia.
Qed.

(** Аудит аксиом. *)
Print Assumptions eval_geom.
Print Assumptions eval_compose_exp_log1m_geom.
Print Assumptions eval_mul.
Print Assumptions eval_exp.
Print Assumptions eval_log1m.

(* ================================================================== *)
(*  СВОДКА: eval — первый анкер аналитического моста.  Формальное сердце *)
(*  E∘L (compose_exp_log1m_is_geom, 0-аксиомно) перенесено в число-      *)
(*  процесс: вычисленная композиция = 1/(1−x).  ДАЛЕЕ: eval как кольцевой *)
(*  гомоморфизм (через Мертенса) + закон композиции → exp_R(L(x))~~1/(1−x)*)
(*  → горизонт ln_mul.                                                    *)
(* ================================================================== *)
