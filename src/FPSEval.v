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

    STATUS: 33 Qed, 0 Admitted, 0 axioms (convergence-леммы наследуют classic; АЛГЕБРАИЧЕСКИЕ hom-леммы 0-аксиомны).
            ГОТОВО: eval + сходимость; eval_congr; ★ eval_geom; ★★ eval_compose_exp_log1m_geom (формальное сердце
            E∘L, вычисленное = 1/(1−x)); ★★ eval_mul; ★ АНКЕРЫ eval_exp (↔exp_limit), eval_log1m (↔ln_proc);
            ★ ℚ-АЛГЕБРА-ГОМОМОРФИЗМ eval_add/zero/one/neg/sub/scale (алгебра 0-аксиомна, eval_add=Closed);
            ★★ eval_mul_abs (eval МУЛЬТИПЛИКАТИВЕН под АБСОЛЮТНОЙ сходимостью — ИТЕРИРУЕМАЯ версия, границы Ma/Mb
            извлечены из abs_conv_bounded [монотон.+Cauchy⟹огранич.]); ★★ POWER LAW eval_pow: eval(gᵏ)~~(eval g)ᵏ
            (cauchy_pow = итерир. cauchy_mul; индукция по k через eval_mul_abs + abs_conv_pow [замкнутость абс-
            сходимости относительно умножения — ИМЕННО это разблокировало power law, коэф. gᵏ растут].
            ОСТАЁТСЯ (БОСС): закон композиции eval(f∘g) x ~~ Σ fₖ(eval g x)ᵏ (Fubini двойного ряда: Σₙ Σ_{k≤n}
            fₖ(gᵏ)ₙxⁿ = Σₖ fₖ Σₙ(gᵏ)ₙxⁿ, внутр. конечна по занулению) → exp_R(L(x))~~1/(1−x) → ln_mul.
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

(* ================================================================== *)
(*  ★ eval — ℚ-АЛГЕБРА-ГОМОМОРФИЗМ: сохраняет +, 0, 1, −, скаляр         *)
(*    (мультипликативность eval_mul уже доказана выше).                  *)
(* ================================================================== *)

(** Поточечное равенство стадий ⟹ ~~ (общий хелпер). *)
Lemma cauchy_equiv_from_cs_eq : forall (P R : CauchySeq),
  (forall n, cs_seq P n == cs_seq R n) -> P ~~ R.
Proof.
  intros P R HPR eps Heps. exists 0%nat. intros n _.
  rewrite (HPR n).
  assert (Hz : cs_seq R n - cs_seq R n == 0) by ring.
  rewrite Hz. change (Qabs 0) with (0:Q). exact Heps.
Qed.

(** Частичная сумma отрицаний. *)
Lemma partial_sum_neg : forall (f : nat -> Q) (n : nat),
  partial_sum (fun i => - f i) n == - partial_sum f n.
Proof.
  intros f n. induction n as [|n IH].
  - reflexivity.
  - rewrite (partial_sum_S (fun i => - f i) n), (partial_sum_S f n), IH.
    cbv beta. ring.
Qed.

(** ★ eval аддитивен: eval(a+b) ~~ eval a + eval b. *)
Lemma eval_add : forall (a b : FPS) (x : Q)
    (H : is_cauchy (partial_sum (eval_terms (fps_add a b) x)))
    (Ha : is_cauchy (partial_sum (eval_terms a x)))
    (Hb : is_cauchy (partial_sum (eval_terms b x))),
  eval (fps_add a b) x H ~~ cauchy_add (eval a x Ha) (eval b x Hb).
Proof.
  intros a b x H Ha Hb. apply cauchy_equiv_from_cs_eq. intro n.
  change (cs_seq (cauchy_add (eval a x Ha) (eval b x Hb)) n)
    with (partial_sum (eval_terms a x) n + partial_sum (eval_terms b x) n).
  change (cs_seq (eval (fps_add a b) x H) n)
    with (partial_sum (eval_terms (fps_add a b) x) n).
  rewrite <- partial_sum_plus.
  apply partial_sum_ext_le. intros k Hk. unfold eval_terms, fps_add. ring.
Qed.

(** ★ eval(0) ~~ 0. *)
Lemma eval_zero : forall (x : Q)
    (H : is_cauchy (partial_sum (eval_terms fps_zero x))),
  eval fps_zero x H ~~ cauchy_const 0.
Proof.
  intros x H. apply cauchy_equiv_from_cs_eq. intro n.
  change (cs_seq (cauchy_const 0) n) with (0:Q).
  change (cs_seq (eval fps_zero x H) n) with (partial_sum (eval_terms fps_zero x) n).
  rewrite (partial_sum_ext_le (eval_terms fps_zero x) (fun _ => 0) n).
  - apply partial_sum_zero.
  - intros k Hk. unfold eval_terms, fps_zero. ring.
Qed.

(** ★ eval(1) ~~ 1. *)
Lemma eval_one : forall (x : Q)
    (H : is_cauchy (partial_sum (eval_terms fps_one x))),
  eval fps_one x H ~~ cauchy_one.
Proof.
  intros x H. apply cauchy_equiv_from_cs_eq. intro n.
  change (cs_seq cauchy_one n) with (1:Q).
  change (cs_seq (eval fps_one x H) n) with (partial_sum (eval_terms fps_one x) n).
  induction n as [|m IH].
  - cbn [partial_sum]. unfold eval_terms. cbn [fps_one Qpow]. ring.
  - rewrite partial_sum_S.
    assert (Hz : eval_terms fps_one x (S m) == 0)
      by (unfold eval_terms; cbn [fps_one]; ring).
    rewrite Hz, IH. ring.
Qed.

(** ★ eval(−a) ~~ − eval a. *)
Lemma eval_neg : forall (a : FPS) (x : Q)
    (H : is_cauchy (partial_sum (eval_terms (fps_neg a) x)))
    (Ha : is_cauchy (partial_sum (eval_terms a x))),
  eval (fps_neg a) x H ~~ cauchy_neg (eval a x Ha).
Proof.
  intros a x H Ha. apply cauchy_equiv_from_cs_eq. intro n.
  change (cs_seq (cauchy_neg (eval a x Ha)) n)
    with (- partial_sum (eval_terms a x) n).
  change (cs_seq (eval (fps_neg a) x H) n)
    with (partial_sum (eval_terms (fps_neg a) x) n).
  rewrite <- partial_sum_neg.
  apply partial_sum_ext_le. intros k Hk. unfold eval_terms, fps_neg. ring.
Qed.

(** ★ eval(a−b) ~~ eval a − eval b. *)
Lemma eval_sub : forall (a b : FPS) (x : Q)
    (H : is_cauchy (partial_sum (eval_terms (fps_sub a b) x)))
    (Ha : is_cauchy (partial_sum (eval_terms a x)))
    (Hb : is_cauchy (partial_sum (eval_terms b x))),
  eval (fps_sub a b) x H ~~ cauchy_sub (eval a x Ha) (eval b x Hb).
Proof.
  intros a b x H Ha Hb. apply cauchy_equiv_from_cs_eq. intro n.
  change (cs_seq (cauchy_sub (eval a x Ha) (eval b x Hb)) n)
    with (partial_sum (eval_terms a x) n + - partial_sum (eval_terms b x) n).
  change (cs_seq (eval (fps_sub a b) x H) n)
    with (partial_sum (eval_terms (fps_sub a b) x) n).
  assert (Hps : partial_sum (eval_terms (fps_sub a b) x) n
                == partial_sum (eval_terms a x) n - partial_sum (eval_terms b x) n).
  { rewrite <- partial_sum_minus. apply partial_sum_ext_le.
    intros k Hk. unfold eval_terms, fps_sub. ring. }
  rewrite Hps. ring.
Qed.

(** ★ eval(c·a) ~~ c · eval a (умножение на скаляр-константу). *)
Lemma eval_scale : forall (c : Q) (a : FPS) (x : Q)
    (H : is_cauchy (partial_sum (eval_terms (fps_scale c a) x)))
    (Ha : is_cauchy (partial_sum (eval_terms a x))),
  eval (fps_scale c a) x H ~~ cauchy_mul (cauchy_const c) (eval a x Ha).
Proof.
  intros c a x H Ha. apply cauchy_equiv_from_cs_eq. intro n.
  change (cs_seq (cauchy_mul (cauchy_const c) (eval a x Ha)) n)
    with (c * partial_sum (eval_terms a x) n).
  change (cs_seq (eval (fps_scale c a) x H) n)
    with (partial_sum (eval_terms (fps_scale c a) x) n).
  rewrite <- (partial_sum_scale c (eval_terms a x) n).
  apply partial_sum_ext_le. intros k Hk. unfold eval_terms, fps_scale. ring.
Qed.

(* ================================================================== *)
(*  ★★ eval_mul под АБСОЛЮТНОЙ СХОДИМОСТЬЮ (итерируемая версия)          *)
(*    — разблокирует power law eval(gᵏ)=(eval g)ᵏ (коэф. gᵏ растут,      *)
(*    равномерной границы нет, но Σ|gᵏ_n|xⁿ сходится).                   *)
(* ================================================================== *)

(** Абсолютная сходимость eval-ряда: Σ |aₙ|·xⁿ сходится (Cauchy). *)
Definition abs_conv (a : FPS) (x : Q) : Prop :=
  is_cauchy (partial_sum (fun n => Qabs (a n) * Qpow x n)).

(** |aₙxⁿ| = |aₙ|·xⁿ (для x≥0). *)
Lemma abs_eval_terms : forall (a : FPS) (x : Q) (k : nat), 0 <= x ->
  Qabs (eval_terms a x k) == Qabs (a k) * Qpow x k.
Proof.
  intros a x k Hx. unfold eval_terms. rewrite Qabs_Qmult.
  rewrite (Qabs_pos (Qpow x k) (Qpow_nonneg x k Hx)). reflexivity.
Qed.

(** Абсолютная сходимость ⟹ обычная сходимость eval (мажорация собой). *)
Lemma abs_conv_eval_cauchy : forall (a : FPS) (x : Q), 0 <= x ->
  abs_conv a x -> is_cauchy (partial_sum (eval_terms a x)).
Proof.
  intros a x Hx Hac.
  apply (absolute_convergence (eval_terms a x) (fun n => Qabs (a n) * Qpow x n)).
  - intro n. rewrite (abs_eval_terms a x n Hx). apply Qle_refl.
  - exact Hac.
Qed.

(** Монотонные абс-частичные суммы Cauchy ⟹ ограничены сверху (извлекаем Ma). *)
Lemma abs_conv_bounded : forall (a : FPS) (x : Q), 0 <= x -> abs_conv a x ->
  exists B, forall N, partial_sum (fun n => Qabs (a n) * Qpow x n) N <= B.
Proof.
  intros a x Hx Hac.
  destruct (Hac 1 ltac:(lra)) as [N HN].
  exists (partial_sum (fun n => Qabs (a n) * Qpow x n) N + 1).
  intro M.
  assert (Hnn : forall k, 0 <= Qabs (a k) * Qpow x k)
    by (intro k; apply Qmult_le_0_compat; [ apply Qabs_nonneg | apply Qpow_nonneg; exact Hx ]).
  assert (N <= M \/ M <= N)%nat as [Hle | Hle] by lia.
  - assert (Hc := HN M N Hle (le_n N)). apply Qabs_Qlt_condition in Hc. lra.
  - assert (Hmono : partial_sum (fun n => Qabs (a n) * Qpow x n) M
                    <= partial_sum (fun n => Qabs (a n) * Qpow x n) N)
      by (apply partial_sum_le_upper; [ exact Hnn | exact Hle ]). lra.
Qed.

(** ★★ eval МУЛЬТИПЛИКАТИВЕН под абсолютной сходимостью (ИТЕРИРУЕМАЯ версия).
    Гипотезы — abs_conv a / abs_conv b (а НЕ равномерные границы |aₙ|≤B), поэтому
    применима к gᵏ.  Границы Ma/Mb для Мертенса извлечены из abs_conv_bounded. *)
Theorem eval_mul_abs : forall (a b : FPS) (x : Q)
    (Hx : 0 <= x) (Hx1 : x < 1)
    (HAa : abs_conv a x) (HAb : abs_conv b x)
    (H : is_cauchy (partial_sum (eval_terms (fps_mul a b) x)))
    (Ha : is_cauchy (partial_sum (eval_terms a x)))
    (Hb : is_cauchy (partial_sum (eval_terms b x))),
  eval (fps_mul a b) x H ~~ cauchy_mul (eval a x Ha) (eval b x Hb).
Proof.
  intros a b x Hx Hx1 HAa HAb H Ha Hb.
  destruct (abs_conv_bounded a x Hx HAa) as [Ma HMa].
  destruct (abs_conv_bounded b x Hx HAb) as [Mb HMb].
  assert (HMa' : forall N, partial_sum (fun k => Qabs (eval_terms a x k)) N <= Ma).
  { intro N. rewrite (partial_sum_ext_le (fun k => Qabs (eval_terms a x k))
                       (fun n => Qabs (a n) * Qpow x n) N).
    - apply HMa.
    - intros k Hk. apply abs_eval_terms; exact Hx. }
  assert (HMb' : forall N, partial_sum (fun k => Qabs (eval_terms b x k)) N <= Mb).
  { intro N. rewrite (partial_sum_ext_le (fun k => Qabs (eval_terms b x k))
                       (fun n => Qabs (b n) * Qpow x n) N).
    - apply HMb.
    - intros k Hk. apply abs_eval_terms; exact Hx. }
  assert (Hconv : is_cauchy (partial_sum (conv (eval_terms a x) (eval_terms b x)))).
  { apply (absolute_convergence
             (conv (eval_terms a x) (eval_terms b x))
             (conv (fun k => Qabs (eval_terms a x k)) (fun k => Qabs (eval_terms b x k)))).
    - intro n. unfold conv. eapply Qle_trans; [ apply partial_sum_abs_le | ].
      apply partial_sum_monotone. intro i. rewrite Qabs_Qmult. apply Qle_refl.
    - apply (conv_cauchy (fun k => Qabs (eval_terms a x k))
                         (fun k => Qabs (eval_terms b x k)) Ma Mb).
      + intro n. apply Qabs_nonneg.
      + intro n. apply Qabs_nonneg.
      + exact HMa'.
      + exact HMb'. }
  unfold eval.
  eapply cauchy_equiv_trans.
  - apply (series_limit_wd (eval_terms (fps_mul a b) x)
             (conv (eval_terms a x) (eval_terms b x)) H Hconv).
    intro n. apply eval_terms_mul.
  - apply (mertens_cauchy_product (eval_terms a x) (eval_terms b x) Ma Mb
             HMa' HMb' Ha Hb Hconv).
Qed.

(* ================================================================== *)
(*  ★★ POWER LAW: eval(gᵏ) ~~ (eval g)ᵏ  (через абс-сходимость + индукцию)*)
(* ================================================================== *)

(** k-я степень числа-процесса (итерированное cauchy_mul). *)
Fixpoint cauchy_pow (P : CauchySeq) (k : nat) : CauchySeq :=
  match k with
  | O => cauchy_one
  | S k' => cauchy_mul P (cauchy_pow P k')
  end.

(** Абсолютная сходимость единицы (члены = (n=0?1:0), сумма ≡ 1). *)
Lemma abs_conv_one : forall x, 0 <= x -> abs_conv fps_one x.
Proof.
  intros x Hx. unfold abs_conv.
  apply (is_cauchy_ext (fun _ => 1)).
  - intro n. induction n as [|m IH].
    + cbn [partial_sum fps_one Qpow]. rewrite (Qabs_pos 1) by lra. ring.
    + rewrite partial_sum_S.
      assert (Hz : Qabs (fps_one (S m)) * Qpow x (S m) == 0)
        by (cbn [fps_one]; change (Qabs 0) with (0:Q); ring).
      rewrite <- IH, Hz. ring.
  - apply cauchy_const_is_cauchy.
Qed.

(** ★ Замкнутость абс-сходимости относительно умножения: abs_conv a, abs_conv b ⟹
    abs_conv (a·b).  |（a·b)ₙ|xⁿ ≤ (conv|a||b|)ₙxⁿ = conv(|a|x^•)(|b|x^•)ₙ [eval_terms_mul
    для |a|,|b|], а это сходится по conv_cauchy.  ИМЕННО это делает power law итерируемым. *)
Lemma abs_conv_mul : forall (a b : FPS) (x : Q), 0 <= x -> x < 1 ->
  abs_conv a x -> abs_conv b x -> abs_conv (fps_mul a b) x.
Proof.
  intros a b x Hx Hx1 HAa HAb.
  destruct (abs_conv_bounded a x Hx HAa) as [Ma HMa].
  destruct (abs_conv_bounded b x Hx HAb) as [Mb HMb].
  unfold abs_conv.
  apply (absolute_convergence
           (fun n => Qabs (fps_mul a b n) * Qpow x n)
           (conv (fun i => Qabs (a i) * Qpow x i) (fun j => Qabs (b j) * Qpow x j))).
  - intro n.
    rewrite (Qabs_pos (Qabs (fps_mul a b n) * Qpow x n))
      by (apply Qmult_le_0_compat; [ apply Qabs_nonneg | apply Qpow_nonneg; exact Hx ]).
    assert (Hid : conv (fun i => Qabs (a i) * Qpow x i) (fun j => Qabs (b j) * Qpow x j) n
                  == conv (fun i => Qabs (a i)) (fun j => Qabs (b j)) n * Qpow x n).
    { symmetry. apply (eval_terms_mul (fun i => Qabs (a i)) (fun j => Qabs (b j)) x n). }
    rewrite Hid.
    apply Qmult_le_compat_r; [ | apply Qpow_nonneg; exact Hx ].
    unfold fps_mul, conv.
    eapply Qle_trans; [ apply partial_sum_abs_le | ].
    apply partial_sum_monotone. intro i. rewrite Qabs_Qmult. apply Qle_refl.
  - apply (conv_cauchy (fun i => Qabs (a i) * Qpow x i) (fun j => Qabs (b j) * Qpow x j) Ma Mb).
    + intro n. apply Qmult_le_0_compat; [ apply Qabs_nonneg | apply Qpow_nonneg; exact Hx ].
    + intro n. apply Qmult_le_0_compat; [ apply Qabs_nonneg | apply Qpow_nonneg; exact Hx ].
    + exact HMa.
    + exact HMb.
Qed.

(** ★ Абсолютная сходимость степени gᵏ (индукция: g⁰=1 база, g·gᵏ шаг). *)
Lemma abs_conv_pow : forall (g : FPS) (x : Q), 0 <= x -> x < 1 ->
  abs_conv g x -> forall k, abs_conv (fps_pow g k) x.
Proof.
  intros g x Hx Hx1 HAg k. induction k as [|k IH].
  - apply abs_conv_one; exact Hx.
  - change (fps_pow g (S k)) with (fps_mul g (fps_pow g k)).
    apply abs_conv_mul; [ exact Hx | exact Hx1 | exact HAg | exact IH ].
Qed.

(** ★★ POWER LAW: eval(gᵏ) ~~ (eval g)ᵏ.  Индукция по k: g⁰=1 ⟹ eval_one;
    g·gᵏ ⟹ eval_mul_abs (с abs_conv g и abs_conv_pow) + IH.  Свидетели сходимости
    извлекаются из абсолютной (abs_conv_eval_cauchy). *)
Lemma eval_pow : forall (g : FPS) (x : Q) (Hx : 0 <= x) (Hx1 : x < 1)
    (HAg : abs_conv g x) (Hg : is_cauchy (partial_sum (eval_terms g x)))
    (k : nat) (Hk : is_cauchy (partial_sum (eval_terms (fps_pow g k) x))),
  eval (fps_pow g k) x Hk ~~ cauchy_pow (eval g x Hg) k.
Proof.
  intros g x Hx Hx1 HAg Hg k. induction k as [|k IH]; intro Hk.
  - apply eval_one.
  - assert (HAk : abs_conv (fps_pow g k) x) by (apply abs_conv_pow; assumption).
    assert (Hk' : is_cauchy (partial_sum (eval_terms (fps_pow g k) x)))
      by (apply abs_conv_eval_cauchy; assumption).
    eapply cauchy_equiv_trans.
    + apply (eval_mul_abs g (fps_pow g k) x Hx Hx1 HAg HAk Hk Hg Hk').
    + apply cauchy_mul_compat; [ apply cauchy_equiv_refl | apply (IH Hk') ].
Qed.

(** Аудит аксиом. *)
Print Assumptions eval_geom.
Print Assumptions eval_compose_exp_log1m_geom.
Print Assumptions eval_mul.
Print Assumptions eval_mul_abs.
Print Assumptions eval_pow.
Print Assumptions eval_exp.
Print Assumptions eval_log1m.
Print Assumptions eval_add.

(* ================================================================== *)
(*  СВОДКА: eval — аналитический МОСТ FPS → число-процесс.  Готово:      *)
(*  eval + сходимость; eval_geom + ВЫЧИСЛЕННОЕ формальное сердце E∘L     *)
(*  (=1/(1−x)); eval = ℚ-алгебра-гомоморфизм (+,0,1,−,·,скаляр; алгебра  *)
(*  0-аксиомна); анкеры exp/log; eval_mul_abs (итерируемая мультипл.) +  *)
(*  POWER LAW eval(gᵏ)~~(eval g)ᵏ (через абс-сходимость).  ДАЛЕЕ (босс): *)
(*  закон композиции eval(f∘g)x ~~ Σ fₖ(eval g x)ᵏ (двойной Fubini) →    *)
(*  exp_R(L(x))~~1/(1−x) → горизонт ln_mul.                              *)
(* ================================================================== *)
