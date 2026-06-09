(** * LnMulClosed.v — ★★★ ГОРИЗОНТ ln_mul ЗАМКНУТ: финальная сборка композиционной теоремы
    Elements: рациональное z∈[0,1); процессы-числа exp_R(ln_proc z), eval(exp∘log1m) z, 1/(1−z).
    Roles:    ФИНАЛЬНАЯ СБОРКА (boss) = роль-склейка двух процессов exp_R∘ln_proc и eval(exp∘log1m)
              через ДОМИНИРОВАННУЮ диагональную сходимость (Таннери).  На стадии n:
                cs_seq(exp_R(ln_proc z)) n = Σ_{k≤n}(sₙ)ᵏ/k!         (диагональ exp_R, exp_R_stage)
                cs_seq(eval(exp∘log1m) z) n = Σ_{k≤n}(1/k!)·Pₖₙ       (конечный Fubini, eval_compose_swap)
              их разность Dₙ = Σ_{k≤n}(1/k!)·((sₙ)ᵏ−Pₖₙ); |Dₙ| ≤ Σ_{k≤n} aₖₙ → 0 по Таннери, где
              aₖₙ=(1/k!)|(sₙ)ᵏ−Pₖₙ| мажорируется Mₖ=(1/k!)·2Bᵏ (B=1/(1−z), домината Pₖₙ≤σₙᵏ≤Bᵏ),
              а поточечно aₖₙ→0 (eval_pow: (sₙ)ᵏ=cs_seq(cauchy_pow(ln_proc z) k) n,
              Pₖₙ=cs_seq(eval(log1m^k) z) n, и cauchy_pow(ln_proc z) k ~~ eval(log1m^k) z).
    Rules:    Таннери (Tannery.v) + домината (LnMulComposition.v) + per-k через eval_pow/eval_log1m
              (FPSEval.v); затем boss + eval_compose_exp_log1m_geom ⟹ КЛЮЧ exp_R(ln_proc z)~~1/(1−z);
              ln_mul_from_key (LnMulReduction.v) ⟹ горизонт ln_mul_functional_equation.

    ============ E/R/R разбор ============
      Elements: на каждой стадии n — конечные Q-суммы Σ_{k≤n}; ни одного актуально-бесконечного объекта.
      Roles:    boss = роль-склейка «функция-как-процесс»↔«exp числа-процесса»; диагональ exp_R и
                конечный Fubini композиции встречаются в пределе по теореме Таннери (доминированная
                перестановка предела и суммы).  exp_R_ln_proc_is_geom = роль-КЛЮЧ; ln_mul_closed =
                роль-ЗАМЫКАНИЕ горизонта.
      Rules:    домината aₖₙ≤Mₖ (домината степеней + σₙ≤1/(1−z)); ΣM=2·exp(B) сходится; per-k aₖₙ→0
                (степень числа-процесса = процесс степеней коэффициентов в пределе); треугольник+Таннери.
    ДИАГНОСТИКА (P4): обе стороны (exp_R∘ln_proc и eval(exp∘log1m)) — потенциальные процессы, конечно-
      актуальные на стадии n; они НЕ равны поэлементно (диагональ vs конечный Fubini различаются при
      конечном n) — равны лишь как ПРЕДЕЛЫ.  Таннери = легальная (доминированная) перестановка, не
      завершённая бесконечность.  Унаследует classic (L3) — это честный анализ, НЕ 0-аксиомная алгебра.

    STATUS: 11 Qed, 0 Admitted, 0 НОВЫХ аксиом (наследует classic через анализ — exp_R/диагональ,
            absolute_convergence).  ★★★ ГОРИЗОНТ ЗАМКНУТ: ln_mul_closed : ln_mul_functional_equation,
            БЕЗ единственной оставшейся гипотезы — программа «функция-как-процесс» (H59) ЗАВЕРШЕНА.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import CauchyProduct.
From ToS Require Import PowerSeries.
From ToS Require Import ExpFunctionalEquation.
From ToS Require Import zeta.LogZeta.
From ToS Require Import Log2Process.
From ToS Require Import FormalPowerSeries.
From ToS Require Import FPSEval.
From ToS Require Import LnMulComposition.
From ToS Require Import Tannery.
From ToS Require Import ProcessExp.
From ToS Require Import Log2FunctionalEq.
From ToS Require Import LnMulReduction.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  Мелкие аналитические хелперы                                        *)
(* ================================================================== *)

(** Треугольное неравенство для разности: |a−b| ≤ |a|+|b|. *)
Lemma Qabs_sub_le : forall a b : Q, Qabs (a - b) <= Qabs a + Qabs b.
Proof.
  intros a b. assert (Hr : a - b == a + - b) by ring. rewrite Hr.
  eapply Qle_trans; [ apply Qabs_triangle | ].
  rewrite Qabs_opp. apply Qle_refl.
Qed.

(** n-я стадия степени числа-процесса = степень n-й стадии:
    cs_seq(cauchy_pow P k) n = (cs_seq P n)ᵏ.  (cauchy_mul поточечно ⟹ индукция.) *)
Lemma cs_seq_cauchy_pow : forall (P : CauchySeq) (k : nat) (n : nat),
  cs_seq (cauchy_pow P k) n == Qpow (cs_seq P n) k.
Proof.
  intros P k. induction k as [|k IH]; intro n.
  - cbn [cauchy_pow Qpow]. reflexivity.
  - change (cs_seq (cauchy_pow P (S k)) n)
      with (cs_seq P n * cs_seq (cauchy_pow P k) n).
    rewrite IH. cbn [Qpow]. reflexivity.
Qed.

(** Конгруэнтность степени числа-процесса по ~~ (индукция через cauchy_mul_compat). *)
Lemma cauchy_pow_compat : forall (A B : CauchySeq) (k : nat),
  A ~~ B -> cauchy_pow A k ~~ cauchy_pow B k.
Proof.
  intros A B k H. induction k as [|k IH].
  - cbn [cauchy_pow]. apply cauchy_equiv_refl.
  - cbn [cauchy_pow]. apply cauchy_mul_compat; [ exact H | exact IH ].
Qed.

(** Монотонность степени по основанию: 0≤a≤b ⟹ aᵏ≤bᵏ. *)
Lemma Qpow_le_compat : forall (a b : Q) (k : nat),
  0 <= a -> a <= b -> Qpow a k <= Qpow b k.
Proof.
  intros a b k Ha Hab. induction k as [|k IH].
  - cbn [Qpow]. apply Qle_refl.
  - cbn [Qpow].
    assert (Hb : 0 <= b) by (apply Qle_trans with a; [ exact Ha | exact Hab ]).
    assert (Hpa : 0 <= Qpow a k) by (apply Qpow_nonneg; exact Ha).
    apply Qle_trans with (b * Qpow a k).
    + apply Qmult_le_compat_r; [ exact Hab | exact Hpa ].
    + rewrite (Qmult_comm b (Qpow a k)), (Qmult_comm b (Qpow b k)).
      apply Qmult_le_compat_r; [ exact IH | exact Hb ].
Qed.

(** Коэффициенты log1m_fps ограничены 1 (как и в sigma_bound: 1/(S k) ≤ 1). *)
Lemma log1m_coeff_le1 : forall n, Qabs (log1m_fps n) <= 1.
Proof.
  intro n. rewrite (Qabs_pos (log1m_fps n) (log1m_nonneg n)).
  unfold log1m_fps. destruct n as [|k]; [ lra | ].
  assert (Hge1 : 1 <= inject_Z (Z.of_nat (S k)))
    by (change (1:Q) with (inject_Z 1); rewrite <- Zle_Qle; lia).
  assert (Hpos : 0 < inject_Z (Z.of_nat (S k))) by lra.
  apply (Qmult_le_l _ _ (inject_Z (Z.of_nat (S k))) Hpos).
  rewrite Qmult_inv_r by lra. lra.
Qed.

(** Абсолютная сходимость лог-ряда eval: Σ|log1m_n|zⁿ Cauchy (члены ≡ eval_terms, т.к. log1m≥0). *)
Lemma abs_conv_log1m : forall (z : Q), 0 <= z -> z < 1 -> abs_conv log1m_fps z.
Proof.
  intros z Hz Hz1. unfold abs_conv.
  apply (is_cauchy_ext (partial_sum (eval_terms log1m_fps z))).
  - intro n. apply partial_sum_ext_le. intros k Hk.
    unfold eval_terms. rewrite (Qabs_pos (log1m_fps k) (log1m_nonneg k)). reflexivity.
  - apply (eval_terms_cauchy_le1 log1m_fps z Hz Hz1 log1m_coeff_le1).
Qed.

(** Сдвиг: σ_{S n} = partial_sum(eval_terms log1m z)(S n) = log_series_partial z n = sₙ
    (лишний нуль eval_terms в индексе 0; копия Hshift из eval_log1m). *)
Lemma eval_log1m_shift : forall (z : Q) (n : nat),
  partial_sum (eval_terms log1m_fps z) (S n) == log_series_partial z n.
Proof.
  intros z n. unfold log_series_partial. rewrite partial_sum_head.
  assert (H0 : eval_terms log1m_fps z 0%nat == 0).
  { unfold eval_terms. cbn [log1m_fps Qpow]. ring. }
  rewrite H0, Qplus_0_l.
  apply partial_sum_ext_le. intros k Hk.
  unfold eval_terms. cbn [log1m_fps log_series_term]. unfold Qdiv. ring.
Qed.

(** Граница sₙ = cs_seq(ln_proc z) n: 0 ≤ sₙ ≤ 1/(1−z)  (через сдвиг + sigma_bound). *)
Lemma s_bound : forall (z : Q) (Hz : 0 <= z) (Hz1 : z < 1) (n : nat),
  0 <= cs_seq (ln_proc z Hz Hz1) n /\ cs_seq (ln_proc z Hz Hz1) n <= / (1 - z).
Proof.
  intros z Hz Hz1 n.
  assert (Hs : cs_seq (ln_proc z Hz Hz1) n == partial_sum (eval_terms log1m_fps z) (S n)).
  { rewrite (eval_log1m_shift z n). reflexivity. }
  split.
  - rewrite Hs. apply partial_sum_nonneg.
    exact (eval_terms_nonneg log1m_fps z Hz log1m_nonneg).
  - rewrite Hs. apply sigma_bound; [ exact Hz | exact Hz1 ].
Qed.

(* ================================================================== *)
(*  Данные для теоремы Таннери (двойная таблица aₖₙ и мажоранта Mₖ)     *)
(* ================================================================== *)

(** aₖₙ = (1/k!)·|(sₙ)ᵏ − Pₖₙ| — расхождение диагонали exp_R и Fubini композиции. *)
Definition lnmul_aT (z : Q) (Hz : 0 <= z) (Hz1 : z < 1) (k n : nat) : Q :=
  / Qfact k * Qabs (Qpow (cs_seq (ln_proc z Hz Hz1) n) k
                    - partial_sum (eval_terms (fps_pow log1m_fps k) z) n).

(** Mₖ = (1/k!)·2Bᵏ, B = 1/(1−z) — суммируемая мажоранта (ΣM = 2·exp(B)). *)
Definition lnmul_MT (z : Q) (k : nat) : Q := / Qfact k * (2 * Qpow (/ (1 - z)) k).

(* ================================================================== *)
(*  ★★★ BOSS: exp_R(ln_proc z) ~~ eval(exp∘log1m) z  (доминир. диагональ)*)
(* ================================================================== *)

Lemma boss : forall (z : Q) (Hz : 0 <= z) (Hz1 : z < 1)
    (Hc : is_cauchy (partial_sum (eval_terms (fps_compose exp_fps log1m_fps) z))),
  exp_R (ln_proc z Hz Hz1) ~~ eval (fps_compose exp_fps log1m_fps) z Hc.
Proof.
  intros z Hz Hz1 Hc.
  (* свидетели сходимости log1m и его степеней *)
  assert (HAlog : abs_conv log1m_fps z) by (apply abs_conv_log1m; [ exact Hz | exact Hz1 ]).
  assert (Hg : is_cauchy (partial_sum (eval_terms log1m_fps z)))
    by (apply abs_conv_eval_cauchy; [ exact Hz | exact HAlog ]).
  assert (Hk : forall k, is_cauchy (partial_sum (eval_terms (fps_pow log1m_fps k) z))).
  { intro k. apply abs_conv_eval_cauchy;
      [ exact Hz | apply abs_conv_pow; [ exact Hz | exact Hz1 | exact HAlog ] ]. }
  (* Гипотеза Таннери 1: aₖₙ ≥ 0 *)
  assert (Hnn : forall k n, 0 <= lnmul_aT z Hz Hz1 k n).
  { intros k n. unfold lnmul_aT. apply Qmult_le_0_compat.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. apply Qfact_pos.
    - apply Qabs_nonneg. }
  (* Гипотеза Таннери 2: aₖₙ ≤ Mₖ  (домината степеней + sₙ,σₙ ≤ B) *)
  assert (Hdom : forall k n, lnmul_aT z Hz Hz1 k n <= lnmul_MT z k).
  { intros k n. unfold lnmul_aT, lnmul_MT.
    assert (Hinv_pos : 0 < / Qfact k) by (apply Qinv_lt_0_compat; apply Qfact_pos).
    apply (Qmult_le_l _ _ (/ Qfact k) Hinv_pos).
    destruct (s_bound z Hz Hz1 n) as [Hsn0 HsnB].
    assert (Hpk_nn : 0 <= partial_sum (eval_terms (fps_pow log1m_fps k) z) n)
      by (apply partial_sum_nonneg;
          exact (eval_terms_nonneg (fps_pow log1m_fps k) z Hz
                  (fps_pow_nonneg log1m_fps log1m_nonneg k))).
    assert (Hsig_nn : 0 <= partial_sum (eval_terms log1m_fps z) n)
      by (apply partial_sum_nonneg; exact (eval_terms_nonneg log1m_fps z Hz log1m_nonneg)).
    assert (Hp_le : Qpow (cs_seq (ln_proc z Hz Hz1) n) k <= Qpow (/ (1 - z)) k)
      by (apply Qpow_le_compat; [ exact Hsn0 | exact HsnB ]).
    assert (Hq_le : partial_sum (eval_terms (fps_pow log1m_fps k) z) n <= Qpow (/ (1 - z)) k).
    { apply Qle_trans with (Qpow (partial_sum (eval_terms log1m_fps z) n) k).
      - exact (P_le_sigma_pow log1m_fps log1m_nonneg z Hz k n).
      - apply Qpow_le_compat; [ exact Hsig_nn | apply sigma_bound; [ exact Hz | exact Hz1 ] ]. }
    eapply Qle_trans; [ apply Qabs_sub_le | ].
    rewrite (Qabs_pos (Qpow (cs_seq (ln_proc z Hz Hz1) n) k)) by (apply Qpow_nonneg; exact Hsn0).
    rewrite (Qabs_pos (partial_sum (eval_terms (fps_pow log1m_fps k) z) n)) by exact Hpk_nn.
    lra. }
  (* Гипотеза Таннери 3: ΣM Cauchy  (= 2·exp(B)) *)
  assert (HM : is_cauchy (partial_sum (lnmul_MT z))).
  { pose (W := cauchy_mul (cauchy_const 2) (exp_limit (/ (1 - z)))).
    apply (is_cauchy_ext (cs_seq W) (partial_sum (lnmul_MT z))).
    - intro n. change (cs_seq W n) with (2 * partial_sum (exp_term (/ (1 - z))) n).
      rewrite <- (partial_sum_scale 2 (exp_term (/ (1 - z))) n).
      apply partial_sum_ext_le. intros k _. unfold lnmul_MT, exp_term. ring.
    - apply cs_cauchy. }
  (* Гипотеза Таннери 4: поточечно aₖₙ → 0  (степень = процесс степеней, eval_pow) *)
  assert (Hconv : forall k eps0, 0 < eps0 ->
            exists Nk, forall n, (Nk <= n)%nat -> lnmul_aT z Hz Hz1 k n < eps0).
  { intros k eps0 Heps0.
    assert (HAB : cauchy_pow (ln_proc z Hz Hz1) k ~~ eval (fps_pow log1m_fps k) z (Hk k)).
    { eapply cauchy_equiv_trans.
      - apply cauchy_pow_compat. apply cauchy_equiv_sym. exact (eval_log1m z Hz Hz1 Hg).
      - apply cauchy_equiv_sym. exact (eval_pow log1m_fps z Hz Hz1 HAlog Hg k (Hk k)). }
    assert (Hfk_pos : 0 < eps0 * Qfact k)
      by (apply Qmult_lt_0_compat; [ exact Heps0 | apply Qfact_pos ]).
    destruct (HAB (eps0 * Qfact k) Hfk_pos) as [Nk HNk].
    exists Nk. intros n Hn. unfold lnmul_aT.
    assert (Heqd : Qpow (cs_seq (ln_proc z Hz Hz1) n) k
                   - partial_sum (eval_terms (fps_pow log1m_fps k) z) n
                   == cs_seq (cauchy_pow (ln_proc z Hz Hz1) k) n
                      - cs_seq (eval (fps_pow log1m_fps k) z (Hk k)) n).
    { rewrite (cs_seq_cauchy_pow (ln_proc z Hz Hz1) k n). reflexivity. }
    rewrite Heqd.
    assert (Hsimp : eps0 == / Qfact k * (eps0 * Qfact k)) by (field; apply Qfact_nonzero).
    rewrite Hsimp.
    apply Qmult_lt_l; [ apply Qinv_lt_0_compat; apply Qfact_pos | apply HNk; exact Hn ]. }
  (* Сборка ~~ через Tannery *)
  intros eps Heps.
  destruct (tannery (lnmul_aT z Hz Hz1) (lnmul_MT z) Hnn Hdom HM Hconv eps Heps) as [N HN].
  exists N. intros n Hn.
  (* тождество стадии: Dₙ = Σ_{k≤n}(1/k!)·((sₙ)ᵏ − Pₖₙ) *)
  assert (HD : cs_seq (exp_R (ln_proc z Hz Hz1)) n
               - cs_seq (eval (fps_compose exp_fps log1m_fps) z Hc) n
               == partial_sum (fun k => / Qfact k *
                    (Qpow (cs_seq (ln_proc z Hz Hz1) n) k
                     - partial_sum (eval_terms (fps_pow log1m_fps k) z) n)) n).
  { assert (HL : cs_seq (exp_R (ln_proc z Hz Hz1)) n
                 == partial_sum (exp_term (cs_seq (ln_proc z Hz Hz1) n)) n)
      by apply exp_R_stage.
    assert (HR : cs_seq (eval (fps_compose exp_fps log1m_fps) z Hc) n
                 == partial_sum (fun k => exp_fps k *
                      partial_sum (eval_terms (fps_pow log1m_fps k) z) n) n).
    { change (cs_seq (eval (fps_compose exp_fps log1m_fps) z Hc) n)
        with (partial_sum (eval_terms (fps_compose exp_fps log1m_fps) z) n).
      apply eval_compose_swap. reflexivity. }
    rewrite HL, HR.
    rewrite <- (partial_sum_minus (exp_term (cs_seq (ln_proc z Hz Hz1) n))
                  (fun k => exp_fps k * partial_sum (eval_terms (fps_pow log1m_fps k) z) n) n).
    apply partial_sum_ext_le. intros k _. unfold exp_term, exp_fps. ring. }
  rewrite HD.
  eapply Qle_lt_trans; [ apply partial_sum_abs_le | ].
  apply Qle_lt_trans with (partial_sum (fun k => lnmul_aT z Hz Hz1 k n) n).
  - apply partial_sum_monotone. intro k. cbv beta. unfold lnmul_aT.
    rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ Qfact k)) by (apply Qlt_le_weak; apply Qinv_lt_0_compat; apply Qfact_pos).
    apply Qle_refl.
  - apply HN. exact Hn.
Qed.

(* ================================================================== *)
(*  ★★ КЛЮЧЕВОЙ ФАКТ и ★★★ ЗАМЫКАНИЕ ГОРИЗОНТА                          *)
(* ================================================================== *)

(** ★★ КЛЮЧ: exp_R(ln_proc z) ~~ 1/(1−z).  boss (= eval композиции) + перенос
    формального сердца E∘L (eval_compose_exp_log1m_geom = геометрическая). *)
Theorem exp_R_ln_proc_is_geom : forall (z : Q) (Hz : 0 <= z) (Hz1 : z < 1),
  exp_R (ln_proc z Hz Hz1) ~~ geometric_limit z Hz Hz1.
Proof.
  intros z Hz Hz1.
  pose (Hc := eval_terms_cauchy_le1 (fps_compose exp_fps log1m_fps) z Hz Hz1 compose_coeff_le1).
  eapply cauchy_equiv_trans.
  - exact (boss z Hz Hz1 Hc).
  - exact (eval_compose_exp_log1m_geom z Hz Hz1 Hc).
Qed.

(** ★★★ ГОРИЗОНТ ЗАМКНУТ: L(x)+L(y) ~~ L(x⊕y).  ln_mul_from_key (эндшпиль) применённый
    к доказанному ключу — БЕЗ единственной оставшейся гипотезы.  Программа H59 завершена. *)
Theorem ln_mul_closed : ln_mul_functional_equation.
Proof. apply ln_mul_from_key. exact exp_R_ln_proc_is_geom.
Qed.

(** Аудит аксиом. *)
Print Assumptions boss.
Print Assumptions exp_R_ln_proc_is_geom.
Print Assumptions ln_mul_closed.

(* ================================================================== *)
(*  СВОДКА: ГОРИЗОНТ ln_mul ЗАМКНУТ.  boss склеивает диагональ exp_R и    *)
(*  конечный Fubini композиции по доминированной сходимости Таннери       *)
(*  (домината Pₖₙ≤σₙᵏ≤Bᵏ + per-k через eval_pow); КЛЮЧ exp_R(L(z))~~1/(1−z)*)
(*  получен; ln_mul_from_key замыкает L(x)+L(y)~~L(x⊕y).  H59 завершена.   *)
(* ================================================================== *)
