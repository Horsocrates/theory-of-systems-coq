(** * Log2Process.v — log₂ в битах как ПРОЦЕСС (Cauchy над Q), а не стена

    Переобрамление DyadicBits.v.  Там иррациональность log₂(нечёт) сформулирована
    ОТРИЦАТЕЛЬНО — `¬∃ a,b. 2^a = n^b` (стена, несуществование).  Но в ToS
    иррациональность — НЕ стена, а ПРОЦЕСС (role-limit как актуальный Cauchy-объект,
    ср. ContinuumLimitRoleLimit.sqrt2_never_reached, EulerProcessRoleLimit).  Этот файл
    даёт сам ОБЪЕКТ — log₂ как RealProcess (Cauchy над Q) — а иррациональность DyadicBits
    становится его честной role-limit-ДИАГНОСТИКОЙ, а не отдельной теоремой-стеной.

    Опора: L(x) = Σ_{m≥1} xᵐ/m = -ln(1-x), сходится для |x|<1.  Отсюда
    ln 2 = -ln(1/2) = L(1/2), ln 3 = -ln(1/3) = L(2/3).  Серия и доминирование
    (log_series_term ≤ Qpow) УЖЕ в zeta/LogZeta.v; Cauchy-машина (comparison_test,
    series_limit) — в SeriesConvergence.v; поле процессов (cauchy_mul/inv) — RealField.v.
    Паттерн реплея — exp_series_cauchy (PowerSeries.v).

    ============ E/R/R разбор ============
      Elements (L1+P4): частичные суммы log_series_partial x M = Σ_{m=1}^{M} xᵐ/m —
        каждая стадия M точна над Q; степени 2ᵏ; диадические аргументы и их целые log.
      Roles (L4): ln-процесс = роль-величина (-ln(1-x) как Cauchy-объект); log₂ = роль
        ln/ln2 (бит-мера).  Element-сторона: log₂(2ᵏ)=k — процесс СХЛОПЫВАЕТСЯ в целое
        (диадическое, ln2 сокращается).  role-limit-сторона: log₂(3) — Cauchy-процесс,
        предел иррационален, НИКОГДА не рационален (DyadicBits, переинтерпретирован).
      Rules (L5): степенной ряд L(x)=Σxᵐ/m; доминирование log_series_term ≤ Qpow x m
        (LogZeta.log_series_term_le_power) → сравнение с геометрическим → Cauchy;
        функциональное уравнение ln(ab)≈ln a+ln b — process-equality (КРЕСТ, см. ниже);
        монотонность частичных сумм; рациональные двусторонние границы.
    ДИАГНОСТИКА (P4): бит-мера ТОЧНА ⟺ диадическая (граница финитизации вены A), но
      не-диадическая сторона теперь — именованный ПРОЦЕСС (вена C), не дыра.  Один файл
      соединяет вену A (точная граница) и вену C (предел=процесс).  0-аксиомно по
      построению (наследует classic из MonotoneConvergence через SeriesConvergence, как
      exp_series_cauchy).

    КРЕСТ ЗАДАЧИ: флагман log₂(2ᵏ)=k — НЕ численный факт (2ᵏ вне радиуса сходимости), а
      process-equality, держащаяся на функц. уравнении ln(2ᵏ)≈k·ln2 (равенство ПРОЦЕССОВ
      `~~`, не поточечное `==`).  Здесь доказан БАЗОВЫЙ случай k=1: log₂(2) ~~ 1 через
      самосокращение ln2/ln2 (cauchy_mul_inv_r_pos).  Общий k (аддитивность ln) и H(p)-
      максимум — следующий файл (честный горизонт).

    STATUS: 8 Qed, 0 Admitted, 0 axioms (наследует только classic через SeriesConvergence)
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia.
From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import RealField.
From ToS Require Import zeta.LogZeta.
From ToS Require Import stdlib.DyadicBits.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  ЯДРО: ln-серия как Cauchy-процесс (реплея exp_series_cauchy)        *)
(* ================================================================== *)

(** ★ ФЛАГМАН-ЛЕММА.  Ряд L(x) = Σ_{m≥1} xᵐ/m сходится (Cauchy над Q) для 0≤x<1.
    Доказательство — СРАВНЕНИЕ с геометрическим Σxᵐ: каждый член
    log_series_term x (S n) ≤ Qpow x (S n) ≤ Qpow x n (доминирование уже в LogZeta),
    а Σ Qpow x n — Cauchy (geometric_series_cauchy).  Это «процесс» из §0: объект,
    которого у DyadicBits не было. *)
Theorem ln_series_cauchy : forall x : Q,
  0 <= x -> x < 1 -> is_cauchy (log_series_partial x).
Proof.
  intros x Hx Hx1.
  unfold log_series_partial.
  apply (comparison_test (fun m => log_series_term x (S m)) (fun n => Qpow x n)).
  - intros n. apply log_series_term_nonneg. exact Hx.
  - intros n. apply Qpow_nonneg. exact Hx.
  - intros n.
    apply Qle_trans with (Qpow x (S n)).
    + apply log_series_term_le_power; [ exact Hx | lra | lia ].
    + apply Qpow_monotone_dec; [ exact Hx | lra ].
  - apply geometric_series_cauchy; [ exact Hx | exact Hx1 ].
Qed.

(* ================================================================== *)
(*  ОБЪЕКТЫ-ПРОЦЕССЫ: ln_proc, ln2_process, ln3_process                 *)
(* ================================================================== *)

(** ln(1/(1-x)) = -ln(1-x) как Cauchy-вещественное (для 0≤x<1). *)
Definition ln_proc (x : Q) (Hx : 0 <= x) (Hx1 : x < 1) : CauchySeq :=
  series_limit (fun m => log_series_term x (S m)) (ln_series_cauchy x Hx Hx1).

(** Каноническая ln 2 = -ln(1/2) = L(1/2) как ПРОЦЕСС. *)
Definition ln2_process : CauchySeq :=
  ln_proc (1#2) ltac:(lra) ltac:(lra).

(** ln 3 = -ln(1/3) = L(2/3) как ПРОЦЕСС (объект, которого DyadicBits не давал). *)
Definition ln3_process : CauchySeq :=
  ln_proc (2#3) ltac:(lra) ltac:(lra).

(** Стадии ln2_process — это в точности частичные суммы log_series_partial (1/2). *)
Lemma cs_seq_ln2 : forall n, cs_seq ln2_process n = log_series_partial (1#2) n.
Proof. intro n. reflexivity. Qed.

(* ================================================================== *)
(*  МОНОТОННОСТЬ И РАЦИОНАЛЬНЫЕ ГРАНИЦЫ (spec п.2)                       *)
(* ================================================================== *)

(** Нижняя рациональная граница: ln2 ≥ 1/2 (первая частичная сумма = 1/2, монотонна). *)
Lemma log2_half_partial_lower : forall n, 1#2 <= log_series_partial (1#2) n.
Proof.
  induction n.
  - assert (Hb : log_series_partial (1#2) 0 == 1#2) by (vm_compute; reflexivity).
    rewrite Hb. lra.
  - eapply Qle_trans; [ exact IHn | apply log_series_partial_increasing; lra ].
Qed.

(** Частичные суммы ln2 монотонно не убывают (роль-предел снизу). *)
Lemma ln2_partial_increasing : forall n,
  log_series_partial (1#2) n <= log_series_partial (1#2) (S n).
Proof. intro n. apply log_series_partial_increasing. lra. Qed.

(** Для обращения нужна СТРОГАЯ нижняя граница q>0 с q < стадия: берём q=1/3. *)
Lemma ln2_inv_lb : forall n : nat, (0 <= n)%nat -> (1#3) < cs_seq ln2_process n.
Proof.
  intros n _. rewrite cs_seq_ln2.
  pose proof (log2_half_partial_lower n). lra.
Qed.

(* ================================================================== *)
(*  log₂ := ln/ln2 (частное процессов) и ФЛАГМАН log₂(2) ~~ 1           *)
(* ================================================================== *)

(** Обратный процесс 1/ln2 (ln2 положителен, ограничен снизу 1/3). *)
Definition ln2_inv : CauchySeq :=
  cauchy_inv_pos ln2_process (1#3) 0 ltac:(lra) ln2_inv_lb.

(** log₂ от вещественного, заданного своим ln-процессом: (ln q)/ln2. *)
Definition log2_of (a : CauchySeq) : CauchySeq := cauchy_mul a ln2_inv.

(** ★ ФЛАГМАН (база креста, k=1): log₂(2) ~~ 1.
    Поскольку ln(2) = ln2_process, имеем log₂(2) = ln2/ln2 ~~ 1 — process-equality
    через самосокращение (cauchy_mul_inv_r_pos).  Это случай k=1 равенства log₂(2ᵏ)=k;
    общий k требует функц. уравнения ln(2ᵏ)≈k·ln2 (следующий файл). *)
Theorem log2_two : log2_of ln2_process ~~ cauchy_one.
Proof.
  unfold log2_of, ln2_inv. apply cauchy_mul_inv_r_pos.
Qed.

(* ================================================================== *)
(*  ПОЗИТИВНОЕ ПЕРЕОБРАМЛЕНИЕ DyadicBits: log₂3 = ПРОЦЕСС, не стена      *)
(* ================================================================== *)

(** ★ §0 формально.  log₂(3) — это РОЛЬ-ПРЕДЕЛ-ПРОЦЕСС:
      (левое) ОБЪЕКТ существует — ln3-серия Cauchy над Q (доказано нашим ядром),
              которого у DyadicBits НЕ было;
      (правое) role-limit-ДИАГНОСТИКА сохранена — нет конечной битовой записи
              (DyadicBits.log2_3_irrational, тот же чётностный аргумент).
    Вместе: иррациональность = процесс + диагностика, а НЕ несуществование/стена. *)
Theorem log2_3_process_not_wall :
  is_cauchy (log_series_partial (2#3))
  /\ ~ (exists a b : nat, (1 <= b)%nat /\ Nat.pow 2 a = Nat.pow 3 b).
Proof.
  split.
  - apply ln_series_cauchy; lra.
  - exact log2_3_irrational.
Qed.

(* ================================================================== *)
(*  СИНТЕЗ                                                              *)
(* ================================================================== *)

(** Капстоун первого файла, три грани log₂-в-битах-как-процесса:
      (1) ЯДРО — ln-серия Cauchy над Q для 0≤x<1 (ln_series_cauchy): объект существует;
      (2) ФЛАГМАН-БАЗА — log₂(2) ~~ 1 (k=1 креста, самосокращение ln2/ln2);
      (3) ПЕРЕОБРАМЛЕНИЕ — log₂(3) есть процесс (role-limit) + диагностика, не стена. *)
Theorem log2_process_synthesis :
  (forall x : Q, 0 <= x -> x < 1 -> is_cauchy (log_series_partial x))
  /\ (log2_of ln2_process ~~ cauchy_one)
  /\ (is_cauchy (log_series_partial (2#3))
      /\ ~ (exists a b : nat, (1 <= b)%nat /\ Nat.pow 2 a = Nat.pow 3 b)).
Proof.
  split; [ exact ln_series_cauchy | ].
  split; [ exact log2_two | exact log2_3_process_not_wall ].
Qed.

(** Аудит аксиом: должно быть ТОЛЬКО classic (0 новых аксиом). *)
Print Assumptions ln_series_cauchy.
Print Assumptions log2_two.
Print Assumptions log2_process_synthesis.

(* ===================================================================== *)
(*  Сводка: ln_series_cauchy (ядро, сравнение с геометрическим) даёт ln-  *)
(*  процесс; ln2_process = L(1/2), нижняя граница 1/2, монотонна;         *)
(*  log₂(2) ~~ 1 (база креста k=1, самосокращение); log₂(3) = процесс +   *)
(*  диагностика (не стена) — позитивное переобрамление DyadicBits.        *)
(*  ГОРИЗОНТ (следующий файл): функц. уравнение ln(ab)≈ln a+ln b ⟹ общий  *)
(*  log₂(2ᵏ)=k; H(p)-процесс + максимум на равновероятном.  0-аксиомно.   *)
(* ===================================================================== *)
