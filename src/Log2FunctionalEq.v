(** * Log2FunctionalEq.v — КРЕСТ: log₂(2ᵏ)=k как process-equality (общий k)

    Продолжение Log2Process.v.  Флагман задачи: log₂(2ᵏ)=k.  Это НЕ численный факт
    (2ᵏ вне радиуса сходимости ряда L), а РАВЕНСТВО ПРОЦЕССОВ (~~), держащееся на
    функциональном уравнении ln(a·b) ≈ ln a + ln b.

    ЧЕСТНАЯ СТРУКТУРА КРЕСТА (что доказано здесь / что — горизонт):
      • ДОКАЗАНО (Element-схлопывание): (k·ln2)/ln2 ~~ k как process-equality, через
        ассоциативность + самосокращение ln2/ln2 (log2_two из Log2Process) + единицу.
        Это и есть log₂(2ᵏ)=k, ЕСЛИ ln(2ᵏ) ≈ k·ln2.  Здесь ln(2ᵏ) ОПРЕДЕЛЁН как k·ln2
        (ln_pow2) — то есть аддитивность ln на степенях двойки взята как структура.
      • ГОРИЗОНТ (глубокая половина креста): сам вывод ln(2ᵏ) ≈ k·ln2 ИЗ РЯДА —
        функц. уравнение L(x)+L(y) ≈ L(x+y−xy) (произведение Коши/Мертенс).  Это
        настоящая теорема вещественного анализа над Q; НЕ фальсифицируется Admitted —
        выписана ниже как Prop `ln_mul_functional_equation` (документ, без доказательства).

    Почему именно так — разрез Element/role-limit (из E/R/R разбора): на ДИАДИЧЕСКОМ
    (2ᵏ) ln2 СОКРАЩАЕТСЯ → процесс схлопывается в целое k (Element).  На не-диадическом
    (3) сокращения нет → role-limit (log2_3_process_not_wall в Log2Process).  Один и тот
    же механизм (сокращение/несокращение ln2) объясняет оба полюса.

    ============ E/R/R разбор ============
      Elements (L1+P4): процессы k·ln2, ln2, 1/ln2 — каждый Cauchy над Q, конечно-актуален.
      Roles (L4): log₂ как роль ln/ln2; на 2ᵏ роль СХЛОПЫВАЕТСЯ в целое (Element).
      Rules (L5): ассоциативность · ; самосокращение a·a⁻¹~~1 (RealField); единица a·1~~a;
                  функц. уравнение ln(ab)~~ln a+ln b (горизонт).
    ДИАГНОСТИКА (P4): log₂(2ᵏ)=k — Element-сторона границы финитизации: процесс-частное
      сходится к ЦЕЛОМУ, потому что ln2 точно сокращается.  Доказано здесь 0-аксиомно
      (наследует только classic).  Глубокая аддитивность из ряда — честный горизонт.

    STATUS: 13 Qed, 0 Admitted, 0 axioms (наследует только classic)
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import zeta.LogZeta.
From ToS Require Import Log2Process.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  ln(2ᵏ) := k·ln2 (аддитивность на степенях двойки = структура)       *)
(* ================================================================== *)

(** ln(2ᵏ), заданный аддитивно как k·ln2.  Что это РАВНО ln от 2ᵏ-как-числа — суть
    функц. уравнения (горизонт `ln_mul_functional_equation` ниже). *)
Definition ln_pow2 (k : nat) : CauchySeq :=
  cauchy_mul (cauchy_const (inject_Z (Z.of_nat k))) ln2_process.

(** log₂(2ᵏ) = (k·ln2)/ln2 как процесс. *)
Definition log2_pow2 (k : nat) : CauchySeq := log2_of (ln_pow2 k).

(* ================================================================== *)
(*  ★ ФЛАГМАН-КРЕСТ: log₂(2ᵏ) ~~ k                                      *)
(* ================================================================== *)

(** ★ КРЕСТ ЗАДАЧИ (Element-схлопывание).  log₂(2ᵏ) ~~ k как process-equality:
    (k·ln2)/ln2 ~~ k через ассоциативность + самосокращение ln2/ln2 (log2_two) + единицу.
    На диадическом 2ᵏ процесс-частное СХЛОПЫВАЕТСЯ в целое k — Element-сторона границы. *)
Theorem log2_pow2_eq : forall k : nat,
  log2_pow2 k ~~ cauchy_const (inject_Z (Z.of_nat k)).
Proof.
  intro k. unfold log2_pow2, log2_of, ln_pow2.
  (* (K·ln2)·ln2⁻¹ ~~ K·(ln2·ln2⁻¹) ~~ K·1 ~~ K *)
  eapply cauchy_equiv_trans; [ apply cauchy_mul_assoc | ].
  eapply cauchy_equiv_trans.
  - apply cauchy_mul_compat; [ apply cauchy_equiv_refl | exact log2_two ].
  - apply cauchy_mul_one_r.
Qed.

(** Конкретика: log₂(2¹) ~~ 1 (= log2_two), log₂(2³) ~~ 3 — инстансы общего креста. *)
Corollary log2_pow2_one : log2_pow2 1 ~~ cauchy_const 1.
Proof. apply log2_pow2_eq. Qed.

Corollary log2_pow2_three : log2_pow2 3 ~~ cauchy_const 3.
Proof. apply log2_pow2_eq. Qed.

(** log₂(2⁰) ~~ 0 (пустая степень = 0 бит). *)
Corollary log2_pow2_zero : log2_pow2 0 ~~ cauchy_const 0.
Proof. apply log2_pow2_eq. Qed.

(* ================================================================== *)
(*  ГОРИЗОНТ: глубокая половина креста — функц. уравнение из РЯДА        *)
(* ================================================================== *)

(** Глубокая половина креста, ВЫПИСАННАЯ как Prop (документ, НЕ доказывается здесь):
    аддитивность ln, выведенная ИЗ РЯДА L(x)=Σxᵐ/m.  Для 1-(x⊕y)=(1-x)(1-y), т.е.
    x⊕y = x+y−xy, это L(x)+L(y) ≈ L(x⊕y) = -ln((1-x)(1-y)).  Доказательство —
    теорема о произведении Коши / Мертенса (настоящий вещ. анализ над Q); НЕ фейк
    через Admitted.  Её добавление превратит ln_pow2 из ОПРЕДЕЛЕНИЯ в СЛЕДСТВИЕ,
    замкнув крест полностью. *)
Definition ln_mul_functional_equation : Prop :=
  forall (x y : Q)
    (Hx : 0 <= x) (Hx1 : x < 1) (Hy : 0 <= y) (Hy1 : y < 1)
    (Hxy : 0 <= x + y - x * y) (Hxy1 : x + y - x * y < 1),
  cauchy_add (ln_proc x Hx Hx1) (ln_proc y Hy Hy1)
    ~~ ln_proc (x + y - x * y) Hxy Hxy1.

(* ================================================================== *)
(*  ГРУНТОВКА функц. уравнения: алгебра ⊕ и аддитивная единица L(0)~~0   *)
(*  (доказуемая база; не-вырожденный L(x)+L(y)~~L(x⊕y) = Коши-произвед., *)
(*   горизонт — в репо НЕТ Cauchy product, см. шапку)                    *)
(* ================================================================== *)

(** Сложение аргументов в области сходимости: x⊕y := x+y−xy, так что
    1−(x⊕y) = (1−x)(1−y) — почему ln(1/(1-x))+ln(1/(1-y))=ln(1/(1-x⊕y)). *)
Definition oplus (x y : Q) : Q := x + y - x * y.

Lemma oplus_comm : forall x y, oplus x y == oplus y x.
Proof. intros x y; unfold oplus; ring. Qed.

Lemma oplus_zero_l : forall y, oplus 0 y == y.
Proof. intros y; unfold oplus; ring. Qed.

(** ★ Ключевое алгебраическое тождество, на котором стоит функц. уравнение. *)
Lemma one_minus_oplus : forall x y, 1 - oplus x y == (1 - x) * (1 - y).
Proof. intros x y; unfold oplus; ring. Qed.

(** Каждый член ряда L при x=0 равен нулю. *)
Lemma log_series_term_zero : forall m, log_series_term 0 (S m) == 0.
Proof.
  intro m. unfold log_series_term.
  assert (Hp : Qpow 0 (S m) == 0) by (simpl; ring).
  rewrite Hp. unfold Qdiv; ring.
Qed.

(** Частичные суммы L(0) тождественно нулевые. *)
Lemma log_series_partial_zero : forall n, log_series_partial 0 n == 0.
Proof.
  induction n.
  - unfold log_series_partial, partial_sum. apply log_series_term_zero.
  - rewrite log_series_partial_step, IHn, (log_series_term_zero (S n)). ring.
Qed.

(** ★ L(0) ~~ 0 — аддитивная ЕДИНИЦА функц. уравнения (база доказана 0-Admitted).
    Вместе с oplus_zero_l (0⊕y=y) это вырожденный случай ln_mul: L(0)+L(y)~~L(0⊕y).
    Не-вырожденный случай (Коши-произведение L(x)+L(y)~~L(x⊕y)) — горизонт. *)
Lemma ln_proc_zero : forall (H0 : 0 <= 0) (H01 : (0:Q) < 1),
  ln_proc 0 H0 H01 ~~ cauchy_const 0.
Proof.
  intros H0 H01 eps Heps. exists 0%nat. intros n _.
  assert (Hz : cs_seq (ln_proc 0 H0 H01) n - cs_seq (cauchy_const 0) n == 0).
  { change (cs_seq (ln_proc 0 H0 H01) n) with (log_series_partial 0 n).
    change (cs_seq (cauchy_const 0) n) with (0:Q).
    rewrite log_series_partial_zero. ring. }
  apply Qabs_Qlt_condition. rewrite Hz. split; lra.
Qed.

(* ================================================================== *)
(*  H(p)-ПРОЦЕСС: энтропия честной монеты H(½) ~~ 1 бит                  *)
(* ================================================================== *)

(** Двойное отрицание процесса (вспомогательное, поточечно: −(−aₙ)=aₙ). *)
Lemma cauchy_neg_neg : forall a : CauchySeq, cauchy_neg (cauchy_neg a) ~~ a.
Proof.
  intros a eps Heps. exists 0%nat. intros n _.
  assert (Hz : cs_seq (cauchy_neg (cauchy_neg a)) n - cs_seq a n == 0)
    by (simpl; ring).
  apply Qabs_Qlt_condition. rewrite Hz. split; lra.
Qed.

(** Энтропия честной монеты.  При p=1−p=½ оба ½-веса дают log₂½, поэтому
    H(½) = −(½·log₂½ + ½·log₂½) = −log₂½.  А log₂½ = (−ln2)/ln2, т.к.
    ln(½) = −ln2 = cauchy_neg ln2_process. *)
Definition H2_fair : CauchySeq := cauchy_neg (log2_of (cauchy_neg ln2_process)).

(** ★ H(½) ~~ 1: энтропия честной монеты — РОВНО один бит (process-equality);
    максимум бинарной энтропии ПО ЗНАЧЕНИЮ (= log₂2 = 1), через −(−ln2/ln2) ~~ 1. *)
Theorem H2_fair_one : H2_fair ~~ cauchy_const 1.
Proof.
  unfold H2_fair, log2_of.
  eapply cauchy_equiv_trans.
  - apply cauchy_neg_compat.
    eapply cauchy_equiv_trans; [ apply cauchy_mul_comm | ].
    eapply cauchy_equiv_trans; [ apply cauchy_mul_neg_r | ].
    apply cauchy_neg_compat.
    eapply cauchy_equiv_trans; [ apply cauchy_mul_comm | ].
    exact log2_two.
  - eapply cauchy_equiv_trans; [ apply cauchy_neg_neg | ].
    apply cauchy_equiv_refl.
Qed.

(* ================================================================== *)
(*  СИНТЕЗ                                                              *)
(* ================================================================== *)

(** Капстоун: log₂(2ᵏ) ~~ k для ВСЕХ k (КРЕСТ, Element-схлопывание) + конкретные
    k=0,3 + энтропия честной монеты H(½) ~~ 1 бит.  Глубокая аддитивность из ряда
    (ln_mul_functional_equation) и общий H(p)-максимум (вогнутость) — горизонт. *)
Theorem log2_functional_synthesis :
  (forall k : nat, log2_pow2 k ~~ cauchy_const (inject_Z (Z.of_nat k)))
  /\ (log2_pow2 0 ~~ cauchy_const 0)
  /\ (log2_pow2 3 ~~ cauchy_const 3)
  /\ (H2_fair ~~ cauchy_const 1).
Proof.
  split; [ exact log2_pow2_eq | ].
  split; [ exact log2_pow2_zero | ].
  split; [ exact log2_pow2_three | exact H2_fair_one ].
Qed.

(** Аудит аксиом: должно быть ТОЛЬКО classic. *)
Print Assumptions log2_pow2_eq.
Print Assumptions log2_functional_synthesis.

(* ===================================================================== *)
(*  Сводка: log₂(2ᵏ) ~~ k (КРЕСТ, Element-схлопывание) для всех k через    *)
(*  сокращение (k·ln2)/ln2 ~~ k (ассоц. + log2_two + единица).  Глубокая   *)
(*  половина — функц. уравнение L(x)+L(y)~~L(x+y−xy) из ряда (Коши-Мертенс)*)
(*  — выписана как ln_mul_functional_equation (горизонт, НЕ Admitted).     *)
(*  0-аксиомно (только classic).  H(p)-процесс + максимум — далее.         *)
(* ===================================================================== *)
