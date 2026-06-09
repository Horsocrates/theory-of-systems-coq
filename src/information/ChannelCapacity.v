(** * ChannelCapacity.v — пропускная способность двоичного симметричного канала над ℚ +
      максимум энтропии на равномерном (закрытие gap'ов §3.2/§3.3 Части XVI «Дискретная математика»).

   Корпус Шеннона уже несёт бинарную энтропию S2 (Паде-log) с пиком на равновероятном
   (`stdlib/ShannonSynthesis.v`) и взаимную информацию I(X;Y) (`stdlib/InformationTheory.v`).
   ЗДЕСЬ закрываются два названных gap'а плана Части XVI:
     §3.2 — МАКСИМУМ энтропии на равномерном (как РАВЕНСТВО-со-свидетелем, не только пик в точках);
     §3.3 — ПРОПУСКНАЯ СПОСОБНОСТЬ двоичного симметричного канала (BSC): C(p) = H_max − H(p).

   ★ АЛГЕБРАИЧЕСКОЕ ЯДРО (genuine).  Для Паде-энтропии замкнутая форма
       S2(p) = 6·p·(1−p) / [(p+1)·(2−p)],
   а ДЕФИЦИТ от равномерного есть ПЕРФЕКТНЫЙ КВАДРАТ:
       (2/3) − S2(p) = 4·(2p−1)² / [3·(p+1)·(2−p)].
   Числитель 4(2p−1)² ≥ 0, знаменатель > 0 на [0,1] ⟹ S2(p) ≤ 2/3 = S2(1/2) ВСЕГДА, с равенством
   тогда и только тогда, когда p=1/2 (равномерное).  Равномерное максимизирует энтропию ИМЕННО потому,
   что «расстояние от равномерного» есть КВАДРАТ (2p−1)² — тот же Element-квадрат, что disc-критерий
   рациональности (H38/H57 QuadraticDiscriminant).  Пропускная способность BSC C(p) := H_max − H(p) =
   этот же квадрат-дефицит: полная (C=2/3) при p=0 (нет шума), нулевая (C=0) при p=1/2 (максимум шума).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  ⚠ log здесь — рациональный Паде-ПРОКСИ (важны РАЗНОСТИ
   энтропии; истинный log2 = role-limit, не завершённый объект).  ГОРИЗОНТ (НЕ берём): общий n-арный
   максимум энтропии (через Schur-вогнутость / мажоризацию в общности), аксиоматическая ЕДИНСТВЕННОСТЬ
   меры (M1: аддитивность+монотонность+нормировка ⇒ −Σp log p), n-арный канал.  S2/ln_pade реплицированы
   из ShannonSynthesis (цитата, self-contained).

   Elements: вероятность ошибки p∈ℚ; Паде-log; квадрат (2p−1)²; крайние режимы p=0, p=1/2.
   Roles:    энтропия = роль-мера; равномерное = max-роль энтропии / min-роль ёмкости; (2p−1)² = Element.
   Rules:    дефицит от равномерного = квадрат ⟹ max на равномерном; C = H_max − H = квадрат-дефицит.

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: ёмкость BSC над ℚ + максимум энтропии на равномерном.
     Rules (L5): 2/3−S2(p)=4(2p−1)²/[3(p+1)(2−p)] (квадрат) ⟹ равномерное=max; C(p)=H_max−H(p)=квадрат-дефицит.
     Roles (L4): H=роль-мера; равномерное=max-энтропии/min-ёмкости; (2p−1)²=Element-структура.
     Elements  : p∈ℚ; Паде-log; квадрат (2p−1)²; режимы p=0/p=1/2.
     ОБРАЗУЮЩИЕ: ShannonSynthesis (S2, реплика); InformationTheory (I(X;Y), цитата); MajorizationSchur
                 (2-й закон); QuadraticDiscriminant H38/H57 (квадрат-критерий — тот же лейтмотив).
     ВЛОЖЕННЫЕ : H_max=S2(1/2)=2/3; C(0)=full / C(1/2)=0 — вложенные крайние режимы канала.
   ДИАГНОСТИКА (P4): ★ ёмкость = квадрат-дефицит энтропии от равномерного — равномерное максимизирует
   энтропию ИМЕННО потому, что дефицит есть КВАДРАТ (тот же Element-квадрат, что disc-критерий). Element-
   сторона (Паде-прокси) точна, 0-аксиом. ЧЕСТНО: log=Паде-прокси (истинный log2=role-limit); общий n-арный
   max + единственность M1 + n-арный канал = ГОРИЗОНТ.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Lia.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Базовые факты о квадратах над Q (Lqa nra не доказывает 0<=y*y)         *)
(* ===================================================================== *)

Lemma Qmul_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  intros a b Ha Hb. apply (Qle_trans _ (0 * b)).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply Qmult_le_compat_r; assumption.
Qed.

Lemma Qsq_nonneg : forall y : Q, 0 <= y * y.
Proof.
  intro y. destruct (Qlt_le_dec y 0) as [Hlt | Hge].
  - setoid_replace (y * y) with ((0 - y) * (0 - y)) by ring.
    apply Qmul_nonneg; lra.
  - apply Qmul_nonneg; assumption.
Qed.

Lemma Qsq_pos : forall y : Q, ~ (y == 0) -> 0 < y * y.
Proof.
  intros y Hy. assert (Hnn : 0 <= y * y) by apply Qsq_nonneg.
  destruct (proj1 (Qle_lteq 0 (y * y)) Hnn) as [H | H].
  - exact H.
  - exfalso. symmetry in H. apply Qmult_integral in H. destruct H; apply Hy; assumption.
Qed.

(* ===================================================================== *)
(*  Бинарная энтропия (Паде-log), реплицирована из ShannonSynthesis.v      *)
(* ===================================================================== *)

Definition ln_pade (x : Q) : Q := 2 * (x - 1) / (x + 1).
Definition S2 (a : Q) : Q := -(a * ln_pade a + (1 - a) * ln_pade (1 - a)).

(** Значение на равновероятном — максимум (нормировка Паде: H_max = 2/3). *)
Lemma binary_entropy_uniform : S2 (1#2) == 2#3.
Proof. unfold S2, ln_pade. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  ★ Замкнутая форма и КВАДРАТ-дефицит                                     *)
(* ===================================================================== *)

(** ★ Замкнутая форма: S2(p) = 6p(1−p) / [(p+1)(2−p)]. *)
Lemma S2_closed : forall p,
  ~ (p + 1 == 0) -> ~ (2 - p == 0) ->
  S2 p == 6 * p * (1 - p) / ((p + 1) * (2 - p)).
Proof. intros p H1 H2. unfold S2, ln_pade. field. split; assumption. Qed.

(** ★★ ЯДРО: дефицит энтропии от равномерного есть ПЕРФЕКТНЫЙ КВАДРАТ. *)
Lemma entropy_deficit_is_square : forall p,
  ~ (p + 1 == 0) -> ~ (2 - p == 0) ->
  (2#3) - S2 p == 4 * (2 * p - 1) * (2 * p - 1) / (3 * ((p + 1) * (2 - p))).
Proof. intros p H1 H2. unfold S2, ln_pade. field. split; assumption. Qed.

(* ===================================================================== *)
(*  ★ Максимум энтропии на равномерном (gap §3.2, бинарный случай)          *)
(* ===================================================================== *)

(** ★ Равномерное максимизирует бинарную энтропию: S2(p) ≤ 2/3 на [0,1]. *)
Lemma binary_entropy_max : forall p,
  0 <= p -> p <= 1 -> S2 p <= 2#3.
Proof.
  intros p Hp0 Hp1.
  assert (Hd1 : ~ (p + 1 == 0)) by (intro H; lra).
  assert (Hd2 : ~ (2 - p == 0)) by (intro H; lra).
  assert (Hpos : 0 < 3 * ((p + 1) * (2 - p))) by nra.
  assert (Heq : (2#3) - S2 p == 4 * (2 * p - 1) * (2 * p - 1) / (3 * ((p + 1) * (2 - p))))
    by (apply entropy_deficit_is_square; assumption).
  assert (Hge : 0 <= (2#3) - S2 p).
  { rewrite Heq. apply Qle_shift_div_l. exact Hpos. rewrite Qmult_0_l.
    setoid_replace (4 * (2 * p - 1) * (2 * p - 1)) with ((2 * (2 * p - 1)) * (2 * (2 * p - 1))) by ring.
    apply Qsq_nonneg. }
  lra.
Qed.

(** ★ Вне равномерного энтропия СТРОГО ниже максимума (дефицит = положительный квадрат). *)
Lemma binary_entropy_strict_below : forall p,
  0 <= p -> p <= 1 -> ~ (p == 1#2) -> S2 p < 2#3.
Proof.
  intros p Hp0 Hp1 Hne.
  assert (Hd1 : ~ (p + 1 == 0)) by (intro H; lra).
  assert (Hd2 : ~ (2 - p == 0)) by (intro H; lra).
  assert (Hpos : 0 < 3 * ((p + 1) * (2 - p))) by nra.
  assert (Hne2 : ~ (2 * p - 1 == 0)) by (intro H; apply Hne; lra).
  assert (Hsq : 0 < 4 * (2 * p - 1) * (2 * p - 1)).
  { setoid_replace (4 * (2 * p - 1) * (2 * p - 1)) with ((2 * (2 * p - 1)) * (2 * (2 * p - 1))) by ring.
    apply Qsq_pos. intro H. apply Hne2. lra. }
  assert (Heq : (2#3) - S2 p == 4 * (2 * p - 1) * (2 * p - 1) / (3 * ((p + 1) * (2 - p))))
    by (apply entropy_deficit_is_square; assumption).
  assert (Hgt : 0 < (2#3) - S2 p).
  { rewrite Heq. apply Qlt_shift_div_l. exact Hpos. rewrite Qmult_0_l. exact Hsq. }
  lra.
Qed.

(* ===================================================================== *)
(*  ★ Пропускная способность BSC (gap §3.3): C(p) = H_max − H(p)            *)
(* ===================================================================== *)

(** Пропускная способность двоичного симметричного канала с вероятностью ошибки p
    (нормировка Паде: H_max = 2/3 = «1 бит»). *)
Definition bsc_capacity (p : Q) : Q := (2#3) - S2 p.

(** ★ Ёмкость = квадрат-дефицит энтропии от равномерного. *)
Lemma bsc_capacity_is_square : forall p,
  ~ (p + 1 == 0) -> ~ (2 - p == 0) ->
  bsc_capacity p == 4 * (2 * p - 1) * (2 * p - 1) / (3 * ((p + 1) * (2 - p))).
Proof. intros p H1 H2. unfold bsc_capacity. apply entropy_deficit_is_square; assumption. Qed.

(** ★ Идеальный канал: нет шума (p=0) ⟹ полная ёмкость (= H_max = 2/3). *)
Lemma bsc_capacity_perfect : bsc_capacity 0 == 2#3.
Proof. unfold bsc_capacity, S2, ln_pade. vm_compute. reflexivity. Qed.

(** ★ Бесполезный канал: максимум шума (p=1/2) ⟹ нулевая ёмкость. *)
Lemma bsc_capacity_useless : bsc_capacity (1#2) == 0.
Proof. unfold bsc_capacity, S2, ln_pade. vm_compute. reflexivity. Qed.

(** ★ Ёмкость неотрицательна на [0,1] (= максимум энтропии на равномерном). *)
Lemma bsc_capacity_nonneg : forall p, 0 <= p -> p <= 1 -> 0 <= bsc_capacity p.
Proof. intros p H0 H1. unfold bsc_capacity. assert (S2 p <= 2#3) by (apply binary_entropy_max; assumption). lra. Qed.

(* ===================================================================== *)
(*  Капстоун                                                               *)
(* ===================================================================== *)

(** Двоичный симметричный канал над ℚ:
      (★ max-энтропии) равномерное максимизирует бинарную энтропию (дефицит = квадрат);
      (★ ёмкость)      C(p) = H_max − H(p) = тот же квадрат-дефицит;
      (режимы)         идеальный канал (p=0) → полная ёмкость 2/3; максимум шума (p=1/2) → ёмкость 0.
    Element-сторона (рациональный Паде-прокси) точна и 0-аксиомна; равномерное максимизирует энтропию
    ИМЕННО потому, что расстояние от него есть Element-квадрат (2p−1)². *)
Theorem bsc_channel_summary :
  (forall p, 0 <= p -> p <= 1 -> S2 p <= 2#3)
  /\ (forall p, 0 <= p -> p <= 1 -> 0 <= bsc_capacity p)
  /\ bsc_capacity 0 == 2#3
  /\ bsc_capacity (1#2) == 0.
Proof.
  split; [ exact binary_entropy_max |].
  split; [ exact bsc_capacity_nonneg |].
  split; [ exact bsc_capacity_perfect | exact bsc_capacity_useless ].
Qed.
