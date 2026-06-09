(** * UltrafilterRoleLimit.v — машинное СВИДЕТЕЛЬСТВО: ультрафильтр = role-limit, а не Element-истина.
      No-go (germ-кольцо Фреше НЕ поле: ∃ ненулевой необратимый) + ЛОКАЛИЗАЦИЯ работы ультрафильтра
      (препятствие = ровно одно неразрешённое множество Evens; решение неканонично) ⟹ вердикт role-limit.

   КОНТЕКСТ.  В `GermInfinitesimal.v` (Часть XVIII, Батч A) построено germ-кольцо ℚ^ℕ/Фреше и доказано
   `zero_divisors_exist` (even_ind·odd_ind ~ 0, оба ≁ 0).  ЗДЕСЬ извлекается ОНТОЛОГИЧЕСКОЕ следствие:
   делитель нуля — не курьёз, а МАШИННЫЙ СЕРТИФИКАТ отсутствующего ультрафильтра.

   ★ ЧТО МЫ НЕ ДЕЛАЕМ (граница против overclaim).  Мы НЕ «фальсифицируем» аксиому ультрафильтра: она
   непротиворечива (следует из AC / леммы о булевом простом идеале) и независима (в ZF её нельзя ни
   доказать, ни опровергнуть).  Мы НЕ ломаем аксиом поля.  «Деление на ноль» ни одна аксиома не
   «разрешает» — оно не определено; ультрафильтр лишь даёт ЛИЦЕНЗИЮ объявить бесконечное множество
   нулевых координат пренебрежимыми, после чего делить не на что нулевое.

   ★ ЧТО МЫ ДЕЛАЕМ (genuine no-go, машинно, 0 аксиом).
     (1) NO-GO:  germ-кольцо Фреше НЕ поле.  `even_ind` ≠ 0 (≁ нулю), но НЕОБРАТИМ: обратный был бы
         1/even_ind(n) = 1/0 на нечётных n.  Поле ⟹ нет делителей нуля; делитель есть ⟹ не поле.
     (2) ЛОКАЛИЗАЦИЯ:  всё препятствие = РОВНО одно неразрешённое множество Evens.  Объяви «Evens велико»
         (фактор по равенству на чётных) — `even_ind` СТАНОВИТСЯ единицей (сам себе обратный).  Объяви
         «Odds велико» — тот же `even_ind` СТАНОВИТСЯ нулём.  Один элемент, две противоположные судьбы
         от свободного решения ⟹ канонического значения НЕТ ⟹ role-limit.
     (3) ВЕРДИКТ (цитата):  продукт *ℝ консервативен (Хенсон–Кейслер) ⟹ леса устранимы.

   ★ ЧЕСТНАЯ ПОПРАВКА к прежней формулировке «LPO-зазор».  Точнее — НЕ LPO.  Решить ОДИН Σ⁰₁-факт = LPO;
   решить ВСЕ подмножества когерентно = ультрафильтр — строго ВЫШЕ лестницы LLPO⊏WLPO⊏LPO
   (`RoleLimitLadder.v`): это фрагмент AC (в ZF LPO держится даром, а свободного ультрафильтра может не
   быть).  Корректная метка — «ультрафильтр/выбор-зазор НАД LPO-лестницей».

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Доказано: germ-кольцо НЕ поле (ненулевой необратимый) +
   локализованные разрешения (mod Evens — единица, mod Odds — нуль).  НЕ доказано в Coq (цитаты):
   консервативность Хенсона–Кейслера (мета-теорема); общий «никакой выбор-свободный фактор ℚ^ℕ не поле»
   (доказан для КАНОНИЧЕСКОЙ конструкции Фреше; общее — честная экстраполяция).  Genuine — перевод
   концептуального вердикта в машинное свидетельствование препятствия + его локализация.

   Elements: GProc=nat→Q; even_ind/odd_ind; geq (Фреше), geq_on_evens/odds (уточн. фильтры); gmul/gconst.
   Roles:    even_ind=роль-индикатор Evens; обратимость=роль-единица; фильтр=роль-решатель; делитель=след.
   Rules:    germ-кольцо НЕ поле (ненул. необратимый); препятствие=Evens; mod Evens — единица, mod Odds — нуль.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: вердикт «ультрафильтр = role-limit» через необратимость делителя нуля + локализацию.
     Rules (L5): no-go (germ-кольцо не поле); локализация (препятствие = Evens); неканоничность (Evens→единица,
                 Odds→нуль); вердикт role-limit + консервативность (цитата).
     Roles (L4): even_ind=роль-индикатор Evens; обратимость=роль-единица; фильтр=роль-решатель; ультрафильтр=
                 тотальный решатель (role-limit); делитель нуля=роль-препятствие/след.
     Elements  : GProc; even_ind/odd_ind; geq/geq_on_evens/geq_on_odds; gmul/gconst.
     ОБРАЗУЮЩИЕ: GermInfinitesimal (germ-кольцо/zero_divisors, реплик.); RoleLimitLadder (лестница — ультрафильтр
                 НАД ней); ZFCAxiomLedger (Choice→L5); Хенсон–Кейслер (консервативность, цитата).
     ВЛОЖЕННЫЕ : раскол Evens/Odds = одно L3-неразрешённое различение; geq_on_evens vs geq_on_odds = два
                 несовместимых уточнения.
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (even_ind): Elements — значения 1,0,1,0,…; Roles — характеристика Evens, роль-делитель;
                 Rules — чередование ВНУТРИ, но правило обратимости ВНЕШНЕЕ («Evens велико?»), Фреше его не решает
                 ⟹ система НЕПОЛНА: unit-статус не определён внутренне, требует L5-решения (ультрафильтра),
                 неканоничного.  Свойство «делитель нуля» = способ системы сказать «обратимость не определена».
   ДИАГНОСТИКА (P4): всё конечно-глубинно по координате ⟹ Element; единственный role-limit — тотальное решение
                 (ультрафильтр), НЕ ассертим — предъявляем необходимость (no-go) и неканоничность (два разрешения).
   ЧЕСТНО: консервативность и общий no-go — цитаты/экстраполяция; доказано для канонической конструкции Фреше.

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Germ-кольцо ℚ^ℕ/Фреше (реплицировано из GermInfinitesimal.v —          *)
(*  во избежание stale .vo при кросс-импорте, по конвенции проекта)         *)
(* ===================================================================== *)

Definition GProc : Type := nat -> Q.
Definition gmul (x y : GProc) : GProc := fun n => x n * y n.
Definition gconst (q : Q) : GProc := fun _ => q.

(** Эквивалентность Фреше: совпадение на коконечном хвосте (велико = коконечно). *)
Definition geq (x y : GProc) : Prop := exists N, forall n, (N <= n)%nat -> x n == y n.

(** Обратимость в germ-кольце: ∃ обратный mod Фреше. *)
Definition g_invertible (x : GProc) : Prop := exists y, geq (gmul x y) (gconst 1).

(** Индикаторы чётных / нечётных (тот же делитель нуля, что в GermInfinitesimal). *)
Definition even_ind : GProc := fun n => if Nat.even n then 1 else 0.
Definition odd_ind  : GProc := fun n => if Nat.odd  n then 1 else 0.

(** Уточнённые фильтры: равенство на коконечном хвосте ВНУТРИ Evens / Odds
    (= «объявить Evens / Odds большим множеством»). *)
Definition geq_on_evens (x y : GProc) : Prop :=
  exists N, forall n, (N <= n)%nat -> Nat.even n = true -> x n == y n.
Definition geq_on_odds (x y : GProc) : Prop :=
  exists N, forall n, (N <= n)%nat -> Nat.odd n = true -> x n == y n.

(* ===================================================================== *)
(*  Делитель нуля (анкер): even_ind · odd_ind ~ 0                           *)
(* ===================================================================== *)

(** even_ind · odd_ind = 0 поточечно (никакое n не чётно И нечётно) ⟹ ~ 0. *)
Lemma even_times_odd_zero : geq (gmul even_ind odd_ind) (gconst 0).
Proof.
  exists 0%nat. intros n _.
  unfold gmul, even_ind, odd_ind, gconst. cbv beta.
  destruct (Nat.even n) eqn:E.
  - assert (Ho : Nat.odd n = false).
    { rewrite <- Nat.negb_even. rewrite E. reflexivity. }
    rewrite Ho. cbv iota. ring.
  - assert (Ho : Nat.odd n = true).
    { rewrite <- Nat.negb_even. rewrite E. reflexivity. }
    rewrite Ho. cbv iota. ring.
Qed.

(* ===================================================================== *)
(*  ★ NO-GO: germ-кольцо Фреше НЕ поле                                      *)
(* ===================================================================== *)

(** even_ind НЕ нуль mod Фреше: значение 1 в каждой чётной точке хвоста. *)
Lemma even_ind_not_zero : ~ geq even_ind (gconst 0).
Proof.
  intros [N HN].
  assert (Hle : (N <= 2 * N)%nat) by lia.
  specialize (HN (2 * N)%nat Hle).
  assert (He : Nat.even (2 * N) = true).
  { replace (2 * N)%nat with (0 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  unfold even_ind, gconst in HN. cbv beta in HN.
  rewrite He in HN. cbv iota in HN. lra.
Qed.

(** ★★ NO-GO-ядро: even_ind НЕОБРАТИМ.  Обратный был бы 1/even_ind = 1/0 на
    нечётных индексах; берём свидетель n = 2N+1 (нечётный, ≥ N) ⟹ 0·y = 1 ⟹ ложь. *)
Lemma even_ind_not_invertible : ~ g_invertible even_ind.
Proof.
  intros [y [N HN]].
  assert (Hle : (N <= 2 * N + 1)%nat) by lia.
  specialize (HN (2 * N + 1)%nat Hle).
  assert (Ho : Nat.even (2 * N + 1) = false).
  { replace (2 * N + 1)%nat with (1 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  unfold gmul, even_ind, gconst in HN. cbv beta in HN.
  rewrite Ho in HN. cbv iota in HN.
  rewrite Qmult_0_l in HN. lra.
Qed.

(** ★ germ-кольцо Фреше НЕ поле: существует ненулевой необратимый элемент. *)
Theorem germ_ring_not_field :
  exists x, ~ geq x (gconst 0) /\ ~ g_invertible x.
Proof.
  exists even_ind. split.
  - exact even_ind_not_zero.
  - exact even_ind_not_invertible.
Qed.

(* ===================================================================== *)
(*  ★ ЛОКАЛИЗАЦИЯ: всё препятствие = одно неразрешённое множество Evens     *)
(* ===================================================================== *)

(** Объяви «Evens велико» — even_ind становится ЕДИНИЦЕЙ (сам себе обратный):
    на чётных even_ind = 1, значит even_ind·even_ind = 1. *)
Lemma even_ind_invertible_mod_evens :
  exists y, geq_on_evens (gmul even_ind y) (gconst 1).
Proof.
  exists even_ind. exists 0%nat. intros n _ Heven.
  unfold gmul, even_ind, gconst. cbv beta.
  rewrite Heven. cbv iota. ring.
Qed.

(** Объяви «Odds велико» — тот же even_ind становится НУЛЁМ:
    на нечётных even_ind = 0. *)
Lemma even_ind_zero_mod_odds : geq_on_odds even_ind (gconst 0).
Proof.
  exists 0%nat. intros n _ Hodd.
  assert (He : Nat.even n = false).
  { rewrite <- Nat.negb_odd. rewrite Hodd. reflexivity. }
  unfold even_ind, gconst. cbv beta.
  rewrite He. cbv iota. reflexivity.
Qed.

(** ★ Неканоничность разрешения: ОДИН элемент even_ind — единица при «Evens велико»
    и нуль при «Odds велико».  Оба решения внутренне согласованы ⟹ канонического
    значения НЕТ ⟹ это решение лежит на role-limit-стороне (свободный выбор). *)
Theorem ultrafilter_decision_required :
  (exists y, geq_on_evens (gmul even_ind y) (gconst 1))
  /\ geq_on_odds even_ind (gconst 0).
Proof.
  split.
  - exact even_ind_invertible_mod_evens.
  - exact even_ind_zero_mod_odds.
Qed.

(* ===================================================================== *)
(*  Капстоун: вердикт role-limit                                            *)
(* ===================================================================== *)

(** Машинный вердикт «ультрафильтр = role-limit» (0 аксиом):
      (★ no-go)        germ-кольцо Фреше НЕ поле — ∃ ненулевой необратимый (even_ind);
      (★ локализация)  объяви «Evens велико» — even_ind единица; «Odds велико» — even_ind нуль;
      (★ неканоничность) один элемент, две противоположные судьбы от свободного решения.
    Делитель нуля — машинный СЛЕД отсутствующего ультрафильтра.  Мы НЕ опровергаем аксиому
    (консистентна, независима) — мы предъявляем РОВНО то препятствие, которое она существует залатать,
    и доказываем неканоничность латания.  Продукт *ℝ консервативен (Хенсон–Кейслер, цитата) ⟹
    устранимые леса.  Ультрафильтр строго НАД лестницей LLPO⊏WLPO⊏LPO (фрагмент AC). *)
Theorem ultrafilter_role_limit_summary :
  (exists x, ~ geq x (gconst 0) /\ ~ g_invertible x)
  /\ (exists y, geq_on_evens (gmul even_ind y) (gconst 1))
  /\ geq_on_odds even_ind (gconst 0).
Proof.
  split.
  - exact germ_ring_not_field.
  - exact ultrafilter_decision_required.
Qed.
