# Глава X.4 «Аксиома выбора: запрет и переинтерпретация» — заметки к ведомости (12.11.2026)

Ведомость: `part10-ch04.json` — 69 ручных записей + 4 автоматических (упоминания файлов); `merge --dry` проходит
без замечаний, список «без сверки» пуст. Вердикты ручных записей: ok — 54, mismatch-statement — 15; расхождений
в цене, в числах и отсутствующих имён нет (с автоматическими: ok — 58).

Пятнадцать записей mismatch-statement относятся к шести местам (расхождения 1–6): две — к опущенной посылке
теоремы несовместимости, одна — к словам «полная форма запрещена», шесть — к «запрет сильнее переинтерпретации»,
две — к совместимости потенциальной бесконечности, одна — к «конечной лемме Цорна», три — к границе между L4 и
выбором.

Цена во всех местах главы названа верно: каждое объявление файлов `P4_Eliminates_AC.v`, `P4ProhibitsAC.v`,
`P4CompletedInfinity.v`, `P4ProhibitionSynthesis.v`, названное в главе, — «Closed under the global context»;
`L4_witness` — аксиома; `L4_definite`, `Schroeder_Bernstein`, `cardinal_antisym` — на `ToS_Axioms.L4_witness`
(две последние — ещё и на `Classical_Prop.classic`). Счёт `Qed` в файлах совпадает с шапками: 15, 12, 9, 6.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part10/ch04/`: `Check.v` (18 утверждений), `CheckL4.v`,
`CheckDC.v`, `CheckSB.v`. Все четыре собираются; ответы `Print Assumptions` приведены по месту. В `src` и в
собранной копии ничего не менялось.

## Что проверить не удалось

- Тезисы о полной аксиоме выбора ZFC, о парадоксе Банаха–Тарского и множествах Витали, об «онтологической
  категории» L4 и выбора — не утверждения о формализации; компилятором они не проверяются. Глава сама отделяет их
  от доказанного (стр. 60–61, 132–133, сноска 8).
- Отсылки к главам 10.3 и 10.5 проверены только в объёме названного здесь: цены `Schroeder_Bernstein`,
  `cardinal_antisym`, `injects_refl`, `injects_trans`, `no_maximal_cardinality`. Слова о «линейности кардинальной
  шкалы» (стр. 9) теоремой в формализации не представлены — сверять не с чем.
- Замечание о принципе разбиения (раздел «Вне главы») — математическое, по литературе; компилятором не
  проверялось.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Противоречие с P4 получено при третьей посылке — мосте; глава её не называет (стр. 55–57; сноска 4, стр. 166)

**Было:**

> (55–57) А P4 (конечная актуальность) требует, чтобы на каждой стадии было актуально лишь конечное. Завершённая
> бесконечная совокупность нарушает эту ограниченность — противоречие.[^4]
>
> (166) … И `P4CompletedInfinity.v`: `CompletedInfSet` против `P4_stage_bounded`, итог —
> `completed_inf_contradicts_P4`. Всё **0 аксиом**.

**Проверка.** `src/foundation/P4CompletedInfinity.v`:

```coq
Definition CompletedInfSet (S : nat -> Prop) : Prop := forall n : nat, S n.                       (* :29 *)
Definition P4_stage_bounded (actual : nat -> nat -> Prop) : Prop :=                               (* :33 *)
  forall stage : nat, exists bound : nat, forall n : nat, actual stage n -> (n <= bound)%nat.
Definition bridge (S : nat -> Prop) (actual : nat -> nat -> Prop) : Prop :=                       (* :42 *)
  forall n : nat, S n -> actual 0%nat n.
Theorem completed_inf_contradicts_P4 :                                                            (* :64 *)
  forall (S : nat -> Prop) (actual : nat -> nat -> Prop),
  CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False.
```

`Print Assumptions`: Closed under the global context. Посылок три. «Завершённое множество» по определению — предикат,
истинный на всех натуральных числах; о стадиях оно не говорит. Для графика функции это свойство
(`choice_graph_completed`, `P4ProhibitsAC.v:65`) есть у любой `f : nat -> nat`, в том числе у разрешённого правила
«голова списка». «Взятость разом» записана третьей посылкой — мостом: всякий член совокупности актуален уже на
нулевой стадии. В пробном файле (`Check.v`) доказано, все — Closed under the global context:

```coq
(* без моста первые две посылки совместны — даже для графика головы списка *)
Lemma completed_and_bounded_consistent : forall F : nat -> list nat,
  exists actual : nat -> nat -> Prop,
    CompletedInfSet (graph_indices (choice_graph (fun n => L5_choose (F n) 0))) /\
    P4_stage_bounded actual.

(* содержание теоремы несовместимости: ограниченная стадия не содержит всех чисел *)
Lemma contradiction_core_equiv :
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False)
  <->
  (forall actual, P4_stage_bounded actual -> ~ (forall n, actual 0%nat n)).
```

Глава 4.1 те же три посылки называет и говорит: «Это *условная* теорема: противоречие получается при наличии всех
трёх посылок» (стр. 797–814, 837–851 той главы).

**В чём расхождение.** Теорема выводит противоречие из трёх посылок; глава называет две, а третья — та, что
несёт смысл слов «взятый разом», — не названа.

**(а) Довести формализацию.** До слов «завершённая совокупность нарушает ограниченность» без моста — нельзя:
утверждение неверно (первая лемма выше — совместная модель: актуальность `fun stage n => n <= stage`). Мост и есть
формальная запись «готовой совокупности»; убрать его из теоремы нечем.

**(б) Поправить слова:**

> (53–57) Ключевой момент: график такой $f$ (в коде это `choice_graph` — совокупность пар «индекс, значение»)
> содержит пару на всяком индексе. Взять его разом, как готовый объект, значит считать все эти пары актуальными
> на одной стадии; в формализации это отдельная посылка — *мост* (`bridge`). А P4 (конечная актуальность)
> требует, чтобы на каждой стадии было актуально лишь конечное. График с парой на всяком индексе, стадийная
> ограниченность и мост вместе дают противоречие.[^4] Теорема условная: без моста противоречия нет, и то же
> противоречие даёт график любой всюду определённой функции — P4 отсекает не функцию, а её чтение как
> завершённого целого.
>
> (166) [^4]: `P4ProhibitsAC.v`: `AC_on_nat` (полная форма), `ac_implies_completed` (AC даёт функцию, график
> которой имеет пару на всяком индексе), `ac_completed_graph_contradicts_P4` (всё рассуждение одной теоремой),
> `P4_prohibits_AC` (сводка). И `P4CompletedInfinity.v`: `CompletedInfSet`, `P4_stage_bounded` и мост `bridge`
> (всякий член совокупности актуален уже на нулевой стадии); итог — `completed_inf_contradicts_P4`: три посылки
> вместе противоречивы. Границу доказанного называет сам файл: то же противоречие даёт график любой всюду
> определённой функции (`completed_graph_contradicts_P4`), а выбор из непустых списков как правило есть теорема
> (`AC_on_nat_as_rule`). Всё **0 аксиом**.

По желанию — слово «при мосте» в двух сводках: стр. 68 («P4 его запрещает (`completed_inf_contradicts_P4`)») и
стр. 146–147 («несовместима с P4 (`completed_inf_contradicts_P4`)»). В ведомости эти места записаны как верные:
слова «как готовый бесконечный объект» отвечают мосту.

## Расхождение 2. «Полная форма — запрещена»: утверждение `AC_on_nat` в формализации доказано (стр. 123–124)

**Было:** «Полная форма — запрещена (`P4_prohibits_AC`, `completed_inf_contradicts_P4`).»

**Проверка.** «Полная форма» по сноске 4 — `AC_on_nat` (`P4ProhibitsAC.v:43`):
`forall F : nat -> list nat, (forall n, F n <> nil) -> exists f : nat -> nat, forall n, In (f n) (F n)`. Это
дословно утверждение `AC_is_L5` (`P4_Eliminates_AC.v:139`), которое предыдущая фраза главы называет теоремой
(`Check.v`: `AC_on_nat_is_AC_is_L5_statement`, `AC_on_nat_from_AC_is_L5`). В самом файле оно доказано:
`Lemma AC_on_nat_as_rule : AC_on_nat` (`:160`), Closed under the global context; шапка файла (`:18–25`): «AC_on_nat
itself is NOT refuted and cannot be».

`P4_prohibits_AC` (`:186`) — конъюнкция трёх утверждений:

```coq
Theorem P4_prohibits_AC :
  AC_gives_completed_graph /\
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False) /\
  (forall F N, (forall n, (n < N)%nat -> F n <> nil) ->
    forall n, (n < N)%nat -> In (finite_choice F N n) (F n)).
```

Первый член (`ac_implies_completed`): из `AC_on_nat` следует, что для всякого семейства есть функция выбора, график
которой имеет пару на каждом индексе. Его заключение верно и без посылки (`Check.v`:
`ac_implies_completed_conclusion_free`). Противоречие с участием выбора даёт другая теорема —
`ac_completed_graph_contradicts_P4` (`:122`), и в ней работает мост; посылка `AC_on_nat` в ней тоже лишняя
(`Check.v`: `completed_choice_graph_contradiction_free`).

**В чём расхождение.** Одно и то же утверждение названо в соседних фразах теоремой и запрещённым; несовместимо с
P4 не оно, а чтение графика функции выбора как завершённого целого.

**(а) Довести формализацию.** Вывести противоречие из `AC_on_nat` нельзя: она доказана. Можно дать одну теорему,
которая закрепляет слова главы «выбор расщепляется надвое» (стр. 136): завершённое чтение графика любой функции
выбора несовместимо с P4, чтение-правило совместимо. Набросок проверен (`Check.v`), Closed under the global
context:

```coq
(* чтение-правило: всякая пара графика становится актуальной на некоторой стадии *)
Definition rule_reading (S : nat -> Prop) (actual : nat -> nat -> Prop) : Prop :=
  forall n, S n -> exists stage, actual stage n.

Theorem choice_as_rule_compatible_with_P4 :
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  exists (f : nat -> nat) (actual : nat -> nat -> Prop),
    (forall n, In (f n) (F n)) /\
    P4_stage_bounded actual /\
    rule_reading (graph_indices (choice_graph f)) actual.
Proof.
  intros F Hne.
  exists (fun n => L5_choose (F n) 0%nat), (fun stage n => (n <= stage)%nat).
  split; [| split].
  - intro n. apply L5_choose_in. apply Hne.
  - intro stage. exists stage. intros n H. exact H.
  - intros n _. exists n. apply Nat.le_refl.
Qed.

Theorem P4_cuts_completed_keeps_rule :
  forall F : nat -> list nat, (forall n, F n <> nil) ->
  (forall (f : nat -> nat) (actual : nat -> nat -> Prop),
     (forall n, In (f n) (F n)) ->
     P4_stage_bounded actual ->
     ~ bridge (graph_indices (choice_graph f)) actual) /\
  (exists (f : nat -> nat) (actual : nat -> nat -> Prop),
     (forall n, In (f n) (F n)) /\
     P4_stage_bounded actual /\
     rule_reading (graph_indices (choice_graph f)) actual).
Proof.
  intros F Hne. split.
  - intros f actual _ HP4 Hb. exact (completed_graph_contradicts_P4 f actual HP4 Hb).
  - exact (choice_as_rule_compatible_with_P4 F Hne).
Qed.
```

Место — `P4ProhibitsAC.v`; новых подключений не нужно. Свидетель в доказательстве — актуальность
`fun stage n => n <= stage` (то же определение в формализации есть под именем `nat_staged_actual`,
`P4ProhibitsImpredicative.v:99`). Заодно получают опору слова стр. 40 и 42 «P4-совместима»: сейчас в
`P4_Eliminates_AC.v` связи выбора-правила со стадийной ограниченностью нет.

**(б) Поправить слова** (нужно в обоих случаях):

> Полная форма как утверждение совпадает с ядром и тоже доказана (`AC_on_nat_as_rule`); запрещено её чтение —
> график функции выбора как завершённое целое: вместе со стадийной ограниченностью и мостом оно даёт
> противоречие (`ac_completed_graph_contradicts_P4`, `completed_inf_contradicts_P4`; сводка —
> `P4_prohibits_AC`).

## Расхождение 3. «Запрет сильнее переинтерпретации» подан как теорема (стр. 74, 76–79, 124–125, 147–148; сноска 6, стр. 168)

**Было:**

> (74) Два уровня — не одно и то же, и их связь сама есть теорема.
>
> (76–79) В формальном синтезе запрет *даёт* переинтерпретацию (если завершённый объект невозможен, он тем более
> не нужен как постулат), тогда как одна переинтерпретация сама по себе противоречия object-формы не даёт — в
> этом смысле запрет сильнее.[^6]
>
> (124–125) Связь — `prohibition_implies_reinterpretation` (запрет сильнее).
>
> (147–148) и запрет строго сильнее переинтерпретации (`prohibition_implies_reinterpretation`).
>
> (168) `P4ProhibitionSynthesis.v`: `prohibition_implies_reinterpretation` (запрет влечёт переинтерпретацию),
> `reinterpretation_weaker` (обратное неверно), `P4_is_prohibition`. 0 аксиом.

**Проверка.** `src/foundation/P4ProhibitionSynthesis.v`:

```coq
Theorem prohibition_implies_reinterpretation :                       (* :72 *)
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False) ->
  potential_infinity.
Proof.
  intros _. exact potential_inf_exists.
Qed.

Lemma reinterpretation_weaker : potential_infinity.                  (* :84 *)
Proof. exact potential_inf_exists. Qed.
```

где `potential_infinity := forall n : nat, exists m : nat, n < m`. Все утверждения файла — Closed under the global
context. Посылка первой теоремы в доказательстве не используется. Вторая лемма утверждает то же, что
`potential_inf_exists`; о неверности обратного говорит только комментарий к ней. В Rocq обратная импликация
доказуема (`Check.v`, Closed under the global context):

```coq
Lemma converse_of_prohibition_implies_reinterpretation :
  potential_infinity ->
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False).
Proof. intros _. exact completed_inf_contradicts_P4. Qed.
```

Оба утверждения — замкнутые теоремы, поэтому каждое следует из другого. К тому же «переинтерпретация» в файле —
потенциальная бесконечность, а в главе — выбор по правилу L5.

Глава 4.1 об этой теореме говорит: «посылку она *не использует* … скорее синтетическая *сводка* … содержательное
соотношение слоёв … верно, но обосновано оно рассуждением, а не этой конкретной теоремой» (стр. 886–902 той
главы).

**В чём расхождение.** Соотношение «запрет влечёт переинтерпретацию, обратное неверно» в формализации теоремой не
выражено; названные теоремы его не доказывают, а в записанном виде обратное следование верно.

**(а) Довести формализацию.** В виде «одно замкнутое утверждение строго сильнее другого» — нельзя: две доказанные
теоремы равносильны. Честно выразимо соотношение двух *чтений* графика: завершённое чтение требует строго
больше, чем чтение-правило, и P4 отсекает именно его. Набросок проверен (`Check.v`, определение `rule_reading` —
в расхождении 2), Closed under the global context:

```coq
Theorem completed_reading_strictly_stronger :
  (forall S actual, bridge S actual -> rule_reading S actual) /\
  (forall f : nat -> nat, exists actual : nat -> nat -> Prop,
     P4_stage_bounded actual /\
     rule_reading (graph_indices (choice_graph f)) actual /\
     ~ bridge (graph_indices (choice_graph f)) actual).
Proof.
  split.
  - intros S actual Hb n Hn. exists 0%nat. apply Hb. exact Hn.
  - intro f. exists (fun stage n => (n <= stage)%nat).
    assert (HP4 : P4_stage_bounded (fun stage n => (n <= stage)%nat)).
    { intro stage. exists stage. intros n H. exact H. }
    split; [exact HP4 | split].
    + intros n _. exists n. apply Nat.le_refl.
    + intro Hb. exact (completed_graph_contradicts_P4 f _ HP4 Hb).
Qed.
```

С этой теоремой (и с `P4_cuts_completed_keeps_rule` из расхождения 2) слова «их связь сама есть теорема» получают
опору в таком виде: завершённое чтение влечёт чтение-правило; обратного нет; при P4 первое невозможно, второе
выполнимо. Две нынешние теоремы тогда можно оставить как сводку или снять: вне своего файла они в `src` не
упоминаются (проверено поиском).

**(б) Поправить слова** (если формализацию не трогать):

> (74–79) Два уровня — не одно и то же. *Переинтерпретация* говорит: P4 делает выбор *ненужным* как аксиому, ибо
> его работу выполняет L5. *Запрет* говорит: P4 *несовместима* с завершённой формой выбора. Соотношение их
> таково: если завершённый объект невозможен, он тем более не нужен как постулат, тогда как наличие замены само
> по себе невозможности исходного не даёт — в этом смысле запрет сильнее. Обосновано это соотношение
> рассуждением: файл синтеза ставит оба уровня рядом, но теоремой их связь не выражает.[^6]
>
> (124–125) Связь двух уровней — рассуждение раздела «Синтез»; файл `P4ProhibitionSynthesis.v` собирает оба
> уровня в сводных теоремах.
>
> (147–148) и запрет сильнее переинтерпретации: невозможное тем более не нужно.
>
> (168) [^6]: `P4ProhibitionSynthesis.v`: сводные теоремы `P4_prohibits_three`, `P4_preserves_three`,
> `P4_is_prohibition`. Теорема `prohibition_implies_reinterpretation` по формулировке гласит «если завершённая
> бесконечность несовместима с P4 при мосте, то есть потенциальная бесконечность», но посылку не использует;
> `reinterpretation_weaker` повторяет её заключение. Это сводка двух доказанных фактов, а не доказательство
> следования (см. Главу 4.1). 0 аксиом.

Слова «запрет строго сильнее» на стр. 15, 24, 88, 137 стоят тезисом без ссылки на теорему; в ведомости они
записаны как верные с пометкой. Слово «строго» в них стоит согласовать с выбранным вариантом.

## Расхождение 4. `potential_compatible_with_P4` не говорит о процессе (стр. 62–63; сноска 5, стр. 167)

**Было:**

> (62–63) ToS не запрещает бесконечные *процессы*: потенциальная бесконечность с P4 вполне совместима.[^5]
>
> (167) `P4CompletedInfinity.v`: `potential_compatible_with_P4` — потенциальная бесконечность не противоречит P4.

**Проверка.** `P4CompletedInfinity.v:93`:

```coq
Lemma potential_compatible_with_P4 :
  exists (actual : nat -> nat -> Prop), P4_stage_bounded actual /\ potential_infinity.
```

Closed under the global context. Второй член (`forall n, exists m, n < m`) от `actual` не зависит; под `exists`
годится любая ограниченная актуальность. В пробном файле то же утверждение доказано на пустой актуальности
(`Check.v`: `potential_compatible_statement_on_empty_actuality`, свидетель `fun _ _ => False`).

**В чём расхождение.** Теорема соединяет два независимых факта — есть ограниченная актуальность, и за всяким числом
есть большее; о процессе, который растёт по стадиям и остаётся ограниченным на каждой, она не говорит.

**(а) Довести формализацию.** Возможно; набросок проверен (`Check.v`), Closed under the global context:

```coq
Theorem potential_process_compatible_with_P4 :
  exists actual : nat -> nat -> Prop,
    P4_stage_bounded actual /\
    (forall stage n, actual stage n -> actual (S stage) n) /\   (* стадии вложены *)
    (forall n, exists stage, actual stage n) /\                 (* всякое число достигается *)
    (forall stage, exists n, ~ actual stage n).                 (* ни одна стадия не содержит всего *)
Proof.
  exists (fun stage n => (n <= stage)%nat).
  split; [| split; [| split]].
  - intro stage. exists stage. intros n H. exact H.
  - intros stage n H. lia.
  - intro n. exists n. apply Nat.le_refl.
  - intro stage. exists (S stage). lia.
Qed.
```

После добавления этой теоремы слова главы верны без правки (в сноске 5 — её имя).

**(б) Поправить слова** (если формализацию не трогать):

> (167) [^5]: `P4CompletedInfinity.v`: `potential_compatible_with_P4` — существует актуальность, ограниченная на
> каждой стадии, и при этом за всяким числом есть большее. Запрещён именно *завершённый* объект, не процесс.

## Расхождение 5. «Конечная лемма Цорна» — наибольшее число в списке (стр. 34–36)

**Было:** «Из той же конечности следует и «конечная лемма Цорна»: в непустом конечном списке есть максимальный
элемент — просто максимум списка, без всякого выбора.[^2]»

**Проверка.** `P4_Eliminates_AC.v:124`:

```coq
Lemma finite_zorn : forall l, l <> nil -> exists m, In m l /\ forall n, In n l -> (n <= m)%nat.
```

`l : list nat`, порядок — обычный порядок натуральных чисел; Closed under the global context. Формула сноски 2
совпадает с утверждением.

**В чём расхождение.** Лемма Цорна говорит о максимальном элементе частично упорядоченного множества; доказано
существование наибольшего числа в списке натуральных чисел. Тип элементов и порядок в основном тексте не названы.

**(а) Довести формализацию.** Возможно, без допущений: для произвольного типа и произвольного разрешимого
транзитивного отношения в непустом списке есть максимальный элемент. Набросок проверен (`Check.v`), Closed under
the global context:

```coq
Section FiniteZorn.
  Variable A : Type.
  Variable le : A -> A -> bool.
  Hypothesis le_trans : forall x y z, le x y = true -> le y z = true -> le x z = true.

  (* максимальный элемент: всё, что лежит не ниже m, лежит и не выше m *)
  Theorem finite_zorn_general : forall l : list A, l <> nil ->
    exists m, In m l /\ forall n, In n l -> le m n = true -> le n m = true.
  Proof.
    induction l as [| x xs IH]; intro Hne.
    - contradiction.
    - destruct xs as [| y ys].
      + exists x. split; [left; reflexivity |].
        intros n [Hn | []] H. subst n. exact H.
      + assert (Hne' : y :: ys <> nil) by discriminate.
        destruct (IH Hne') as [m [Hm Hmax]].
        destruct (le m x) eqn:Hmx.
        * destruct (le x m) eqn:Hxm.
          -- exists m. split; [right; exact Hm |].
             intros n [Hn | Hn] H.
             ++ subst n. exact Hxm.
             ++ apply Hmax; assumption.
          -- exists x. split; [left; reflexivity |].
             intros n [Hn | Hn] H.
             ++ subst n. exact H.
             ++ assert (Hmn : le m n = true) by (apply le_trans with x; assumption).
                apply le_trans with m; [apply Hmax; assumption | exact Hmx].
        * exists m. split; [right; exact Hm |].
          intros n [Hn | Hn] H.
          -- subst n. rewrite Hmx in H. discriminate.
          -- apply Hmax; assumption.
  Qed.
End FiniteZorn.
```

Нынешняя `finite_zorn` получается из неё при `le := Nat.leb` (`Check.v`: `finite_zorn_nat_from_general`). С общей
теоремой слова главы верны без правки; в сноску 2 — её имя и формулу.

**(б) Поправить слова** (если формализацию не трогать):

> Из той же конечности следует и простейший случай «конечной леммы Цорна»: в непустом списке натуральных чисел
> есть наибольший элемент — просто максимум списка, без всякого выбора.[^2]

## Расхождение 6. L4 и выбор: граница проходит по способу применения, а не по аксиоме (стр. 8–9, 99–100, 102)

**Было:**

> (7–9) Глава 10.3 локализовала выбор: он не нужен ни для предпорядка вложений, ни для Шрёдера–Бернштейна, ни для
> Кантора — но появляется в переходе сюръекция${}\to{}$инъекция и в требовании линейности кардинальной шкалы.
>
> (99–100) Поэтому результаты 10.3 (Шрёдер–Бернштейн, антисимметрия) используют L4, но *не* выбор: L4 обращает
> *единственное*, а выбор отбирал бы по слоям.
>
> (102) (в 10.3 он применялся через `L4_definite`)

**Проверка.**

1. Цена. `Schroeder_Bernstein` (`src/SchroederBernstein_ERR.v:357`) и `cardinal_antisym`
   (`src/settheory/CardinalityWithoutChoice.v:98`): `Classical_Prop.classic`, `ToS_Axioms.L4_witness`. Слова
   «используют L4» верны.
2. Как L4 применён. В доказательстве два применения: `L4_definite` — частичные обратные `f_inv`, `g_inv`
   (`SchroederBernstein_ERR.v:80`, `:84`), свидетель единствен по инъективности; и `L3_informative` — разбор
   случаев в определении `h` и в доказательствах (`:274`, `:287–288`, `:328–344`). `L3_informative`
   (`ToS_Axioms.v:119`) вызывает `L4_witness` напрямую (`:126`), не через `L4_definite`; свидетель там — булево
   значение, оно тоже единственно. Проверено компилятором (`CheckSB.v`): доказательство из
   `SchroederBernstein_ERR.v`, взятое дословно, проходит, если вместо аксиомы дать посылку раздела

   ```coq
   Hypothesis DD : forall (T : Type) (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.
   ```

   и вывести из неё обе опоры. Ответ `Print Assumptions` для полученной теоремы: `classic : forall P : Prop, P \/ ~ P`
   — и только. Слова «L4 обращает единственное» о доказательстве главы 10.3 верны.
3. Что даёт объявленная аксиома. `L4_witness` записана без условия единственности. Из неё выводится (`CheckL4.v`,
   `CheckDC.v`; ответ компилятора в трёх случаях — одна `ToS_Axioms.L4_witness`):

   ```coq
   Theorem surjection_gives_injection_from_L4 : forall A B : Type, surjects A B -> injects B A.
   Theorem functional_choice_from_L4_axiom :
     forall (I X : Type) (R : I -> X -> Prop),
       (forall i, exists x, R i x) -> exists f : I -> X, forall i, R i (f i).
   Theorem dependent_choice_from_L4_axiom :
     forall (A : Type) (R : A -> A -> Prop), (forall x, exists y, R x y) ->
     forall x0, exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n)).
   ```

   Первая — тот самый переход «сюръекция → инъекция», отбор прообраза в каждом слое. Шапка
   `CardinalityWithoutChoice.v:19–20` («With only L4_witness one inverts a BIJECTION (unique preimages), not an
   arbitrary surjection») компилятором не подтверждается.

**В чём расхождение.** Глава проводит границу так: L4 обращает единственное, выбор отбирает по слоям. По
компилятору объявленная аксиома делает и то, и другое; единственностью ограничено её *применение* в
доказательствах главы 10.3, и названо это применение не полностью (кроме `L4_definite` есть `L3_informative`).

**(а) Довести формализацию.** Возможно — сделать ограничение единственностью видимым компилятору: в
`SchroederBernstein_ERR.v` доказать теорему при посылке `DD` (текст выше), определив внутри раздела

```coq
Definition L4_definite (T : Type) (P : T -> Prop) (H : exists! x, P x) : {x : T | P x} := @DD T P H.
Arguments L4_definite {T} P H.

Lemma L3_informative : forall P : Prop, {P} + {~P}.
Proof.
  intro P.
  assert (Hex : exists! b : bool, if b then P else ~P).
  { destruct (classic P) as [HP | HnP].
    - exists true. split; [exact HP |]. intros [|] Hb; [reflexivity | contradiction].
    - exists false. split; [exact HnP |]. intros [|] Hb; [contradiction | reflexivity]. }
  destruct (@DD bool _ Hex) as [b Hb].
  destruct b; [left | right]; exact Hb.
Defined.
```

Остальной текст файла не меняется (`CheckSB.v` — полный собранный вариант). Прежняя формулировка получается
подстановкой `ToS_Axioms.L4_definite` (в `CheckSB.v` — `Schroeder_Bernstein_from_axiom`; допущения: `classic`,
`L4_witness`), так что `cardinal_antisym` и другие потребители не затрагиваются, если новой теореме дать новое
имя. Тогда слова «L4 обращает единственное» станут утверждением с машинной опорой: теорема Шрёдера–Бернштейна
следует из `classic` и извлечения *единственного* свидетеля. Переход «сюръекция → инъекция» из такой посылки не
получается тем же способом — там свидетель не единствен.

**(б) Поправить слова** (нужно в обоих случаях):

> (7–9) Глава 10.3 локализовала выбор: он не нужен ни для предпорядка вложений, ни для Шрёдера–Бернштейна, ни для
> Кантора — но появляется в переходе сюръекция${}\to{}$инъекция, где свидетеля приходится извлекать в каждом слое
> без единственности, и в требовании линейности кардинальной шкалы.
>
> (99–103) Поэтому результаты 10.3 (Шрёдер–Бернштейн, антисимметрия) используют L4, но *не* выбор: в их
> доказательствах L4 применён только там, где свидетель *единствен*, — к прообразу при инъекции (`L4_definite`)
> и к ответу «да или нет» при разборе случаев (`L3_informative`); выбор отбирал бы по слоям, где свидетелей
> много. Сама аксиома `L4_witness` записана без условия единственности, и применённая к каждому слою дала бы и
> такой отбор (сноска 7): граница между L4 и выбором проходит по способу применения. При этом L4 — не
> 0-аксиомная конструкция, а отдельный свидетельский принцип уровня L4; его цена учитывается *отдельно* от
> выбора.

Как назвать это соотношение — решает автор; проверка показывает только, что аксиома в объявленном виде шире своего
применения в главе 10.3.

## Сомнительные места (не расхождения)

- **Сноска 1, `AC_is_L5` «(функция выбора — голова)».** Формулировка — `exists f, forall i, In (f i) (family i)`;
  что `f` есть голова, видно из доказательства. Явно голова названа в `finite_choice` и
  `P4_eliminates_AC_finite` (через `finite_choice_fn`).
- **Стр. 41–43, «постадийная версия с конечным фронтом $N$».** В `P4_eliminates_AC_finite` число `N` входит только
  в условия `i < N`; функция выбора та же, что в неограниченной версии, и определена на всех индексах. Теорема
  выводится из `finite_choice` одной строкой. Различие двух версий — в чтении; глава так и говорит.
- **Стр. 40 и 42, «P4-совместима».** В `P4_Eliminates_AC.v` связи с `P4_stage_bounded` нет; совместимость
  выбора-правила со стадийной ограниченностью доказана только в пробном файле (расхождение 2, пункт «а»).
- **Стр. 108, «длина сохраняется при конечном разбиении».** `finite_decomposition_preserves_length` — равенство
  `length (l1 ++ l2) = length l1 + length l2` (лемма стандартной библиотеки `app_length`): длина при склейке двух
  списков. Сноска 8 пересказывает её точно. О разбиении списка по разрешимому признаку леммы нет; она доказуема
  без допущений (`Check.v`): `decidable_partition_length : length (filter f l) + length (filter (fun x => negb (f
  x)) l) = length l` и `decidable_partition_cover`.
- **Сноска 4, `ac_implies_completed`.** Пересказ верен. Посылка `AC_on_nat` доказана в том же файле, поэтому
  заключение верно и без неё; «завершённый граф» в формулировке — график всюду определённой функции. Глава 4.1
  это оговаривает, здесь оговорка появится с правкой расхождения 1.
- **Сноска 7, «шапка прямо это проговаривает».** Слова «This is NOT the Axiom of Choice» стоят в строке 72 — в
  комментарии раздела L4, а не в шапке файла (строки 1–29).
- **Сноска 7, «не зависимый выбор».** Верно о записи аксиомы. По силе зависимый выбор из `L4_witness` выводится
  (`CheckDC.v`).
- **Стр. 111, 128, сноска 7, «сила сопоставима».** Доказана одна сторона: из формулировки L4 следует
  функциональный выбор по произвольному семейству (`l4_statement_gives_functional_choice`). Обратного утверждения
  в формализации нет.
- **Стр. 13, 60–61, 131–132, слова о полной ZFC-AC.** Теорем о ней нет; глава говорит это сама («формальный файл
  фиксирует именно нат-индексированный диагноз»). На стр. 131–132 («которую P4 как раз запрещает») этой оговорки
  нет.
- **Стр. 12, «(или из приближения процесса)».** `process_choice` (`P4_Eliminates_AC.v:80`) — то же определение,
  что `finite_choice_fn`, под другим именем; `process_choice_valid` повторяет `finite_choice`.
- **Таблица разбора, пометки «(L5)», «(L4)», «(L1${}+{}$P4)».** Это имена слоёв, а не цена: все названные в
  строках объявления — без допущений.

## Вне главы: файлы формализации

Для сведения (в главе эти строки не цитируются, кроме отмеченных выше):

- `settheory/CardinalityWithoutChoice.v:17–20` — «the converse bridge surjects(A,B) => injects(B,A) … is EXACTLY
  the Axiom of Choice … With only L4_witness one inverts a BIJECTION … not an arbitrary surjection». Второе
  компилятором не подтверждается (расхождение 6, пункт 3). О первом: утверждение «если $A$ отображается на $B$,
  то $B$ вкладывается в $A$» в литературе называют принципом разбиения; он следует из аксиомы выбора, а
  равносильность ей, насколько известно, остаётся открытым вопросом; аксиоме выбора равносильно существование
  правого обратного у всякой сюръекции. Не проверялось; относится к главам 10.3 и 10.6.
- `SchroederBernstein_ERR.v:33` — «AXIOMS: classic + L4_definite (CDD)»: по компилятору — `classic` и
  `L4_witness`; второе применение (`L3_informative`) в шапке не названо.
- `settheory/ChoicePriceMap.v`: строка `RFiniteChoice` (цена `PZero`) не имеет названной опорной теоремы в
  перечне `:81–109`; естественные опоры (`finite_choice`, `P4_eliminates_AC_finite`, `finite_choice_works`) —
  Closed, цена с ними согласуется. Строка `RFunctionalChoice` (цена `PL4`): названная лемма
  `l4_statement_gives_functional_choice` по компилятору Closed (L4 — посылкой); безусловная теорема о
  функциональном выборе от аксиомы имеет допущение `L4_witness` (`CheckL4.v`) — цена относится к ней. Ссылка
  «P4ProhibitsAC.v:28–31» (`:190`) устарела: определение стоит в строках 43–46.
- `P4_Eliminates_AC.v:71` — `L5_choice_deterministic : L5_choose l d = L5_choose l d` (равенство выражения самому
  себе; в главе не упоминается); `:152–154` — «every subset is measurable»: понятия меры в файле нет;
  `:194–195` — «above» о теореме, стоящей ниже.
- `P4ProhibitionSynthesis.v:12–16` — «Prohibition ⇒ Reinterpretation», «Reinterpretation ⇏ Prohibition»: это слова
  шапки; теоремами файла они не выражены (расхождение 3).
- `ToS_Axioms.v:27` — «3 Qed»: в файле 2 `Qed` и 1 `Defined`.

## Дополнительные проверки

- Все 15 утверждений `P4_Eliminates_AC.v`, все 12 — `P4ProhibitsAC.v`, все 9 — `P4CompletedInfinity.v`, все 6 —
  `P4ProhibitionSynthesis.v`: Closed under the global context. Шапки файлов называют те же числа `Qed`.
- Исходники этих четырёх файлов, `ToS_Axioms.v` и `ChoicePriceMap.v` совпадают с собранной копией (SHA-1).
- `AC_on_nat` объявлена дважды с одной формулировкой (`P4ProhibitsAC.v:43`, `ChoicePriceMap.v:192`) и дважды
  доказана (`AC_on_nat_as_rule`, `ac_on_nat_free`); `L5_choose` определена дважды одинаково
  (`P4_Eliminates_AC.v:25`, `P4ProhibitsAC.v:141`); имя `finite_choice` в двух файлах означает разное — лемму
  (`P4_Eliminates_AC.v:47`) и функцию с фронтом (`P4ProhibitsAC.v:168`). Сноска 1 называет файл, путаницы нет.
- Комментарий к `P4_eliminates_AC` (сноска 3) — строки 191–195 — пересказан точно.
- Формулы главы для `AC_on_nat` (стр. 51–52), `L4_witness` (стр. 95–96, сноска 7), `finite_zorn` (сноска 2)
  совпадают с утверждениями в `.v`.
