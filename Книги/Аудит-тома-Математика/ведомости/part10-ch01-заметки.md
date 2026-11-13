# Глава X.1 «Множество как Система, а не объект» — заметки к ведомости (12.11.2026)

Ведомость: `part10-ch01.json` — 51 ручная запись, автоматических нет; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты: ok — 44, mismatch-statement — 5, mismatch-price — 2.

Семь записей с расхождением относятся к четырём местам (расхождения 1–4): две записи — об одной отсылке к
`P4ProhibitsImpredicative.v`, две — о Фундировании и циклах, две — об одной формуле «без выбора».

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part10/ch01/`: `Check.v` (13 утверждений), `Check2.v`
(4 утверждения) — оба собираются, все ответы `Print Assumptions` — Closed under the global context;
`CheckUniverse.v`, `CheckUniverse2.v`, `CheckUniverse3.v` — по одному определению, которое компилятор отклоняет
(текст отказа приведён ниже, в сомнительном месте 1; эти три файла не собираются намеренно). В `src` и в
собранной копии ничего не менялось.

Числа главы: счёта `Qed`, файлов и аксиом страница не приводит. Действительный счёт названных файлов:
`TheoryOfSystems_Core_ERR.v` — 36 Qed, `foundation/P4ProhibitsImpredicative.v` — 7, `foundation/TransfiniteInductionLevel.v` — 6;
`Axiom`, `Parameter`, `Admitted` в них нет. Все девять имён главы найдены, блоков кода в главе нет.

## Что проверить не удалось

- Тезисы о замещении выбора правилом L5 и бесконечности схемой P4 (стр. 25, 171–174) — предмет глав 10.4 и
  10.5; здесь не сверялись.
- У теорем глав 10.2 и 10.3, названных в обзоре (стр. 46–47, 168–171), сверена цена и общность утверждения
  (`Q_countable`, `Q_bijection`, `Schroeder_Bernstein`, `cardinal_antisym`, `cantor_no_surjection`,
  `no_maximal_cardinality`); полная сверка формулировок — в аудите этих глав.
- Что условие о домене в `russell_paradox_blocked` и `cantor_paradox_blocked_v1` не используется, установлено
  чтением доказательств (гипотеза `Hdom` вводится и далее не упоминается) и пробной теоремой
  `criterion_label_never_own_level`, где то же заключение получено без этого условия.
- Отказ компилятора принять `System L2` доменом критерия установлен по тексту ошибки; в `Check.v` те же два
  определения стоят под `Fail`.
- Страница «Формализация», на которую ссылается стр. 153, открывалась только на строке 101 (лемма
  `l4_statement_gives_functional_choice`).
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. `russell_paradox_blocked` доказана для одного уровня, сноска говорит «ни на каком уровне» (стр. 185)

**Было:**

> [^3]: `russell_paradox_blocked` (`TheoryOfSystems_Core_ERR.v`): расселова совокупность не может быть построена
> ни на каком уровне.

**Проверка.** `russell_paradox_blocked` (`src/TheoryOfSystems_Core_ERR.v:248`):

```coq
Theorem russell_paradox_blocked :
  ~ exists (C : Criterion L2),
    crit_domain L2 C = System L2 /\
    crit_level_witness L2 C = L2.
Proof.
  intros [C [Hdom Hlev]].
  pose proof (crit_level_valid L2 C) as Hvalid.
  rewrite Hlev in Hvalid.
  apply (level_lt_irrefl L2). exact Hvalid.
Qed.
```

`Print Assumptions`: Closed under the global context. Утверждение — для уровня `L2`. Расселова условия
$x\notin x$ в нём нет. Условие о домене (`Hdom`) в доказательстве не используется. То же утверждение для
произвольного уровня есть под другим именем — `cantor_paradox_blocked_v1` (`Core_ERR.v:1255`, `forall L, …`), а
`cantor_no_system_of_all_L2_systems` (`Core_ERR.v:1300`) совпадает с `russell_paradox_blocked` дословно.
Невозможность самой расселовой совокупности на любом носителе в формализации доказана в другом файле —
`russell_no_universal_set` (`src/cs/RussellViaLawvere.v:54`):
`forall (A : Type) (mem : A -> A -> Prop), ~ exists R : A, forall x, mem R x <-> ~ mem x x` — Closed under the
global context.

**В чём расхождение.** Названная теорема говорит об одном уровне и о метке уровня критерия; слова «расселова
совокупность» и «ни на каком уровне» шире её утверждения.

**(а) Довести формализацию.** Возможно, без допущений. Набросок проверен (`Check.v`), все три теоремы — Closed
under the global context:

```coq
(* заключение без условия о домене и для любого уровня *)
Theorem criterion_label_never_own_level :
  forall (L : Level) (C : Criterion L), crit_level_witness L C <> L.
Proof.
  intros L C Heq.
  pose proof (crit_level_valid L C) as Hv.
  rewrite Heq in Hv.
  exact (level_lt_irrefl L Hv).
Qed.

(* расселова совокупность: любой носитель, любое отношение *)
Theorem russell_collection_impossible :
  forall (A : Type) (mem : A -> A -> Prop),
    ~ exists r : A, forall x : A, mem x r <-> ~ mem x x.
Proof.
  intros A mem [r Hr].
  destruct (Hr r) as [H1 H2].
  assert (Hn : ~ mem r r) by (intro Hm; exact (H1 Hm Hm)).
  exact (Hn (H2 Hn)).
Qed.

(* «ни на каком уровне» *)
Theorem russell_blocked_every_level :
  forall (L : Level) (mem : System L -> System L -> Prop),
    ~ exists R : System L, forall X : System L, mem X R <-> ~ mem X X.
Proof.
  intros L mem. exact (russell_collection_impossible (System L) mem).
Qed.
```

С теоремой `russell_blocked_every_level` слова сноски верны, если назвать в ней это имя. Чтобы не трогать
головной файл `TheoryOfSystems_Core_ERR.v` (от него зависят десятки файлов), теоремы можно поместить в
`foundation/TransfiniteInductionLevel.v`, который его подключает. В доказательствах других файлов
`russell_paradox_blocked` не применяется (упоминается только в комментариях), так что обобщить её саму до
`forall L` тоже можно без последствий для сборки.

**(б) Поправить слова** (если формализацию не трогать):

> [^3]: `russell_paradox_blocked` (`TheoryOfSystems_Core_ERR.v`): на уровне $L_2$ нет критерия, у которого домен —
> системы уровня $L_2$, а уровень домена — сам $L_2$; для произвольного уровня то же утверждение —
> `cantor_paradox_blocked_v1`. Невозможность самой расселовой совокупности при любом носителе и любом отношении
> принадлежности — `russell_no_universal_set` (`cs/RussellViaLawvere.v`). Всё — без аксиом.

## Расхождение 2. «$R$ требует завершённой тотальности, P4 её не допускает» — в файле комментарий, не теорема (стр. 185, 186)

**Было:**

> [^3]: … См. также `P4ProhibitsImpredicative.v`: импредикативное определение $R=\{x \mid x\notin x\}$ требует
> завершённой тотальности «всех множеств», которую P4 не допускает.
>
> [^4]: `P4ProhibitsImpredicative.v`: $R$ требует completed totality; P1${}+{}$P4 её исключают.

**Проверка.** В `src/foundation/P4ProhibitsImpredicative.v` семь лемм, все — Closed under the global context:

- `P1_blocks_russell` (:56): `(forall x, ~ member x x) -> forall x, russell_criterion member x`, где
  `russell_criterion member x := ~ member x x`, — заключение повторяет посылку;
- `russell_contradiction_without_P1` (:69): `forall (member : nat -> nat -> Prop) (r : nat),
  (forall x, member x r <-> ~ member x x) -> False` — диагональ Рассела для отношения на `nat`;
- `nat_is_inductive` (:92), `nat_staged_bounded` (:102), `nat_eventually_actual` (:109) — о `nat` и его стадиях;
- `P4_dissolves_russell` (:124) и `p4_impredicative_synthesis` (:144) — конъюнкции перечисленных фактов.

В `P4_dissolves_russell` член с комментарием «Russell requires completed totality» — та же диагональ Рассела;
о тотальности в нём ничего не сказано. P4 входит в файл одним утверждением `P4_stage_bounded nat_staged_actual`,
с расселовой совокупностью не связанным. Определение `NatTotality` (:33,
`forall P : nat -> Prop, exists n : nat, True`) истинно при любом содержании, и комментарий в файле это
оговаривает; оно и `impredicative_prop` (:41) ни в одной лемме не используются. «P4 не допускает завершённой
тотальности» доказано в соседнем файле: `completed_inf_contradicts_P4` (`foundation/P4CompletedInfinity.v:64`) —
при посылке `bridge` (каждый член совокупности актуален на стадии 0).

**В чём расхождение.** Слова «$R$ требует завершённой тотальности» и «P1 и P4 её исключают» стоят в
комментариях файла; среди его теорем таких утверждений нет.

**(а) Довести формализацию.** Возможно, без допущений. Содержание простыми словами: собиратель расселова условия
по области $T$ сам в $T$ не лежит; по каждой конечной стадии такой собиратель есть и появляется на следующей
стадии; противоречие возникает только тогда, когда область включает сам собиратель, то есть завершена. Набросок
проверен (`Check.v`), все четыре теоремы — Closed under the global context:

```coq
Theorem russell_collector_escapes :
  forall (A : Type) (mem : A -> A -> Prop) (T : A -> Prop) (r : A),
    (forall x, T x -> (mem x r <-> ~ mem x x)) -> ~ T r.
Proof.
  intros A mem T r Hr HT.
  destruct (Hr r HT) as [H1 H2].
  assert (Hn : ~ mem r r) by (intro Hm; exact (H1 Hm Hm)).
  exact (Hn (H2 Hn)).
Qed.

Theorem russell_needs_incomplete_range :
  forall (mem : nat -> nat -> Prop) (T : nat -> Prop) (r : nat),
    (forall x, T x -> (mem x r <-> ~ mem x x)) -> ~ CompletedInfSet T.
Proof.
  intros mem T r Hr HT.
  exact (russell_collector_escapes nat mem T r Hr (HT r)).
Qed.

Theorem staged_russell_collector_exists :
  forall stage : nat,
    exists r : nat,
      (forall x, nat_staged_actual stage x -> (x < r <-> ~ x < x)) /\
      ~ nat_staged_actual stage r /\
      nat_staged_actual (S stage) r.
Proof.
  intro stage. exists (S stage).
  unfold nat_staged_actual.
  split; [ | split ].
  - intros x Hx. split.
    + intros _ Hxx. lia.
    + intros _. lia.
  - lia.
  - lia.
Qed.

Theorem russell_requires_completed_totality :
  P4_stage_bounded nat_staged_actual /\
  (forall stage : nat,
     exists r : nat,
       (forall x, nat_staged_actual stage x -> (x < r <-> ~ x < x)) /\
       ~ nat_staged_actual stage r) /\
  (forall (mem : nat -> nat -> Prop) (T : nat -> Prop) (r : nat),
     (forall x, T x -> (mem x r <-> ~ mem x x)) -> ~ CompletedInfSet T).
Proof.
  split; [ exact nat_staged_bounded | split ].
  - intro stage.
    destruct (staged_russell_collector_exists stage) as [r [H1 [H2 _]]].
    exists r. split; assumption.
  - exact russell_needs_incomplete_range.
Qed.
```

После добавления этих теорем в `P4ProhibitsImpredicative.v` (счёт файла станет 11 Qed) первая половина сносок
(«$R$ требует завершённой тотальности») получает утверждение; вторая («P4 её не допускает») опирается на
`completed_inf_contradicts_P4` с его посылкой `bridge`. Пример со стадиями построен для одного отношения
($x<y$ на `nat`); первая и третья теоремы — для любого отношения.

**(б) Поправить слова** (если формализацию не трогать):

> [^3]: … См. также `P4ProhibitsImpredicative.v`: там доказано, что расселова совокупность противоречива при
> любом отношении принадлежности на `nat` (`russell_contradiction_without_P1`) и что стадийная актуальность
> `nat` ограничена на каждой стадии (`nat_staged_bounded`). Что определение $R=\{x \mid x\notin x\}$ требует
> завершённой тотальности «всех множеств», которую P4 не допускает, — чтение этих фактов; отдельной теоремой
> оно не записано.
>
> [^4]: `P4ProhibitsImpredicative.v`: противоречивость расселовой совокупности
> (`russell_contradiction_without_P1`) и стадийная ограниченность `nat` (`nat_staged_bounded`). Вывод «$R$
> требует завершённой тотальности; P1${}+{}$P4 её исключают» — чтение, не теорема файла.

## Расхождение 3. Фундирование приписано иррефлексивности; отсутствие циклов — одной иррефлексивности (стр. 143–144, 146)

**Было:**

> (142–144) **Корректность.** Система корректна $\Longleftrightarrow$ её критерий-домен строго ниже (P2);
> иррефлексивность $\ll$ гарантирует отсутствие $\in$-циклов *по построению*.
>
> (146) **Что даёт.** Фундирование $\to$ теорема (`level_lt_irrefl`);

**Проверка.** `level_lt_irrefl` (`src/TheoryOfSystems_Core_ERR.v:96`): `forall l, ~ (l << l)` — запрет петли.
В `src/foundation/MetaPairStrength.v` (17 Qed, все названные ниже — Closed under the global context) различие
доказано явно:

- `order_no_mediated_cycle` (:70): циклов нет у строгого порядка, то есть при иррефлексивности *и*
  транзитивности (`strict_order`, :41);
- `order_does_not_give_anti_regress` (:96): существует строгий порядок с бесконечным спуском — $(\mathbb{Z},<)$;
  иррефлексивность и транзитивность фундированности не дают;
- `tos_hierarchy_models_meta_pair` (:142): для порядка уровней — нет петли, асимметрия, нет циклов любой длины
  (`forall L, ~ clos_trans Level level_lt L L`), нет бесконечного спуска;
- `no_infinite_level_regress` (:137): `forall f : nat -> Level, ~ (forall n, level_lt (f (S n)) (f n))`.

Фундированность порядка уровней — `level_lt_wf : well_founded level_lt` (`foundation/TransfiniteInductionLevel.v:32`;
то же имя и утверждение — `MetaPairStrength.v:128`). Текст главы на стр. 83–88 это различие оговаривает
(«частично несёт», «не буквально совпадают»); итоговые строки 143–146 оговорку опускают.

**В чём расхождение.** `level_lt_irrefl` запрещает только $l\ll l$. Отсутствие циклов требует ещё
транзитивности, а аксиоме Фундирования соответствует фундированность порядка; оба утверждения в формализации
доказаны, но под другими именами. Кроме того, все эти теоремы — о порядке уровней $\ll$; для отношения
`element_at` утверждений о циклах нет (оно связывает систему с элементами домена её критерия, а не с системами).

**(а) Довести формализацию.** Доводить нечего: нужные теоремы есть (`level_lt_wf`, `no_infinite_level_regress`,
`tos_hierarchy_models_meta_pair`). По желанию можно добавить форму, ближайшую к самой аксиоме Фундирования, — «в
непустой совокупности уровней не у каждого члена есть член строго ниже». Набросок проверен (`Check.v`), Closed
under the global context:

```coq
Theorem level_foundation_form :
  forall P : Level -> Prop,
    (exists l, P l) ->
    ~ (forall l, P l -> exists l', P l' /\ l' << l).
Proof.
  intros P [l0 Hl0] Hno.
  revert Hl0. induction l0 as [l IH] using level_strong_induction.
  intro Hl. destruct (Hno l Hl) as [l' [Hl' Hlt]].
  exact (IH l' Hlt Hl').
Qed.
```

**(б) Поправить слова:**

> (142–144) **Корректность.** Система корректна $\Longleftrightarrow$ её критерий-домен строго ниже (P2);
> иррефлексивность и транзитивность $\ll$ исключают циклы по уровням *по построению*.
>
> (146) **Что даёт.** Фундирование $\to$ теорема (`level_lt_wf`: порядок уровней фундирован; отсюда и
> иррефлексивность, `level_lt_irrefl`);

## Расхождение 4. «Без выбора» о теореме Шрёдера–Бернштейна (стр. 46–47, 170–171)

**Было:**

> (46–47) сравнение мощностей без выбора (10.3)
>
> (170–171) Глава 10.3: сравнение мощностей без выбора — Шрёдер–Бернштейн и общая теорема Кантора.

**Проверка.** `Schroeder_Bernstein` (`src/SchroederBernstein_ERR.v:357`) и `cardinal_antisym`
(`src/settheory/CardinalityWithoutChoice.v:98`), `Print Assumptions` у обеих:

```
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

Из утверждения `L4_witness` выбор над любым семейством выводится: `l4_statement_gives_functional_choice`
(`src/settheory/ChoicePriceMap.v:164`, Closed under the global context) — об этом говорит и сама глава на
стр. 153. Шапка `ChoicePriceMap.v` (запись от 17.10.2026) прежний тезис «ничто в Части X не использует выбор»
снимает именно для Шрёдера–Бернштейна, антисимметрии мощностей и дихотомии замкнутых множеств. Вторая половина
фразы верна: `cantor_no_surjection` (`settheory/CantorTheoremGeneral.v:55`, для произвольного типа `X`),
`no_maximal_cardinality` (`CardinalityWithoutChoice.v:108`), `injects_refl`, `injects_trans` — Closed under the
global context. Глава 10.3 в своём тексте цену Шрёдера–Бернштейна называет (стр. 68–70 той главы).

**В чём расхождение.** Теорема Шрёдера–Бернштейна в формализации опирается на `L4_witness`, из утверждения
которого выбор над любым семейством выводится; обзорные фразы главы 10.1 относят слова «без выбора» и к ней.

**(а) Довести формализацию.** В рамках этой главы — нечего; вопрос принадлежит главе 10.3. Можно ли получить
теорему на одном `classic`, здесь не проверялось.

**(б) Поправить слова:**

> (45–48) … счётность и несчётность как правила о процессах (10.2), сравнение мощностей (10.3), двойственная
> судьба аксиомы выбора — запрет и переинтерпретация (10.4), …
>
> (170–171) Глава 10.3: сравнение мощностей — теорема Шрёдера–Бернштейна на L3 и L4 и общая теорема Кантора без
> допущений.

Те же слова стоят в названии главы 10.3; решение о названии — за аудитом той главы.

## Сомнительные места (расхождениями не записаны)

**1. Что доказывают теоремы о Расселе и Канторе и что на деле отклоняет компилятор (стр. 91–94, 117–120, 147, 185, 188).**
`russell_paradox_blocked`, `cantor_paradox_blocked_v1`, `cantor_no_system_of_all_L2_systems` и
`no_self_level_elements` (`Core_ERR.v:248, 1255, 1300, 1271`) имеют посылку из двух условий: домен критерия равен
`System L` и метка уровня домена равна `L`. Во всех четырёх доказательствах используется только второе условие.
Содержание теорем — «метка `crit_level_witness` критерия уровня `L` не равна `L`» (пробная
`criterion_label_never_own_level`), что прямо следует из поля записи `crit_level_valid` и иррефлексивности.
Слова главы («критерий должен был бы пробегать по своему же уровню», «он должен быть строго ниже») это содержание
передают верно, поэтому записи стоят с вердиктом ok. Два обстоятельства стоит знать:

- метка уровня домена с типом домена не связана: домен `nat` принимается и с меткой `L1`, и с меткой `L2`
  (`nat_crit_label_L1`, `nat_crit_label_L2` в `Check.v`);
- критерий с доменом `System L2` компилятор отклоняет при любой метке, в том числе на уровне выше
  (`CheckUniverse.v`: `Criterion L2` с меткой `L1`; `CheckUniverse2.v`: `Criterion L3` с меткой `L2`). Текст отказа
  в обоих случаях один:

  ```
  The term "System L2" has type "Type@{max(Set+1,Criterion.u0+1)}"
  while it is expected to have type "Type@{Criterion.u0}"
  (universe inconsistency: Cannot enforce Criterion.u0 < Criterion.u0 because
  Criterion.u0 = Criterion.u0).
  ```

  То есть в нынешней записи система не может иметь элементами системы никакого уровня — ни своего, ни нижнего;
  комментарий в `Core_ERR.v:364–368` это оговаривает («We use indices as a practical workaround»). Запрет
  «своего уровня» и допуск «нижнего уровня», о которых говорит глава, в формализации различаются только меткой.

Слова стр. 117–118 «и его диагональный спутник» теоремой `cantor_paradox_blocked_v1` не покрыты: диагонали в ней
нет. Диагональ на любом уровне получается из общей теоремы Кантора одной строкой (`Check2.v`, Closed under the
global context):

```coq
Theorem cantor_diagonal_every_level :
  forall (L : Level) (f : System L -> (System L -> bool)),
    ~ @surjective (System L) f.
Proof.
  intros L f. exact (@cantor_no_surjection (System L) f).
Qed.
```

**2. `element_at` не требует выполнения критерия; «работу Выделения выполняют критерий + P2» (стр. 23, 58–60, 138, 146–147).**
`element_at` (`Core_ERR.v:583`) определено для `StructuredSystem` (система с назначением позиций), а не для
`System`, и означает «элемент занимает некоторую позицию». Предикат критерия `crit_predicate` в определение не
входит. Пробный пример (`Check2.v`, `element_at_ignores_criterion`, Closed under the global context): в системе
над критерием «$n>5$» (`example_nat_system`) позицию 0 занимает число 0; `element_at` выполнено, критерий — нет.
Выполнение критерия — отдельное условие: поле `wf_L4` записи `ERR_WellFormed` (`Roles.v:290–297`) и суждение
`HasElem` (`Judgments.v:158`). Мост доказывается в одну строку (`Check2.v`, Closed under the global context):

```coq
Lemma element_at_satisfies_criterion :
  forall (L : Level) (S : StructuredSystem L),
    ERR_WellFormed L S ->
    forall e, element_at S e ->
      crit_predicate L (sys_criterion L (ss_base L S)) e.
Proof.
  intros L S Hwf e [p Hp].
  exact (wf_L4 L S Hwf p e Hp).
Qed.
```

Теоремы о Выделении в формализации нет; слова стр. 138 и 146–147 — чтение. При этом реестр
`foundation/ZFCAxiomLedger.v` относит Выделение к P4 (`tos_verdict Separation = ReplacedBy P4`,
`verdict_separation`, :104, со ссылкой на `P4ProhibitsImpredicative`), а глава — к критерию и P2. Реестр глава
не называет; расхождение между страницей и реестром стоит снять при аудите главы, где реестр назван.

**3. `P1_no_self_membership` — об уровнях, не о принадлежности (стр. 80–81, 184).**
Утверждение теоремы — `forall L, ~ (L << L)`, то же, что у `level_lt_irrefl` (доказательство —
`exact level_lt_irrefl`); сноска 2 приводит формулу верно. Отношение `element_at` в утверждение не входит, и
теоремы «система не занимает позицию в самой себе» в формализации нет: по типам `element_at S S` не записывается
(`CheckUniverse3.v`: выражение `fun S : StructuredSystem L2 => element_at S S` компилятор не принимает, а критерий
с доменом `StructuredSystem L2` отклоняет с тем же отказом, что в месте 1). Для записи `FunctionalSystem`, где у элемента есть уровень (`fs_element_level`), соответствующее
утверждение доказывается сразу (`Check.v`, `functional_system_no_own_level_element`:
`fs_element_level L S e <> L`, Closed under the global context); в `Core_ERR.v` есть только частный случай для
`L3` — `err_self_reference_blocked` (:1888). Имя `P1_no_self_membership` объявлено также в
`foundation/PrinciplesFromLaws.v:47`; глава называет `Core_ERR`.

**4. «Система корректна ⟺ P2» (стр. 90–91, 142).**
В Rocq P2 — поле записи `Criterion` (`crit_level_valid`), и `P2_always_holds` (`Core_ERR.v:174`) говорит, что оно
выполнено у всякого критерия. Отдельного свойства «корректна», равносильного P2, нет: равносильность на
стр. 142 — определение, а не теорема. Имя «well-formedness» в формализации занято другим условием:
`ERR_WellFormed` (`Roles.v:290`) — единственность позиции и выполнение критерия занявшим её элементом; об уровнях
в нём ничего нет.

**5. «Беспарадоксальна по построению» (стр. 44, 75, 97, 164, 177).**
За словами стоят три теоремы о невозможности трёх конкретных конструкций. Общего утверждения «в теории не
выводится противоречие» в формализации нет, и средствами самой системы оно недоказуемо. Глава такой теоремы не
заявляет; слово «беспарадоксальна» стоит читать как «названные три построения не образуются».

**6. «P1 и P4 вместе» (стр. 107–109, 127–130).**
Три теоремы главы доказаны из одного порядка уровней (`level_depth`); P4 в их доказательствах не участвует.
Теоремы, соединяющей P1 и P4 в разборе парадоксов, нет (см. расхождение 2, где такая связь предложена).

**7. Бурали-Форти (стр. 111–115, 187).**
Тип `Level` (`L1 | LS`) — нумерация уровней натуральными числами с единицы, и `no_universal_level` по
содержанию — «наибольшего уровня нет». Об ординалах утверждения нет; глава говорит «соответствующий приём», что
верно. В `TransfiniteInductionLevel.v` шапка называет файл дополнением к `foundation/TransfiniteInduction.v`
(ординальные обозначения) — тот файл в этой главе не назван и не сверялся.

**8. Строка «Elements» таблицы (стр. 140).**
«На каждой стадии — конечные данные» — чтение. Тип `System` конечности не закрепляет: `sys_pos_bound` допускает
`Unbounded`, а `ss_assignment` — функция на всех позициях сразу. Стадийная ограниченность записана отдельным
определением `P4_stage_bounded` (`P4CompletedInfinity.v:33`) и с типом `System` не связана.

**9. Одноимённые объявления.**
`level_lt_wf` объявлена дважды с одним утверждением (`TransfiniteInductionLevel.v:32`, `MetaPairStrength.v:128`).
`P1_blocks_russell` объявлена дважды с разными утверждениями: в `P4ProhibitsImpredicative.v:56` (см. расхождение
2) и в `PrinciplesFromLaws.v:51` (`forall l, ~ (l << l)`). Глава этих имён не называет; при правке сносок их
стоит указывать вместе с файлом.
