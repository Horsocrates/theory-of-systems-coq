# Глава I.7 «Онтологическое ядро» — заметки к ведомости (13.11.2026)

Ведомость: `part01-ch07.json` — 49 ручных записей + 3 автоматических (упоминания файлов); `merge --dry` проходит без
замечаний, список «без сверки» пуст. Вердикты ручных записей: ok — 44, mismatch-statement — 4, missing-name — 1
(с автоматическими: ok — 47).

Глава называет 13 имён (9 объявлений и 4 поля записи `Distinction`) и 8 файлов. Блоков кода и чисел (`Qed`, файлов,
аксиом) на странице нет. О цене допущений глава говорит в одном месте (стр. 348–352, «не требует отдельной аксиомы») —
верно.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part01/ch07/`:

- `Check.v` — уровни, критерий на собственном уровне, запись `Distinction`;
- `CheckList.v` — переход «список → мультимножество → множество»;
- `CheckListQ.v` — `in_list` слоя `src/settheory/` как support списка;
- `CheckBarandes.v` — граф → преобразование Кэли → унистохастическая матрица → неделимость двухшагового перехода;
- `CheckGap.v` — что означает `indivisible` в `ConnectionClosesGap.v`;
- `CheckProcess.v` — монотонность модели sharpness/coherence и теорема, оставленная в файле под `Abort`;
- `CheckPA.v` (вывод — `CheckPA.out`) — `Print Assumptions` всех 169 утверждений девяти файлов.

Все собираются; каждое новое утверждение — Closed under the global context. В `src` и в собранной копии ничего не
менялось.

## Что проверить не удалось

- Отсылки к другим главам и частям (Глава 3 — стр. 90; Глава 4 — стр. 297, 539; Глава 6 — стр. 221, 309, 327, 352,
  358; Части II и IV — стр. 302–306) не сверялись: их утверждения проверяются в ведомостях этих глав. Попутно
  проверено: Глава 3 (её стр. 429–454) сама оговаривает двойной статус $L3$; в Главе II.2 (её стр. 263–283) переход
  «список → мультимножество → множество» изложен прозой, имён формализации при нём нет.
- «Файлы физического контура» (стр. 679) и «связанные Cayley-файлы» (сноска 1) поимённо не названы. Проверены: четыре
  файла сноски 1 (прочитаны целиком); из Cayley-файлов — `GraphUnitary.v`, `BlockCayleyUnistochastic.v`,
  `GeneralHermitianCayley.v` (снят `Print Assumptions` всех утверждений, прочитаны итоговые теоремы);
  `L1_DoublyStochastic.v`, `CayleyFourierMassBridge.v`, `CayleyGeometrySpectralBridge.v`,
  `DoublyStochasticForkBridge.v` — только шапки и перечни утверждений.
- В `foundation/L5_Indivisible.v` есть другое определение `indivisible` (для историй `nat -> list nat` и функции
  переходов); глава этот файл не называет, он не сверялся.
- Сказанное о квантовой логике (стр. 74–87: работа Биркгофа и фон Неймана, ортодополненность решётки, отказ от
  дистрибутивности) к формализации не относится и компилятором не проверялось; файлов о квантовой логике в `src` нет.
- Для множеств-предикатов общего вида (расхождение 2) представимость через список или перечисляющий процесс не
  проверялась.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. `russell_paradox_blocked` — утверждение об одном уровне `L2` (стр. 336–343)

**Было:**

> С точки зрения же $P2/L5$ та же тотальность пытается задать критерий на собственном уровне, что запрещено иерархией
> уровней: формально это разобрано в файле `TheoryOfSystems_Core_ERR.v`, где теорема `russell_paradox_blocked`
> устанавливает невозможность критерия-свидетеля на собственном уровне через иррефлексивность отношения `level_lt`.

**Проверка.** `src/TheoryOfSystems_Core_ERR.v:163`, `:248`:

```coq
Record Criterion (L : Level) : Type := mkCriterion {
  crit_domain : Type;
  crit_predicate : crit_domain -> Prop;
  crit_level_witness : Level;
  crit_level_valid : crit_level_witness << L;
}.

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

Closed under the global context. По утверждению и доказательству видно:

- уровень фиксирован — `L2` (`L2 := LS L1`, `:63`);
- первый член конъюнкции, `crit_domain L2 C = System L2`, в доказательстве не используется (`Hdom`): заключение верно
  для критерия уровня `L2` с любой областью;
- требование «свидетель строго ниже уровня» — поле записи `Criterion` (`crit_level_valid`); теорема соединяет это поле
  с леммой `level_lt_irrefl` (`:96`). Слова «через иррефлексивность» точны; запрет внесён в определение критерия;
- то же утверждение дословно стоит в файле ещё раз под именем `cantor_no_system_of_all_L2_systems` (`:1300`): в
  `Check.v` обе теоремы проходят проверку одного и того же типа.

Общая форма в формализации есть, под другими именами (все — Closed under the global context):

```coq
(* TheoryOfSystems_Core_ERR.v:1255 *)
Theorem cantor_paradox_blocked_v1 :
  forall L, ~ exists (C : Criterion L), crit_domain L C = System L /\ crit_level_witness L C = L.

(* foundation/TransfiniteInductionLevel.v:96, :109 *)
Theorem criterion_label_never_own_level :
  forall (L : Level) (C : Criterion L), crit_level_witness L C <> L.
Theorem russell_blocked_every_level :
  forall (L : Level) (mem : System L -> System L -> Prop),
    ~ exists R : System L, forall X : System L, mem X R <-> ~ mem X X.
```

Последние две добавлены в ноябре 2026 года (коммит d6453e3, аудит Части X) с пометкой в файле (`:93–95`): «This is
the content of russell_paradox_blocked (Core_ERR), there stated for L2 only and with a premise about the domain which
its proof does not use».

**В чём расхождение.** Глава говорит о невозможности «на собственном уровне» вообще и называет теорему, которая
утверждает это для одного уровня `L2`; общая форма доказана другими теоремами.

**(а) Довести формализацию.** Не требуется: общая форма уже доказана (`criterion_label_never_own_level`), и названная
главой теорема получается из неё одной строкой (`Check.v`, `russell_paradox_blocked_from_general`, Closed under the
global context). Саму `russell_paradox_blocked` менять нельзя (инвариант `CLAUDE.md`) и незачем.

**(б) Поправить слова** — назвать общую теорему:

> С точки зрения же $P2/L5$ та же тотальность пытается задать критерий на собственном уровне, что запрещено иерархией
> уровней: формально это разобрано в файле `TheoryOfSystems_Core_ERR.v`, где теорема `russell_paradox_blocked`
> устанавливает для уровня `L2` невозможность критерия-свидетеля на собственном уровне через иррефлексивность
> отношения `level_lt`; для всякого уровня то же утверждает `criterion_label_never_own_level`
> (`TransfiniteInductionLevel.v`).

По желанию автора к этой фразе можно добавить и `russell_blocked_every_level`: ни на каком уровне нет системы,
собирающей в точности те системы уровня, которые не входят в себя, — при любом отношении вхождения.

## Расхождение 2. Слой `src/settheory/` не построен поверх списков (стр. 381–388; сноска 2)

**Было:**

> **Теория множеств как надстройка.** Сказанное не отменяет теории множеств. Оно указывает её *место*: формальная
> теория множеств есть *надстройка* над более первичным уровнем списков, а не фундамент под ним. В репозитории ToS
> это отражено прямо: формализация теоретико-множественных конструкций[^2] располагается *поверх* списочного
> аппарата, как производный слой, а не как основание.

**Проверка.** В каталоге `src/settheory/` 11 файлов, 178 строк `Qed.`. Чем в них заданы множества и для чего служат
списки:

| файл | Qed | множества и их аналоги | списки |
|---|---|---|---|
| `BorelDeterminacy.v` | 19 | выигрышное множество — предикат `GameState -> Prop` | позиция игры `GameState := list nat` (`:28`) |
| `CantorBendixsonFull.v` | 35 | `PointSet := Q -> Prop` (`:36`) | `in_list` (`:519`) — множество, заданное списком; о нём три утверждения |
| `CantorTheoremGeneral.v` | 6 | предикаты `X -> bool` | нет |
| `CardinalityWithoutChoice.v` | 21 | типы и отображения: `injects`, `surjects`, `bijects` (`:43–49`) | нет |
| `ChoicePriceMap.v` | 20 | таблица цен (перечисления `AxiomPrice`, `ResultName`) | семейство `nat -> list nat` в формулировке выбора (`:263`) |
| `FiniteTreeEmbedding.v` | 18 | — (деревья) | поддеревья узла: `FNode : list FTree -> FTree` (`:16`) |
| `HigmanLemma.v` | 16 | — (слова) | слова как списки, вложение `list_le` (`:29`) |
| `KruskalFull.v` | 12 | — (деревья) | через `FTree` |
| `KruskalTree.v` | 19 | — (деревья; последовательности `nat -> A`) | через `FTree` |
| `StructuralWellOrdersWithoutChoice.v` | 6 | отношения на типе; `Level` | нет |
| `ZermeloDeterminacy.v` | 6 | `GameState -> Prop` | через `GameState` |

Что из этого следует:

- множества слоя заданы предикатами, типами с отображениями и функциями в `bool`; ни в одном файле множество не
  определено как support списка, кроме `in_list`;
- списки взяты из стандартной библиотеки (`From Stdlib Require Import List` — в восьми файлах из одиннадцати) и служат
  рабочим материалом: позициями игр, словами, наборами поддеревьев; три файла списков не содержат;
- из модулей самой формализации слой подключает `SchroederBernstein_ERR`, `ToS_Axioms`, `TheoryOfSystems_Core_ERR`,
  `foundation.Ordinal`, `foundation.TransfiniteInductionLevel` и собственные файлы; модуля о списках среди них нет;
- перехода «список → мультимножество → множество» в `src` нет: слово `multiset` встречается в двух файлах другой темы
  (`light/MaxwellFromGraph.v`, `numbertheory/PrimeFactorization.v`).

Единственный переход от списка к множеству (`CantorBendixsonFull.v:519`):

```coq
Definition in_list (l : list Q) : PointSet :=
  fun x => exists q, In q l /\ x == q.
```

Он действительно есть support списка и не видит ни порядка, ни кратности (`CheckListQ.v`, все — Closed under the
global context):

```coq
Theorem in_list_ignores_order : forall (l1 l2 : list Q),
  Permutation l1 l2 -> forall x : Q, in_list l1 x <-> in_list l2 x.
Theorem in_list_ignores_multiplicity : forall (q0 : Q) (l : list Q) (x : Q),
  in_list (q0 :: q0 :: l) x <-> in_list (q0 :: l) x.
Theorem full_set_is_not_a_list : ~ exists l : list Q, forall x : Q, in_list l x.
```

Последняя теорема показывает границу: множество всех рациональных точек слоя списком не задаётся.

Сама глава ниже называет положение иначе: в таблице (стр. 682) — «требует уточнения», в пояснении (стр. 690–692) —
«точная связь списка, support и теоретико-множественного слоя ещё требует уточнения».

**В чём расхождение.** Слова «отражено прямо … располагается поверх списочного аппарата» говорят больше, чем есть в
репозитории, и расходятся с таблицей той же главы.

**(а) Довести формализацию.** Возможно частично, без допущений. Двухступенчатая схема главы записывается и
доказывается (`CheckList.v`; все утверждения — Closed under the global context):

```coq
Section ListModes.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  Definition mult (l : list A) : A -> nat := fun x => count_occ eq_dec l x.   (* режим «мультимножество» *)
  Definition support (l : list A) : A -> Prop := fun x => In x l.             (* режим «множество» *)

  Definition same_multiset (l1 l2 : list A) : Prop := forall x, mult l1 x = mult l2 x.
  Definition same_set (l1 l2 : list A) : Prop := forall x, support l1 x <-> support l2 x.

  (* первая ступень забывает порядок и только его *)
  Theorem first_step_forgets_exactly_order :
    forall l1 l2, same_multiset l1 l2 <-> Permutation l1 l2.
  Proof.
    intros l1 l2. unfold same_multiset, mult. split.
    - intro H. apply (Permutation_count_occ eq_dec). exact H.
    - intro H. apply (Permutation_count_occ eq_dec). exact H.
  Qed.

  (* множество получается из мультимножества: кратность > 0 *)
  Theorem support_from_mult : forall l x, support l x <-> mult l x > 0.
  Proof. intros l x. unfold support, mult. apply (count_occ_In eq_dec). Qed.

  Theorem second_step_well_defined : forall l1 l2, same_multiset l1 l2 -> same_set l1 l2.
  Corollary set_ignores_order : forall l1 l2, Permutation l1 l2 -> same_set l1 l2.
  Lemma set_ignores_multiplicity : forall (a : A) (l : list A), same_set (a :: a :: l) (a :: l).
  Theorem set_has_duplicate_free_list : forall l, exists l', NoDup l' /\ same_set l l'.
End ListModes.

(* каждая ступень действительно что-то забывает *)
Theorem order_is_forgotten :
  [1; 2; 3] <> [3; 2; 1] /\ same_multiset nat Nat.eq_dec [1; 2; 3] [3; 2; 1].
Theorem multiplicity_is_forgotten :
  same_set nat [1; 1; 2; 3] [1; 2; 3] /\ ~ same_multiset nat Nat.eq_dec [1; 1; 2; 3] [1; 2; 3].

(* обратного пути нет: что зависит только от множества, не видит кратности;
   что зависит только от мультимножества, не видит порядка *)
Theorem set_mode_cannot_see_multiplicity : forall (B : Type) (g : list nat -> B),
  (forall l1 l2, same_set nat l1 l2 -> g l1 = g l2) -> g [1; 1] = g [1].
Theorem multiset_mode_cannot_see_order : forall (B : Type) (g : list nat -> B),
  (forall l1 l2, same_multiset nat Nat.eq_dec l1 l2 -> g l1 = g l2) -> g [1; 2] = g [2; 1].
```

Такой файл (например, `src/settheory/ListModes.v`) вместе с тремя леммами об `in_list` дал бы прямой формальный якорь
тезису «множество есть support списка с погашенными порядком и кратностью» — для множеств, заданных списком. Довести
до слов «весь слой располагается поверх списочного аппарата» честно нельзя: в слое есть множества, не заданные никаким
списком (`full_set_is_not_a_list`), и для предикатов общего вида (`PointSet := Q -> Prop`) представление через список
или перечисляющий процесс в формализации не доказано. Для них верным остаётся слово таблицы — «требует уточнения».

**(б) Поправить слова** (согласовать со стр. 682 и 690–692):

> **Теория множеств как надстройка.** Сказанное не отменяет теории множеств. Оно указывает её *место*: формальная
> теория множеств есть *надстройка* над более первичным уровнем списков, а не фундамент под ним. В репозитории ToS
> это отражено пока частично: в формализации теоретико-множественных конструкций[^2] множества заданы предикатами и
> типами, списки служат их рабочим материалом — позициями игр, словами, наборами поддеревьев, — а переход от списка к
> множеству записан в одном месте (`in_list`: конечное множество точек как support списка). Точная связь списка,
> support и теоретико-множественного слоя ещё требует уточнения (см. таблицу § 7.3).

Если принять вариант (а), слова «в одном месте (`in_list` …)» заменяются на «для множеств, заданных списком
(`ListModes.v`: `first_step_forgets_exactly_order`, `support_from_mult`)».

## Расхождение 3. `ConnectionClosesGap.v`: соответствие записано комментарием, теорема — три числовые проверки (сноска 1, стр. 735)

**Было:** «`ConnectionClosesGap.v` собирает Barandes-style correspondence между distinction graph, doubly stochastic /
unistochastic transitions и path-dependence.»

**Проверка.** Состав файла `src/foundation/ConnectionClosesGap.v` (27 `Qed`, все — Closed under the global context):

- таблица соответствия с аксиомами Барандеса — комментарий (`:20–44`; повторно `:257–273`);
- `is_DS_2x2 a b c d` (`:55`) — четыре числа образуют дважды стохастическую матрицу $2\times2$; пример
  $(1/2, 1/2, 1/2, 1/2)$;
- 18 числовых равенств вида `(9#25) + (16#25) == 1`, `(4#9) + (4#9) + (1#9) == 1`; 15 из них — пять равенств, каждое
  под тремя именами (например, `U2_col0_norm`, `Gamma2_row0`, `Gamma2_col0`);
- `History := list nat`, `has_intermediate`, `indivisible` (`:176–194`) и пример на списках `[1;2;3]`, `[1;4;3]`;
- итоговые теоремы `complete_chain_N2`, `complete_chain_N3`, `grand_synthesis`.

```coq
Definition indivisible (h1 h2 : History) : Prop :=
  exists s1 s2, has_intermediate h1 s1 /\ has_intermediate h2 s2 /\ s1 <> s2.

Theorem grand_synthesis :
  is_DS_2x2 (1#2) (1#2) (1#2) (1#2) /\
  is_DS_2x2 (9#25) (16#25) (16#25) (9#25) /\
  indivisible [1%nat;2%nat;3%nat] [1%nat;4%nat;3%nat].
```

Чего в утверждениях файла нет:

- графа: ни типа графа, ни матрицы смежности; «distinction graph» встречается только в комментариях; запись
  `Distinction` не подключена (файл подключает только стандартную библиотеку);
- унистохастичности: предикат `is_unistochastic` объявлен в `UnistochasticFromGraph.v`, сюда не подключён; проверяется
  двойная стохастичность четырёх чисел;
- связи чисел $9/25$, $16/25$ с преобразованием Кэли: матрица $U$ объектом файла не является, о ней говорит
  комментарий;
- зависимости от пути: `indivisible` — свойство пары списков («у них есть разные промежуточные элементы»), матриц
  переходов и их произведения в определении нет. История с двумя разными промежуточными состояниями «неделима» сама
  с собой, а любые два трёхэлементных списка с разными средними элементами «неделимы» (`CheckGap.v`, Closed under the
  global context):

```coq
Lemma history_indivisible_with_itself : indivisible [1; 2; 3; 4]%nat [1; 2; 3; 4]%nat.
Lemma indivisible_is_about_lists : forall (a b c d s1 s2 : nat),
  s1 <> s2 -> indivisible [a; s1; b] [c; s2; d].
```

**В чём расхождение.** Соответствие, о котором говорит сноска, записано в файле комментарием; итоговая теорема
соединяет три проверки на числах и списках, не связанные между собой ни одним общим объектом.

**(а) Довести формализацию.** Возможно для $N = 2$, без допущений, из объектов соседних файлов (`GraphUnitary.v`:
`M_2`, `cayley_2`; `UnistochasticFromGraph.v`: `is_orthogonal`, `is_unistochastic`, `unistochastic_implies_DS`).
Цепочка проверена (`CheckBarandes.v`; все утверждения — Closed under the global context):

```coq
(* 1. cayley_2 theta есть преобразование Кэли матрицы графа M_2 theta:  U (I - M/2) = I + M/2 *)
Theorem cayley_2_is_cayley_transform : forall theta i j,
  (i < 2)%nat -> (j < 2)%nat ->
  mat_prod (GraphUnitary.cayley_2 theta) (I_minus_half theta) 2 i j == I_plus_half theta i j.
Proof.
  intros theta i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia;
    unfold mat_prod, I_minus_half, I_plus_half, Id2, GraphUnitary.M_2,
           GraphUnitary.cayley_2; simpl; field;
    apply GraphUnitary.four_plus_sq_neq_0.
Qed.

(* 2. она ортогональна при любом theta *)
Theorem cayley_2_orthogonal : forall theta, is_orthogonal (GraphUnitary.cayley_2 theta) 2.
Theorem cayley_2_transpose_orthogonal : forall theta,
  is_transpose_orthogonal (GraphUnitary.cayley_2 theta) 2.

(* 3. матрица переходов Gamma(theta) = |U(theta)|^2 унистохастическая и дважды стохастическая *)
Definition Gamma_graph (theta : Q) : Mat := gamma_of (GraphUnitary.cayley_2 theta).
Theorem graph_transition_unistochastic : forall theta, is_unistochastic (Gamma_graph theta) 2.
Corollary graph_transition_doubly_stochastic : forall theta, is_doubly_stochastic (Gamma_graph theta) 2.
Lemma cayley_2_at_1_is_U2 : forall i j, GraphUnitary.cayley_2 1 i j == U2 i j.

(* 4. неделимость: матрица переходов за два шага унистохастическая,
      но не равна произведению матриц переходов за один шаг (49/625 против 337/625) *)
Definition two_step (U : Mat) : Mat := fun i j => mat_prod U U 2 i j.
Theorem two_step_transition_unistochastic : is_unistochastic (gamma_of (two_step U2)) 2.
Theorem two_step_transition_indivisible :
  ~ (forall i j, (i < 2)%nat -> (j < 2)%nat ->
       gamma_of (two_step U2) i j == mat_prod Gamma2 Gamma2 2 i j).
Proof.
  intro H.
  assert (H00 := H 0%nat 0%nat ltac:(lia) ltac:(lia)).
  vm_compute in H00. discriminate H00.
Qed.
```

С этими теоремами три звена соответствия связаны одним объектом — матрицей графа `M_2`: её преобразование Кэли
ортогонально, квадраты его элементов образуют унистохастическую и дважды стохастическую матрицу переходов, а переход
за два шага не раскладывается в произведение одношаговых. Остаётся вне формализации: происхождение графа из записи
`Distinction` (матрица `M_2` вписана в файл), вывод двойной стохастичности из $L1$ для этой матрицы, общий случай
$N$. Последняя фраза сноски («не должны читаться как уже завершённый формальный вывод …») остаётся в силе.

**(б) Поправить слова:**

> `ConnectionClosesGap.v` проверяет на примерах три звена Barandes-style correspondence — двойную стохастичность
> равномерной матрицы $2\times2$ и матрицы $(9/25,\ 16/25)$ и различие промежуточных состояний двух историй — и
> сводит эти проверки в одну теорему; само соответствие между distinction graph, doubly stochastic / unistochastic
> transitions и path-dependence приведено в файле таблицей в комментарии.

## Расхождение 4 (статус). «Запись `Distinction` с её полями машинно проверена» (стр. 685–687)

**Было:** «Позитивная онтология имеет прямой формальный след: запись `Distinction` с её полями машинно проверена.»

**Проверка.** `src/foundation/Distinction.v:67`:

```coq
Record Distinction := mkDistinction {
positive   : Prop;
negative   : Prop;
exclusive  : ~ (positive /\ negative);
exhaustive : positive \/ negative;
}.
```

Это определение записи. Поля `exclusive` и `exhaustive` — требования к тому, кто строит экземпляр: предъявить
доказательство несовместности и доказательство исчерпанности. Теоремы `L2_exclusivity` (`:107`) и `L3_totality`
(`:117`) возвращают эти поля (`exact (exclusive D)`, `exact (exhaustive D)`); обе — Closed under the global context.
Канонический экземпляр `distinction_of P` (`:75`) строится с полем `exhaustive := classic P`;
`Print Assumptions distinction_of` — `Axioms: Distinction.classic : forall P : Prop, P \/ ~ P`. Из 20 утверждений
файла 9 зависят от `Distinction.classic`, 11 закрыты. Утверждения о позитивности существующего в файле нет.

**В чём расхождение.** «Машинно проверена» сказано об определении. Компилятор проверил, что определение записано
правильно; содержание полей — несовместность и исчерпанность сторон — он не доказывал: это условия, которые экземпляр
обязан принести с собой. Строка таблицы (стр. 680) называет то же точнее — «прямой формальный след».

**(а) Довести формализацию.** Возможно, без допущений: доказать о записи то, что глава говорит об отрицании
(стр. 498–501, 513–515: «отрицание — производная операция над положенным», «аспект этой структуры»). В `Check.v`
проверено, обе — Closed under the global context:

```coq
Theorem negative_iff_not_positive :
  forall D : Distinction, negative D <-> ~ positive D.
Proof.
  intro D. split.
  - intros n p. exact (exclusive D (conj p n)).
  - intro np. destruct (exhaustive D) as [p | n].
    + contradiction.
    + exact n.
Qed.

Theorem positive_iff_not_negative :
  forall D : Distinction, positive D <-> ~ negative D.
```

То есть во всяком различении отрицательная сторона равносильна отрицанию положительной (и наоборот): самостоятельного,
не определяемого положительной стороной содержания у поля `negative` нет. Там же пример экземпляра, у которого
отрицательная сторона записана без знака отрицания и который строится без аксиомы (`zero_or_succ`: «$n = 0$» против
«$n$ есть следующее за некоторым $m$»). С этими теоремами (добавление в `Distinction.v`, существующее не меняется)
слова «машинно проверена» получают опору: «…запись `Distinction` машинно проверена: во всяком различении отрицательная
сторона равносильна отрицанию положительной (`negative_iff_not_positive`)».

**(б) Поправить слова:**

> Позитивная онтология имеет прямой формальный след: запись `Distinction` с её полями задана в Rocq, и канонический
> экземпляр `distinction_of` построен (его поле `exhaustive` заполняет аксиома `classic`).

## Расхождение 5 (имена). Файл `Core_ERR.v` (стр. 681)

**Было:** «| операциональная делимость | `Level`, `System` $L$, `Criterion` в `Core_ERR.v` | формализовано как иерархия
уровней |»

**Проверка.** Файла `Core_ERR.v` в `src` нет; полное имя — `TheoryOfSystems_Core_ERR.v` (так файл назван на стр. 339
и в сноске 3). `Level` (`:59`), `Criterion` (`:163`), `System` (`:203`) в нём объявлены.

**(б) Стало:** «| операциональная делимость | `Level`, `System` $L$, `Criterion` в `TheoryOfSystems_Core_ERR.v` |
формализовано как иерархия уровней |».

## Сомнительные места (не расхождения)

- **Стр. 89–98, 113, 130–132 — статус $L3$.** Глава говорит об $L3$ в трёх формах, и в формализации им отвечают три
  разных объекта:
  «третьего исхода структурно нет» (стр. 92–93) — `L3_binarity : forall P, ~ ~ (P \/ ~ P)` и `pending_binarity`
  (`foundation/BinarityVsTotality.v:72`, `:104`), Closed under the global context;
  «держится всегда, для любого $A$», «дизъюнкция верна всегда» (стр. 94–95, 113) — `Axiom classic`
  (`foundation/Distinction.v:36`); шапка `BinarityVsTotality.v`: «TOTALITY … NOT provable; this is precisely the
  axiom `classic`»;
  «полнота завершённого различения» (стр. 131–132) — `L3_totality` (`Distinction.v:117`), проекция поля `exhaustive`.
  О доказанности в Rocq глава здесь не говорит, слово «онтологически» стоит, Глава 3 оговаривает двойной статус —
  расхождения нет. Заголовок «$L3$ держится безусловно» и слово «выводится» стоят без этой оговорки; при желании
  автора после «(Глава 3)» можно добавить: «в Rocq общая форма принята аксиомой `classic`, без аксиом доказана
  невозможность третьего исхода (`L3_binarity`)». Файлы `BinarityVsTotality.v` и `TotalityNow.v` (июль 2026 года), в
  которых две формы $L3$ разведены, страницы Части I не называют; согласование слов главы с этим разведением — вопрос
  к автору, вне предмета проверки.
- **Стр. 100–118 — суперпозиция как несовершённое различение.** У этого чтения есть формальный якорь, который глава
  не называет: запись `PendingDistinction` (`BinarityVsTotality.v:94`) — две со-определённые и несовместные стороны
  без поля исчерпанности; `pending_binarity` — третьего нет уже для несовершённого акта; `actualize` (`:130`) —
  переход к завершённому различению по предъявленному исходу. Теорем о квантовых состояниях там нет.
- **Стр. 303–306 — «Формально этот режим … развёрнут с E/R/R-разбором в Части II».** Речь о разборе E/R/R в
  Главе II.2, не о Rocq; перехода «список → мультимножество → множество» в формализации нет (расхождение 2). Слово
  «Формально» может быть прочитано как «в формализации»; вариант без этого риска: «Подробно этот режим … развёрнут с
  E/R/R-разбором в Части II».
- **Стр. 538–544 и сноска 3 — у формальной иерархии есть нижний уровень.** «Над всяким уровнем есть уровень выше» —
  верно (`level_lt_succ`, `level_no_top`, `foundation/TransfiniteInductionLevel.v:61`, `:75`). Словам «под структурой
  … на более низком уровне обнаруживается её собственное устройство» в типе `Level` ничего не отвечает, и сноска это
  оговаривает. Сверх оговорки (`Check.v`, Closed under the global context): под `L1` нет ничего
  (`nothing_below_L1`); критериев и систем уровня `L1` не существует (`no_criterion_at_L1`, `no_system_at_L1`);
  область критерия `crit_domain` — произвольный тип, с уровнем-свидетелем не связанный
  (`domain_independent_of_witness`). Формализована, таким образом, иерархия уровней-меток; разложения объектов по
  уровням в ней нет. В сноску можно добавить одну фразу: «у формальной иерархии есть нижний уровень `L1`».
- **Стр. 679 и 688–690 — «процессные конструкции и незавершённость бесконечности проверены».** `Generator` и `Process`
  в `TheoryOfSystems_Core_ERR.v` — определения записей; теорем о них в этом файле нет (есть развёртка `unfold_gen`).
  «Незавершённость бесконечности» — `completed_inf_contradicts_P4` (`P4CompletedInfinity.v:70`): противоречие
  получено из трёх посылок, третья — мост `bridge S actual` (все члены `S` актуальны на стадии 0). Слово «частично» и
  оговорка «не как единая полная модель» это покрывают.
- **Стр. 711–713 — «Точное распределение … сведено в таблицу».** Таблица стр. 677–683 распределяет пять позиций
  Главы 7. Узлы, перечисленные в том же абзаце, — Законы $L1$–$L5$, Принципы $P1$–$P4$, $E/R/R$, аксиомы реализации —
  в неё не входят. К формализации замечание не относится; вариант: «Распределение для позиций онтологического ядра
  сведено в таблицу «Позиции и их формальный статус»; для узлов Глав 1–6 оно дано в самих этих главах».
- **Сноска 1 — `DistinctionProcess.v`.** Модель — две функции номера шага: `distinction_sharpness K := K/(K+1)`,
  `coherence K := 1/(K+1)`; запись `Distinction` в утверждения не входит (модуль подключён, его объявления не
  используются). Рост резкости с каждым шагом в файле не доказан (есть значения при $K = 0, 1, 2$), теорема о
  завершении для любого $\varepsilon$ оставлена под `Abort` с пометкой «NOT provable … without Archimedean». Обе
  доказываются без допущений (`CheckProcess.v`: `coherence_decreasing`, `sharpness_increasing`,
  `measurement_eventually_completes`, `measurement_stays_complete`; Closed under the global context). Слова сноски
  («задаёт модель …, где измерение понимается как постепенное sharpening») с файлом согласны.
- **Сноска 1 — `MeasurementSynthesis.v`.** «Мост» — порог $1/2$ на той же функции: `is_quantum K := 1/2 < coherence K`,
  `is_classical K := coherence K <= 1/2`; доказаны три значения ($K = 0, 1, 2$). Слово «формулирует» точно.
- **Сноска 1 — `UnistochasticFromGraph.v`.** В файле нет графа: матрицы `U2`, `U3` вписаны, преобразование Кэли
  вычисляется в `GraphUnitary.v`, и связь между двумя файлами не доказана (доказывается: `CheckBarandes.v`,
  `cayley_2_at_1_is_U2`). Предикат `is_unistochastic` требует вещественной (рациональной) ортогональной матрицы —
  это частный случай унистохастичности. Слова сноски («конкретные унистохастические конструкции …») верны.
- **Стр. 348–358 — выбор.** Формализацию глава здесь не называет. Якоря есть: `finite_choice_works`
  (`foundation/P4ProhibitsAC.v:171`) — конечный выбор без аксиом; `ac_completed_graph_contradicts_P4` (`:122`) —
  противоречие для графа функции выбора, прочитанного как завершённое целое, при посылке-мосте; `AC_on_nat_as_rule`
  (`:160`) — выбор из счётного семейства непустых списков есть теорема. Словам главы («в этой, завершённой форме …
  несовместима с $P4$») это соответствует.
- **Стр. 510–512 — `distinction_of`.** Описание точное; о цене страница не говорит. Канонический экземпляр зависит от
  `Distinction.classic` (поле `exhaustive`).
- **Стр. 506–509, 680 — имена полей.** `positive`, `negative`, `exclusive`, `exhaustive` — поля записи, а не
  объявления верхнего уровня; имя `positive` без уточнения компилятор относит к стандартной библиотеке (двоичные
  положительные числа). В главе они стоят рядом с именем записи, разночтения нет.

## Вне главы: шапки и состав файлов

Для сведения (в главе эти строки не цитируются):

- `foundation/Distinction.v`: `distinction_theorem_count := 22` (`:250`) — в файле 20 `Qed`; комментарий `:34–35`
  («Not an additional axiom — L3 = classic») стоит над объявлением `Axiom classic`; `L1_stability` (`:93`) —
  `positive D = positive D`, доказательство `reflexivity`.
- `TheoryOfSystems_Core_ERR.v`: `russell_paradox_blocked` (`:248`) и `cantor_no_system_of_all_L2_systems` (`:1300`) —
  одно утверждение под двумя именами; у `cantor_paradox_blocked_v1` (`:1255`) и `no_self_level_elements` (`:1271`)
  член об области критерия в доказательстве не используется; `P2_always_holds` (`:174`) возвращает поле
  `crit_level_valid`; `three_levels_of_being : Prop := True` (`:485`) — пометка для документации.
- `foundation/DistinctionProcess.v`: шапка — «25 Qed», в файле 17; `born_rule_is_distinction_weight` (`:182`) и
  `complementary_weights` (`:172`) — одно утверждение, `p + (1 - p) == 1`, посылка `valid_weight p` отбрасывается
  (`intros p _`); о правиле Борна в нём ничего нет (комментарий файла `:176–181` это оговаривает).
- `foundation/MeasurementSynthesis.v`: шапка — «15 Qed», в файле 8; заголовок «Measurement problem dissolved» при
  трёх доказанных значениях функции $1/(K+1)$.
- `foundation/ConnectionClosesGap.v`: заключительный комментарий — «18 Qed», в файле 27; различных утверждений 17.
- `foundation/GeneralHermitianCayley.v`: `cayley_dense_in_UN` (`:239`) и `p4_all_unistochastic` (`:252`) — равенство
  `N*(N+1)/2 + N*(N-1)/2 = N*N` с отброшенной посылкой под именами о плотности в $U(N)$ и о всех унистохастических
  матрицах; `general_covers_block` (`:224`) — `x == x`.
- `foundation/BlockCayleyUnistochastic.v`: `block_cayley_unistochastic` (`:363`) утверждает суммы строк и
  неотрицательность `block_mod_sq`; унитарной матрицы как объекта в утверждении нет.
- `foundation/P4CompletedInfinity.v`: `P4_prohibition_infinity` (`:114`) повторяет `completed_inf_contradicts_P4`;
  о составных теоремах сказано в шапке файла.
- `settheory/BorelDeterminacy.v:21` объявляет `classic` собственной аксиомой.

## Дополнительные проверки

- `Print Assumptions` снят для всех 169 утверждений девяти файлов (`CheckPA.v`): `Distinction.v` — 11 закрытых и 9 на
  `Distinction.classic` (`every_prop_distinguishes`, `one_distinction_exists`, `two_distinctions_exist`,
  `distinction_count_succ`, `distinction_count_any`, `co_constitution`, `distinction_decidable`, `distinction_and`,
  `distinction_or`); `P4CompletedInfinity.v` (10), `DistinctionProcess.v` (17), `MeasurementSynthesis.v` (8),
  `UnistochasticFromGraph.v` (19), `ConnectionClosesGap.v` (27), `GraphUnitary.v` (26),
  `BlockCayleyUnistochastic.v` (22), `GeneralHermitianCayley.v` (20) — все Closed under the global context. Других
  имён в выводе компилятора нет.
- Отдельно сняты: `russell_paradox_blocked`, `level_lt_irrefl`, `P1_no_self_membership`, `P2_always_holds`,
  `cantor_paradox_blocked_v1`, `no_self_level_elements`, `cantor_no_system_of_all_L2_systems`, `L5_resolve_le_all`
  (`TheoryOfSystems_Core_ERR.v`); `criterion_label_never_own_level`, `russell_blocked_every_level`,
  `level_foundation_form` (`TransfiniteInductionLevel.v`); `L3_binarity`, `pending_binarity`
  (`BinarityVsTotality.v`); `finite_choice_works`, `ac_completed_graph_contradicts_P4`, `AC_on_nat_as_rule`
  (`P4ProhibitsAC.v`); `finite_choice` (`P4_Eliminates_AC.v`) — все Closed under the global context.
- Файлы в репозитории и в собранной копии совпадают побайтно (SHA-1): `Distinction.v`,
  `TheoryOfSystems_Core_ERR.v`, `P4CompletedInfinity.v`, `DistinctionProcess.v`, `MeasurementSynthesis.v`,
  `UnistochasticFromGraph.v`, `ConnectionClosesGap.v`, `GraphUnitary.v`, `CantorBendixsonFull.v`,
  `BinarityVsTotality.v`, `TransfiniteInductionLevel.v`.
- Счёт `Qed` (`grep -c 'Qed\.'`): `Distinction.v` — 20, `TheoryOfSystems_Core_ERR.v` — 36,
  `P4CompletedInfinity.v` — 10, `DistinctionProcess.v` — 17, `MeasurementSynthesis.v` — 8,
  `UnistochasticFromGraph.v` — 19, `ConnectionClosesGap.v` — 27; каталог `src/settheory/` — 11 файлов, 178.
  Страница этих чисел не приводит.
- Оговорки главы о статусе (стр. 8–11, 23–28, 137–144, 373–379, 589–596, 608–610, 685–696, сноски 1 и 3) с
  содержанием формализации согласны, кроме двух мест, вынесенных в расхождения 2 и 4.
