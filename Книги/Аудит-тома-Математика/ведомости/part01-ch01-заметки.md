# Глава I.1 «Первоначало: A = ∃» — заметки к ведомости (13.11.2026)

Ведомость: `part01-ch01.json` — 43 ручные записи + 7 автоматических (`Prop`, `unit`, `tt`, `nat`, `X`, `ex`,
`bool` — имена стандартной библиотеки и переменная блока кода); `merge --dry` проходит без замечаний, список
«без сверки» пуст. Вердикты ручных записей: ok — 25, mismatch-statement — 14, mismatch-price — 1,
missing-name — 3 (с автоматическими: ok — 32).

Четырнадцать записей mismatch-statement и три missing-name относятся к пяти местам (расхождения 1–4 и 6),
запись mismatch-price — к расхождению 5.

Глава философская; о формализации в ней говорят раздел «Граница формализации» (стр. 513–874: записи-попытки и
стандартная библиотека Rocq) и раздел «Что делать с границей» (стр. 880–1271: запись `Distinction`, законы,
аксиомы, анонсы следующих глав). Сноски 1–13 (стр. 1275–1287) — библиографические, о формализации не говорят.
Философские тезисы главы не оценивались.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part01/ch01/`:

- `Check.v` — блок кода страницы `some_type_inhabited`, библиотечный `inhabited`, теоремы о записи `Distinction`
  (собирается; ответы `Print Assumptions` приведены по месту);
- `CheckForget.v` — забывание как функтор на подкатегории забываемых систем (собирается; всё — Closed under the
  global context);
- `CheckClass.v`, `CheckReq.v`, `CheckReq2.v` — запись `Class Inhabited` со страницы и подключение
  `Coq.Logic.Inhabited` (все три компилятор отклоняет — это и есть результат проверки);
- `deps.txt` — граф зависимостей всех файлов формализации (`coqdep`), `closure.cjs`, `closure2.cjs` — счёт файлов,
  зависящих от `foundation/Distinction.v`; `pa39.cjs`, `pa39.txt`, `pa_dp.cjs` — `Print Assumptions` всех теорем
  этих файлов.

В `src`, в собранной копии и на сайте ничего не менялось.

## Что проверить не удалось

- Отсылки к другим главам (главы 2–7 Части I, Часть IV, Часть X, глава 14.4, Методологическое введение) по
  существу не сверялись: это участки других проверок. Проверено только то, что названные в анонсах объекты
  существуют и что о них сказано в самой главе 1 (расхождения 1, 4, 5).
- Недоказуемость закона исключённого третьего в CIC без аксиом — известный метаматематический результат;
  компилятором он не проверяется. В расхождении 1 он использован как довод, а не как проверенный факт.
- Вопрос, существует ли на уровнях выше базового другое, всюду определённое забывание (с заменой свидетеля уровня
  в критерии), не исследовался. Проверено: `forget_obj` определено только для забываемых систем, и функтора из
  `SystemCat (LS L1)` в `SystemCat L1` нет вовсе (расхождение 4).
- Слова стр. 1252 о Части X («список как индуктивный тип, на котором работает оператор в режиме игнорирования
  части атрибутов») имён не называют; с формализацией не сверялись.
- История репозитория известна только по `git`: первый коммит — 19.01.2026. Что было до переноса в репозиторий,
  проверить нечем.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Законы выводятся из `Distinction`»: в формализации законы даны полями записи и аксиомой (стр. 859–860, 1126–1131, 1188–1190, 1228–1229)

**Было:**

> (859–860) Но в Главе 3 акт различения станет основанием для *вывода* законов логики как теорем Rocq.
>
> (1126–1131) Свойства акта различения как первого формализуемого — то, что он опирается на $A = \exists$, не
> отождествляясь с ним; что он формализуем в CIC; что он минимален; что из него выводимы дальнейшие структуры
> (законы логики как теоремы, типизация, со-определение положительного/отрицательного) — суть *наблюдаемые
> характеристики* обнаруженного объекта.
>
> (1188–1190) В Главе 3 будет показано, что из структуры `Distinction` *выводятся* законы логики
> $L1, L2, L3, L4$ как теоремы Rocq о свойствах этой записи.
>
> (1228–1229) Из него выводятся законы логики (Глава 3), типизация (Глава 2.4), онтология
> положительно-отрицательного (Глава 4).

**Проверка.** Запись (`src/foundation/Distinction.v:67`) и аксиома (`:36`):

```coq
Axiom classic : forall P : Prop, P \/ ~P.

Record Distinction := mkDistinction {
positive   : Prop;
negative   : Prop;
exclusive  : ~ (positive /\ negative);
exhaustive : positive \/ negative;
}.
```

Теоремы о законах в том же файле:

```coq
Theorem L1_stability : forall D : Distinction, positive D = positive D.
Proof. reflexivity. Qed.                                              (* :93  *)

Theorem L2_exclusivity : forall D : Distinction, ~ (positive D /\ negative D).
Proof. intros D. exact (exclusive D). Qed.                            (* :107 *)

Theorem L3_totality : forall D : Distinction, positive D \/ negative D.
Proof. intros D. exact (exhaustive D). Qed.                           (* :117 *)

Theorem L4_self_grounding : forall D : Distinction, forall (p : positive D), ~ negative D.
Proof. intros D p n. apply (exclusive D). split; [exact p | exact n]. Qed.   (* :128 *)
```

Все четыре — Closed under the global context. По содержанию:

- `L2_exclusivity` и `L3_totality` возвращают поля `exclusive` и `exhaustive` того экземпляра, о котором
  говорят: заключение теоремы есть то, что вложено в экземпляр при его построении;
- `L1_stability` — рефлексивность равенства; утверждение верно для любого терма и ни одного поля не использует;
- `L4_self_grounding` получена из поля `exclusive` одним шагом и ему равносильна:
  `(P -> ~N) <-> ~(P /\ N)` (`Check.v`, `self_grounding_iff_exclusive`, Closed under the global context);
- закон исключённого третьего для произвольной пропозиции в файле есть аксиома: `distinction_decidable :
  forall P, P \/ ~P` (`:222`) доказана `exact classic`, `Law_of_ExcludedMiddle` в
  `foundation/LawsFromDistinction.v:63` — тоже; `Print Assumptions` обеих: `Distinction.classic`. Этой же аксиомой
  строится различение по пропозиции: `distinction_of P := mkDistinction P (~P) … (classic P)` (`:75`).

То же в `foundation/LawsFromDistinction.v` (22 `Qed`): `L2_from_distinction` и `L3_from_distinction` повторяют
`L2_exclusivity` и `L3_totality`; `five_laws_from_distinction` (`:139`) — конъюнкция тех же утверждений (с
добавлением `negative D = negative D`) и `forall l : Level, ~ (l << l)`; последнее записи `Distinction` не
использует.

В самой главе статус L3 в формализации назван верно в трёх местах: стр. 972–975 («получает статус
самостоятельного $L3$»), стр. 1029 («записываемое как самостоятельное поле»), стр. 1204–1206 («технические
аксиомы … `classic`»). Четыре места, приведённые выше, с ними расходятся.

**В чём расхождение.** Законы L2 и L3 в формализации не выводятся из записи, а входят в неё полями; L4 — то же
поле L2 в другой записи; L1 от записи не зависит; исключённое третье для произвольной пропозиции принято
аксиомой.

**(а) Довести формализацию.** Вывести L3 из записи без аксиомы нельзя. Посылка «для всякого различения
`positive \/ negative`» доказуема без аксиом (это поле), поэтому переход от неё к закону для произвольной
пропозиции сам равносилен этому закону (`Check.v`, Closed under the global context):

```coq
Theorem record_L3_to_general_iff_L3 :
  ((forall D : Distinction, positive D \/ negative D) -> forall P : Prop, P \/ ~ P)
  <-> (forall P : Prop, P \/ ~ P).
```

а закон исключённого третьего в CIC без аксиом не доказуем. Что можно добавить честно — теоремы, показывающие,
*как именно* законы связаны с записью. Проверены в `Check.v`, все — Closed under the global context:

```coq
(* оба поля вместе: отрицательная сторона равносильна отрицанию положительной *)
Theorem negative_iff_not_positive :
  forall D : Distinction, negative D <-> ~ positive D.
Proof.
  intro D. split.
  - intros n p. exact (exclusive D (conj p n)).
  - intro np. destruct (exhaustive D) as [p | n].
    + exfalso. exact (np p).
    + exact n.
Qed.

(* пара сторон достраивается до различения в точности при двух условиях *)
Theorem distinction_exists_iff :
  forall P N : Prop,
    (exists D : Distinction, positive D = P /\ negative D = N)
    <-> ((N <-> ~ P) /\ (P \/ ~ P)).

(* исключённое третье равносильно тому, что различить можно всякую пропозицию *)
Theorem every_prop_distinguishes_iff_L3 :
  (forall P : Prop, exists D : Distinction, positive D = P)
  <-> (forall P : Prop, P \/ ~ P).
Proof.
  split.
  - intros H P. destruct (H P) as [D HP]. subst P.
    destruct (exhaustive D) as [p | n].
    + left. exact p.
    + right. intro p. exact (exclusive D (conj p n)).
  - intros EM P.
    exists (mkDistinction P (~ P)
              (fun H => match H with conj p np => np p end) (EM P)).
    reflexivity.
Qed.

Theorem canonical_distinction_iff_L3 :
  (forall P : Prop, exists D : Distinction, positive D = P /\ negative D = (~ P))
  <-> (forall P : Prop, P \/ ~ P).

Theorem negative_side_alone_iff_L3 :
  (forall N : Prop, exists D : Distinction, negative D = N)
  <-> (forall P : Prop, P \/ ~ P).
```

Третья теорема даёт точное отношение L3 к акту различения: закон не следует из записи, а равносилен тому, что акт
различения применим ко всякой пропозиции. Для канонической пары (P, ¬P) законы L2 и L4 в формализации уже
доказаны без записи и без аксиом: `L2_canonical : forall P, ~ (P /\ ~P)` и `L4_canonical : forall P, P -> ~~P`
(`LawsFromDistinction.v:55`, `:89`, Closed under the global context).

**(б) Поправить слова.**

> (859–860) Но в Главе 3 акт различения станет основанием для *прочтения* законов логики как теорем Rocq о его
> структуре.
>
> (1126–1131) …что он формализуем в CIC; что он минимален; что в его структуре прочитываются дальнейшие (законы
> логики как теоремы о записи, типизация, со-определение положительного/отрицательного) — суть *наблюдаемые
> характеристики* обнаруженного объекта.
>
> (1188–1190) В Главе 3 будет показано, как законы логики $L1, L2, L3, L4$ *прочитываются* в структуре
> `Distinction` теоремами Rocq о свойствах этой записи: $L2$ и $L3$ — её поля `exclusive` и `exhaustive`, взятые
> у произвольного экземпляра; $L4$ — то же поле `exclusive`, записанное импликацией; $L1$ — рефлексивность
> равенства. Исключённое третье для произвольной пропозиции из записи не выводится: оно принято аксиомой
> `classic`, и ею строится различение по любой пропозиции.
>
> (1228–1229) В нём прочитываются законы логики (Глава 3), типизация (Глава 2.4), онтология
> положительно-отрицательного (Глава 4).

Если теоремы пункта (а) будут внесены, к стр. 1188–1190 можно добавить: «Теоремой без аксиом доказано: закон
исключённого третьего выполнен для всех пропозиций тогда и только тогда, когда всякая пропозиция есть
положительная сторона некоторого различения».

## Расхождение 2. «Запись `Distinction` исторически появилась раньше других основных структур» (стр. 1112–1124)

**Было:**

> (1112–1117) **Первое в записи в Rocq — технически приоритетное.** В репозитории `theory-of-systems-coq` запись
> `Distinction` исторически появилась раньше других основных структур и служит основанием для дальнейших
> определений. Это — технический факт о порядке файлов и теорем в репозитории, не претендующий на онтологическое
> утверждение.
>
> (1119–1124) Все три смысла «первого» — онтологический (порождает время), структурный (базовый для дедукции),
> технический (приоритет в репозитории) — согласованы между собой, но имеют разные основания и работают на разных
> уровнях. Когда мы говорим, что акт различения есть *первое формализуемое в томе*, мы используем все три смысла
> одновременно, поскольку в нашем случае они совпадают на одном объекте.

**Проверка.** История репозитория (`git log`):

| что | первый коммит | дата |
|---|---|---|
| `Level`, `<<`, `Criterion`, `System` (`TheoryOfSystems_Core_ERR.v`), `RealProcess` (`ShrinkingIntervals_ERR.v`) | 06db789 | 19.01.2026 |
| `CauchyReal.v` | 1061d6b | 04.03.2026 |
| `Roles.v`, `IntensionalIdentity.v` | 4ec80b8 | 06.03.2026 |
| `SystemCategory.v`, `LevelFunctors.v`, `LevelAdjunction.v` | 8beb4a2 | 08.03.2026 |
| `ToS_Axioms.v` | 956e2fc | 09.03.2026 |
| `process/ProcessCore.v` | 78901df | 14.03.2026 |
| `foundation/Distinction.v` (`Record Distinction`, `mkDistinction`) | 36ef3ff | 19.03.2026 |

Строки `Record Distinction` и `mkDistinction` до коммита 36ef3ff в истории не встречаются (`git log -S`); до него
в репозитории 232 коммита и 725 файлов `.v`. Комментарий в `foundation/LawsFromDistinction.v`, внесённом тем же
коммитом: «BEFORE this file: L1-L5 were NAMES in comments».

Зависимости (граф `coqdep` по 2046 файлам): от `foundation/Distinction.v` прямо или через другие файлы зависят
39 файлов — 30 в `src/foundation`, 9 в `src/stdlib`. `TheoryOfSystems_Core_ERR.v`, `ToS_Axioms.v`, `Roles.v`,
`CauchyReal.v`, `process/ProcessCore.v`, `SystemCategory.v`, `LevelFunctors.v`, `LevelAdjunction.v`,
`ShrinkingIntervals_ERR.v` в их числе нет. Обратная зависимость есть: `LawsFromDistinction.v` подключает
`TheoryOfSystems_Core_ERR.v` (оттуда `Level` для L5).

**В чём расхождение.** Запись `Distinction` внесена в репозиторий через два месяца после уровней, систем и
процессов, и основные определения на неё не опираются; названное «техническим фактом» история и граф зависимостей
не подтверждают.

**(а) Довести формализацию.** Невозможно: историю репозитория не изменить, а подключение
`foundation/Distinction.v` к основным файлам ничего бы в их определениях не изменило (см. расхождение 3).

**(б) Поправить слова.**

> **Первое в записи в Rocq — открывающее цепочку основания.** В репозитории `theory-of-systems-coq` запись
> `Distinction` открывает файл `foundation/Distinction.v`, с которого начинается цепочка основания: от неё идут
> теоремы о законах, принципах и E/R/R. По времени записи она не первая: файл внесён 19 марта 2026 года, после
> определений уровней, систем и процессов, и на него опираются 39 файлов из 2046. Это — технический факт о
> порядке файлов и теорем в репозитории, не претендующий на онтологическое утверждение.
>
> Три смысла «первого» — онтологический (порождает время), структурный (базовый для дедукции), технический
> (начало цепочки основания в репозитории) — имеют разные основания и работают на разных уровнях. Когда мы
> говорим, что акт различения есть *первое формализуемое в томе*, мы используем первые два смысла; третий
> относится к одной цепочке файлов, а не ко всему репозиторию.

## Расхождение 3. «От акта различения выводится дальнейшее; каждый последующий объект тома разворачивается из него» (стр. 1095–1103, 1229–1231)

**Было:**

> (1095–1103) **Первое в записи тома — структурно базовое.** В математической работе тома акт различения играет
> роль *первого формализуемого*: первого объекта, который записывается в Rocq и от которого *выводится*
> дальнейшее. Эта роль — не временная (она не утверждает порядок написания глав или порядок исследования автора),
> а *структурная*: акт различения находится в основании дедуктивной цепи, и каждый последующий объект тома
> (числовые системы, функции, пространства, категории) разворачивается из него через последовательность
> формализаций.
>
> (1229–1231) Дальнейшая работа тома получает прочный фундамент в виде формального объекта, на котором стоит
> строго.

**Проверка.** Тот же граф зависимостей: 39 файлов из 2046. По каталогам: `src/foundation` — 30 из 404,
`src/stdlib` — 9 из 552; в корне `src` (103 файла), в `src/process` (340), `src/analysis` (40), `src/algebra`
(12), `src/category` (13), `src/settheory` (11), `src/numbertheory` (11), `src/geometry` (7) и остальных
каталогах — ни одного. Определения, которыми в формализации заданы объекты, названные на странице:

- числа — `nat` и `Q` стандартной библиотеки;
- процессные действительные — `RealProcess := nat -> Q` (`process/ProcessCore.v:34`; файл подключает только
  стандартную библиотеку);
- системы и уровни — `Level`, `Criterion`, `System` (`TheoryOfSystems_Core_ERR.v:59` и далее);
- категории — `SystemCat` (`SystemCategory.v:57`).

Ни одно из них не содержит записи `Distinction` и не зависит от её файла. Формальная цепочка, идущая от записи:
`Distinction.v` → `LawsFromDistinction.v` → `PrinciplesFromLaws.v` → `PrinciplesToERR.v`, `ERRFromDistinction.v`
и далее файлы `foundation` о физических приложениях. Связь с числами в ней есть в виде соответствия, а не
построения: `positive_nat_is_distinction_count` (`foundation/PrimalityOfOne.v:94`) утверждает, что для всякого
`n ≥ 1` существует список различений длины `n`; тип `nat` при этом уже дан.

**В чём расхождение.** Страница говорит о дедуктивной цепи, в основании которой стоит запись в Rocq; в
формализации числа, процессы, системы и категории определены независимо от этой записи, и от неё зависит одна
ветвь из 39 файлов.

**(а) Довести формализацию.** Честно довести нельзя. Подключение файла не делает определение выведенным: `nat`,
`Q`, `nat -> Q`, `System` суть индуктивные типы и функции CIC, и запись `Distinction` в их определения не входит.
Возможны только связующие теоремы вида «в такой-то структуре прочитывается различение»; они показывают
соответствие, а не порядок вывода, и часть их уже есть.

**(б) Поправить слова.**

> **Первое в записи тома — структурно базовое.** В математической работе тома акт различения играет роль
> *первого формализуемого*: первого объекта, который записывается в Rocq и с которого начинается изложение. Эта
> роль — не временная (она не утверждает порядок написания глав или порядок исследования автора), а
> *структурная*: акт различения стоит в основании порядка изложения, и каждый последующий объект тома (числовые
> системы, функции, пространства, категории) вводится после него. В самой формализации эта связь проведена не
> зависимостью файлов: числа, процессы и категории систем определены на индуктивных типах Rocq, а от записи
> `Distinction` формально зависит цепочка основания — законы, принципы, E/R/R.
>
> (1229–1231) Дальнейшая работа тома получает в нём формальный объект, с которого начинается изложение;
> формальная зависимость от него проведена в цепочке основания, а не во всех файлах формализации.

## Расхождение 4. «Функторы `forget` и `embed` с их сопряжением» (стр. 1253)

**Было:**

> Первое формализуемое по эту сторону границы — сама схема перехода между уровнями (функторы `forget` и `embed` с
> их сопряжением).

**Проверка.** Объявления `forget` в формализации нет. Объявления `embed` есть в двух файлах, и оба — другие
объекты: `process/ProcessFiniteDim.v:310` (обрезание последовательности: `fun k => if Nat.ltb k n then f k else 0`)
и `stdlib/ProcessHilbert.v:34` (дописывание нуля к списку). Переход между уровнями записан в `src/LevelFunctors.v`
и `src/LevelAdjunction.v`:

```coq
Definition embed_obj (L : Level) (S : System L) : System (LS L)                      (* LevelFunctors.v:34  *)
Definition EmbedFunctor (L : Level) : Functor (SystemCat L) (SystemCat (LS L)).      (* :130 *)

Definition is_forgettable (L : Level) (S : System (LS L)) : Prop :=
  crit_level_witness (LS L) (sys_criterion (LS L) S) << L.                           (* :186 *)
Definition forget_obj (L : Level) (S : System (LS L)) (Hf : is_forgettable L S) : System L   (* :192 *)
Theorem P1_obstructs_total_forget : forall (L : Level),
  exists S : System (LS L), ~ is_forgettable L S.                                    (* :353 *)

Theorem level_adjunction : forall (L : Level) (S : System L)
  (T : System (LS L)) (Hf : is_forgettable L T),
  (forall (f : SystemMorphism (LS L) (embed_obj L S) T),
    morphism_eq (LS L) (adj_backward L S T Hf (adj_forward L S T Hf f)) f) /\
  (forall (g : SystemMorphism L S (forget_obj L T Hf)),
    morphism_eq L (adj_forward L S T Hf (adj_backward L S T Hf g)) g).               (* LevelAdjunction.v:85 *)
```

Все перечисленные — Closed under the global context. Вложение — запись `Functor`. Забывание определено только для
систем со свойством `is_forgettable`; записи `Functor` для него нет (шапка `LevelAdjunction.v`: «we cannot form a
proper Functor instance for it»), законы функтора доказаны отдельными леммами с условием забываемости
(`forget_mor_id`, `forget_mor_comp`). `level_adjunction` — взаимная обратность двух отображений морфизмов при
условии `is_forgettable L T`; естественность — `adj_natural_S`, `adj_natural_T` (`:101`, `:117`), тоже при этом
условии.

**В чём расхождение.** Имён `forget` и `embed` в названном смысле нет; функтором в формализации является только
вложение, а забывание и сопряжение определены на части категории `SystemCat (LS L)` — на забываемых системах.

**(а) Довести формализацию.** Возможно, без допущений. В `CheckForget.v` забывание записано функтором на полной
подкатегории забываемых систем; всё — Closed under the global context:

```coq
Definition full_subcat (C : Category) (P : cat_obj C -> Prop) : Category := …   (* объекты: { a | P a } *)

Definition ForgettableCat (L : Level) : Category :=
  full_subcat (SystemCat (LS L)) (is_forgettable L).

Definition ForgetFunctor (L : Level) : Functor (ForgettableCat L) (SystemCat L).
Proof.
  apply (mkFunctor (ForgettableCat L) (SystemCat L)
    (fun A => forget_obj L (proj1_sig A) (proj2_sig A))
    (fun A B f => forget_mor L (proj1_sig A) (proj1_sig B) (proj2_sig A) (proj2_sig B) f)).
  - intros A B f g Heq. apply forget_mor_compat. exact Heq.
  - intros A. apply forget_mor_id.
  - intros A B C f g. simpl. apply forget_mor_comp.
Defined.

Definition EmbedToForgettable (L : Level) : Functor (SystemCat L) (ForgettableCat L).

Lemma Forget_Embed_obj : forall (L : Level) (S : System L),
  fobj (ForgetFunctor L) (fobj (EmbedToForgettable L) S) = S.

Theorem embed_forget_hom_bijection : forall (L : Level) (S : System L) (T : cat_obj (ForgettableCat L)),
  (forall f : cat_mor (ForgettableCat L) (fobj (EmbedToForgettable L) S) T,
     cat_mor_eq (ForgettableCat L) (fobj (EmbedToForgettable L) S) T
       (adj_backward L S (proj1_sig T) (proj2_sig T) (adj_forward L S (proj1_sig T) (proj2_sig T) f)) f) /\
  (forall g : cat_mor (SystemCat L) S (fobj (ForgetFunctor L) T),
     cat_mor_eq (SystemCat L) S (fobj (ForgetFunctor L) T)
       (adj_forward L S (proj1_sig T) (proj2_sig T) (adj_backward L S (proj1_sig T) (proj2_sig T) g)) g).

Theorem no_functor_to_base :
  forall F : Functor (SystemCat (LS L1)) (SystemCat L1), False.
```

С этими определениями слова «функторы забывания и вложения с их сопряжением» верны для пары категорий `Sys(L)` и
«забываемые системы уровня `LS L`». Распространить забывание на всю `SystemCat (LS L)` на базовом шаге нельзя:
в `SystemCat L1` нет ни одного объекта (`L1_criterion_absurd`, `SystemCategory.v:412`), поэтому функтора из
`SystemCat (LS L1)` в `SystemCat L1` не существует (`no_functor_to_base`).

**(б) Поправить слова.**

> Первое формализуемое по эту сторону границы — сама схема перехода между уровнями (функтор вложения
> `EmbedFunctor`, забывание `forget_obj` на забываемых системах и их сопряжение `level_adjunction`).

Если определения пункта (а) будут внесены — «(функторы `ForgetFunctor` и `EmbedFunctor` с их сопряжением на
забываемых системах)».

## Расхождение 5. «Аксиомы, на которые опирается работа с `Distinction` (`classic` и `L4_witness`)» (стр. 1204–1208)

**Было:**

> В последующей главе об аксиоматическом слое Rocq будут проговорены технические аксиомы, на которые опирается
> работа с `Distinction` (`classic` и `L4_witness`), и впервые развёрнут механизм, заменяющий Аксиому Выбора —
> передача статуса через E/R/R с применением $L4$ и $L5$.

**Проверка.** `Axiom classic : forall P : Prop, P \/ ~P` — `foundation/Distinction.v:36` (собственное объявление
файла; в выводе компилятора — `Distinction.classic`, отдельно от `Classical_Prop.classic` стандартной
библиотеки). `Axiom L4_witness : forall (A : Type) (P : A -> Prop), (exists x, P x) -> {x : A | P x}` —
`ToS_Axioms.v:105`; файл `ToS_Axioms.v` от `Distinction.v` не зависит.

`Print Assumptions` снят для всех теорем `foundation/Distinction.v` и 39 зависящих от него файлов (`pa39.txt`,
`pa_dp.cjs`): 499 теорем, из них 463 — Closed under the global context, 36 — `Distinction.classic`, ни одной с
`L4_witness`. Имя `L4_witness` в этих файлах встречается дважды, оба раза в комментариях
(`PrinciplesFromLaws.v:190`, `GaugeFromDistinctionSynthesis.v:39`).

**В чём расхождение.** Работа с `Distinction` в формализации опирается на одну аксиому — `classic`; `L4_witness`
в ней не участвует.

**(а) Довести формализацию.** Доводить нечего: теорем о `Distinction`, которым нужен свидетель, извлечённый из
существования, в формализации нет, и добавлять опору на аксиому ради слов страницы не следует.

**(б) Поправить слова.**

> В последующей главе об аксиоматическом слое Rocq будут проговорены технические аксиомы формализации — `classic`,
> на которую опирается работа с `Distinction`, и `L4_witness`, которая нужна дальше, при извлечении свидетеля, — и
> впервые развёрнут механизм, заменяющий Аксиому Выбора — передача статуса через E/R/R с применением $L4$ и $L5$.

## Расхождение 6. Типового класса `Inhabited` и модуля `Coq.Logic.Inhabited` в стандартной библиотеке нет; блок кода не собирается (стр. 587–603, далее по разделу)

**Было:**

> (593–603) В Rocq и в стандартной библиотеке `Coq.Logic.Inhabited` есть типовой класс, утверждающий, что
> некоторый тип *населён*, то есть имеет по крайней мере одного обитателя:
>
> ```coq
> Class Inhabited (X : Type) : Prop :=
>   inhabited_witness : X.
> ```
>
> (Точное определение в стандартной библиотеке немного отличается, используя `inhabits`, но для нашего обсуждения
> это несущественно.)

**Проверка** (Rocq 9.0.1):

- `Require Import Coq.Logic.Inhabited.` — «Cannot find a physical path bound to logical path
  Stdlib.Logic.Inhabited» (`CheckReq2.v`); то же для `From Stdlib Require Import Logic.Inhabited` (`CheckReq.v`);
- `Locate Inhabited.` — «No object of basename Inhabited»;
- блок страницы — «Error: Universe inconsistency. Cannot enforce … <= Prop» (`CheckClass.v`): поле типа `X : Type`
  не может составлять класс сорта `Prop`;
- в библиотеке есть индуктивный предикат (`Corelib.Init.Logic`; в прежних версиях `Coq.Init.Logic`):

```coq
Inductive inhabited (A : Type) : Prop :=  inhabits : A -> inhabited A.
```

Остальное в разделе проверено и соответствует: блок `some_type_inhabited` (стр. 632–636) собран дословно —
Closed under the global context; две формы записи-попытки (стр. 609–618, «или, эквивалентно») для библиотечного
`inhabited` равносильны — `inhabited_forms_equiv`, Closed under the global context.

**В чём расхождение.** Названного модуля и типового класса в Rocq нет, а приведённую запись система не принимает;
в библиотеке населённость выражена индуктивным предикатом `inhabited`. На ход рассуждения раздела это не влияет.

**(а) Довести формализацию.** В формализации исправлять нечего: речь о стандартной библиотеке. Если блокам кода
раздела нужен исходник в репозитории, в отдельный файл можно внести проверенные `some_type_inhabited` и
`inhabited_forms_equiv` (`Check.v`):

```coq
Lemma inhabited_forms_equiv :
  (exists X : Type, inhabited X) <-> (exists (X : Type) (x : X), True).
Proof.
  split.
  - intros [X [x]]. exists X. exists x. exact I.
  - intros [X [x _]]. exists X. exact (inhabits x).
Qed.
```

**(б) Поправить слова.** Имя `Inhabited` заменить на `inhabited` в заголовке подраздела и далее по разделу
(стр. 587, 589–591, 610, 646, 656, 663, 703); стр. 593–603 —

> В базовой библиотеке Rocq (модуль `Init.Logic`) есть индуктивный предикат, утверждающий, что некоторый тип
> *населён*, то есть имеет по крайней мере одного обитателя:
>
> ```coq
> Inductive inhabited (A : Type) : Prop :=
>   inhabits : A -> inhabited A.
> ```

Скобочное замечание стр. 602–603 после этого не нужно. Блок стр. 609–610 — `exists (X : Type), inhabited X`.

## Сомнительные места (расхождением не являются)

- **Стр. 1198–1200, «невозможно построить `Distinction`, имея лишь одну из сторон».** В смысле, который задаёт
  Глава 5 (нет терма типа `Distinction` без значения поля `negative`), это верно для всякой записи: конструктор
  `mkDistinction` принимает все четыре аргумента. Теоремы о невозможности в формализации нет. При этом
  `distinction_of` строит различение по одной пропозиции, достраивая вторую сторону как её отрицание, — ценой
  аксиомы `classic`. Содержательная форма того же утверждения доказуема без аксиом (`Check.v`):
  построить различение по одной заданной стороне для всякой пропозиции можно тогда и только тогда, когда выполнен
  закон исключённого третьего (`every_prop_distinguishes_iff_L3`, `negative_side_alone_iff_L3`).
- **Стр. 1166–1170, «общая запись `Distinction` шире».** По равенству полей — да. По содержанию — с точностью до
  равносильности нет: `negative D <-> ~ positive D` для всякого `D` (`negative_iff_not_positive`, Closed under the
  global context).
- **Стр. 1166–1168 и 1184, `distinction_of`.** Цена построения — аксиома `classic` — в этих местах не названа;
  общий список аксиом стоит на стр. 1204–1206. Слова «первый *явно конструктивный* объект тома» (стр. 1176)
  относятся к типу записи, который допущений не имеет; построение экземпляра по произвольной пропозиции
  конструктивным не является.
- **Стр. 646–648, «Чтобы доказать `Inhabited X`… нужен *конкретный обитатель*. Иначе доказательство
  невозможно».** Верно для CIC без аксиом. При аксиоме `classic`, принятой в формализации, населённость доказуема
  и от противного, без предъявления обитателя: `inhabited_by_contradiction : forall X, ~ ~ inhabited X ->
  inhabited X` (`Check.v`; `Print Assumptions`: `classic`).
- **Стр. 910, «Предложение „Структура границы"».** На стр. 685–706 то же положение названо «Утверждение» и
  сказано, что оно не доказывается формально. Слово «Предложение» читается как название доказанного результата.
- **Стр. 1229, «онтология положительно-отрицательного (Глава 4)».** Глава о со-определении в томе имеет номер 5
  (`05 Со-определение A и ¬ A.md`); глава 4 — «E/R/R: онтология системы».
- **Стр. 1253, «$\Sys(L_0), \Sys(L_1), …, \Sys(L_n)$».** Базовый уровень в формализации — `L1`
  (`TheoryOfSystems_Core_ERR.v:59`), уровня с номером 0 нет; в категории `SystemCat L1` нет объектов
  (`L1_criterion_absurd`, `SystemCategory.v:412`), первая населённая категория — `SystemCat (LS L1)`.
- **Стр. 1056–1070, 1128, 1185, «минимальная структура», «он минимален», «необходимость каждого поля».** В главе 1
  это тезис и анонс Главы 2; доказанным в Rocq он здесь не назван, поэтому не проверялся.
- **Стр. 1251, `RealProcess`.** Одно и то же определение `nat -> Q` объявлено в десяти файлах (и ещё раз внутри
  модуля в `TheoryOfSystems_Core_ERR.v:1341`); глава файла не называет. Все объявления совпадают.
- **Блоки кода стр. 528, 554, 609, 616 (`Axiom …`).** Инструмент отмечает «нет такого объявления» — так и должно
  быть: страница приводит их как отвергаемые попытки, в формализации их нет.
- **Стр. 1248, «через все 20 частей».** В томе 20 папок частей (01–20) — соответствует.

## Попутно — для проверки соседних глав

- `foundation/LawsFromDistinction.v:172`, `L3_independence : (forall D, positive D \/ negative D) -> (forall P,
  P \/ ~P)` — посылка в доказательстве не используется (`intros _ P. exact (classic P).`); `Print Assumptions`:
  `Distinction.classic`. Утверждение без посылки есть сама аксиома (ср. `record_L3_to_general_iff_L3` выше).
- `foundation/IndivisibleDistinction.v:28`, `all_four_necessary : forall P, exists D, positive D = P` — под именем
  о необходимости четырёх полей стоит утверждение `every_prop_distinguishes`; опирается на `Distinction.classic`.
- Глава 5, стр. 606–607: блок кода приводит прежнюю формулировку `co_constitution`; в исходнике
  (`Distinction.v:202`) сейчас `positive (distinction_of P) = P /\ negative (distinction_of P) = ~ P`.
- `foundation/PrimalityOfOne.v:40`, `one_from_distinction (D : Distinction) : nat := 1` — определение от аргумента
  не зависит.
- `foundation/DistinctionProcess.v:139`, `measurement_eventually_completes` — формулировка оставлена в файле и
  закрыта командой `Abort` (в счёт `Qed` и `Admitted` не входит).
- Шапка `LevelAdjunction.v` называет сопряжение «forget -| embed (left adjoint -| right adjoint)», тогда как
  доказанное соответствие морфизмов `embed_obj L S -> T` и `S -> forget_obj L T Hf` ставит слева вложение.
- В каталоге `src` лежит файл `TestNode.v` из одного слова `test`; `coqdep` на нём останавливается, в
  `_CoqProject` он не внесён.
