# Глава II.1 «Первичность единицы», первая половина (стр. 1–970 и сноски 1–9) — заметки к ведомости (13.11.2026)

Ведомость: `part02-ch01a.json` — 72 ручные записи; `merge --dry` проходит без замечаний, список «без сверки»
пуст (четыре автоматические записи `missing-name` — `one_is_first`, `succ_from_distinction`, `zero_from_absence`,
`ToS_nat` — стоят на стр. 1817–1852, во второй половине главы). Вердикты ручных записей: ok — 63,
mismatch-statement — 8, mismatch-price — 1.

Девять записей с расхождением относятся к четырём местам (расхождения 1–4): одна — о цене теоремы
`distinction_asymmetric`, четыре — о двух предикатах счёта, три — о парах порядков, одна — о теореме
`tos_ordering`. Мелкие несовпадения блоков кода и одно разорванное имя собраны отдельным разделом.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part02/ch01a/`; все четыре собираются, `Axiom`,
`Parameter`, `Admitted` в них нет:

- `Check.v` — основной: цена `P <> ~P`, несовместность посылок `marked_greater_than_unmarked`, сторона как роль,
  два предиката счёта, счёт по предъявленному списку, пары порядков, перестановка сторон;
- `CheckAsym.v` — доказательство `distinction_asymmetric` без `classic` в окружении самого файла
  `AsymmetricDistinction.v`;
- `CheckCount.v` — блок о счёте предъявленного в окружении файла `PrimalityOfOne.v`;
- `CheckBlock.v` — блоки кода страницы в окружении файла `AsymmetricDistinction.v`.

В `src` и в собранной копии ничего не менялось.

Участок называет три файла `src/foundation/`: `AsymmetricDistinction.v` (17 `Qed`), `Distinction.v` (20),
`PrimalityOfOne.v` (15). Для проверки слов главы прочитаны ещё `DistinctionCoDefinition.v` (40),
`IndivisibleDistinction.v` (18), `LevelNatIso.v` (15), `L5_NatFromHierarchy.v` (15).

## Что проверить не удалось

- Вторая половина главы (стр. 971–1915) не читалась; из неё взяты только сноски, чтобы отнести каждую к месту
  её знака. Сноски 10–15 (знаки на стр. 1002–1807) в ведомость не вошли.
- Отсылки к другим главам сверены только в нужной для этого участка мере: Глава II.2 действительно разбирает
  предикат `distinction_count_from_one` (её слова сверяются в её ведомости); для слов об изоморфизме (Глава II.3)
  проверено наличие и цена лемм; отсылки к Главам I.2, I.6, I.7, II.5 проверены поиском по словам
  (см. «Сомнительные места», п. 9).
- Общее утверждение стр. 725–731 («каким бы он ни был… не может не быть изоморфен стандартному натуральному
  ряду») в общем виде внутри Rocq не формулировалось; проверен названный пример.
- Слова о стандартной библиотеке («тысячи доказанных лемм», стр. 716–718) не проверялись.
- Исторические сведения (§ 1.5 до стр. 970, сноски 7–9) вне предмета аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1 (цена). `distinction_asymmetric`: аксиома названа «формальным следом закона», а утверждению она не нужна (сноска 4, знак на стр. 353; стр. 347)

**Было** (стр. 1921):

> Доказательство `distinction_asymmetric` опирается на аксиому `classic` — техническое свидетельство $L3$ в CIC
> (Глава I.6). Это уместно: утверждение «$P$ и $\neg P$ не совпадают» есть утверждение об *определённости*
> различия, а определённость различия и есть то, что $L3$ обеспечивает. Здесь `classic` работает не как
> привнесённое допущение, а как формальный след структурного закона акта различения.

**Проверка.** `src/foundation/AsymmetricDistinction.v:92`:

```coq
Theorem distinction_asymmetric : forall P : Prop,
  positive (distinction_of P) <> positive (swap_distinction (distinction_of P)).
Proof.
  intro P. simpl.
  intro H.
  destruct (classic P) as [Hp | Hnp].
  - assert (Hnp : ~P) by (rewrite <- H; exact Hp).
    exact (Hnp Hp).
  - assert (Hp : P) by (rewrite H; exact Hnp).
    exact (Hnp Hp).
Qed.
```

`Print Assumptions distinction_asymmetric`: `Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P`. Первое
предложение сноски нынешнему доказательству соответствует. Но утверждение после раскрытия определений есть
`P <> ~P`, и оно верно без допущений: из `P = ~P` получается `~P` (если `P`, то по равенству `~P`, противоречие),
а из `~P` по тому же равенству — `P`. Та же формулировка, слово в слово, доказана без аксиомы (`CheckAsym.v`):

```coq
Theorem distinction_asymmetric' : forall P : Prop,
  positive (distinction_of P) <> positive (swap_distinction (distinction_of P)).
Proof.
  intro P. change (P <> ~ P). intro H.
  assert (np : ~ P).
  { intro p. assert (np : ~ P) by (rewrite <- H; exact p). exact (np p). }
  apply np. rewrite H. exact np.
Qed.
```

`Print Assumptions distinction_asymmetric'`: Closed under the global context. Общая форма — для всякого
различения, а не только канонического — уже есть в формализации: `sides_distinct : forall D : Distinction,
positive D <> negative D` (`src/foundation/DistinctionCoDefinition.v:125`, Closed under the global context); она
следует из полей `exclusive` и `exhaustive`. В пробном файле из неё получены `forall D, positive D <> positive
(swap_distinction D)` и `forall D, swap_distinction D <> D` (оба Closed).

Замечание о выводе компилятора: теорема, полученная из общей формы подстановкой `distinction_of P`
(`CheckAsym.v`, `distinction_asymmetric''`), снова показывает `classic` — оттого, что в терм доказательства
входит само `distinction_of`, построенное на `classic P`. Это цена определения, а не рассуждения.

**В чём расхождение.** Сноска объясняет присутствие аксиомы существом утверждения; проверка показывает, что
аксиома стоит только в выбранном тексте доказательства. «$P$ и $\neg P$ не совпадают» закон $L3$ не привлекает.

**(а) Довести формализацию.** Возможно, без аксиом: заменить текст доказательства в `AsymmetricDistinction.v:94–104`
приведённым выше (новых подключений не нужно; собирается в окружении этого файла). К нему можно добавить общую
форму, тоже проверенную в окружении файла (`CheckAsym.v`, Closed):

```coq
Theorem swap_changes_positive_of_any : forall D : Distinction,
  positive D <> positive (swap_distinction D).
Proof.
  intros D H. change (positive D = negative D) in H.
  destruct (exhaustive D) as [p | n].
  - apply (exclusive D). split; [exact p | rewrite <- H; exact p].
  - apply (exclusive D). split; [rewrite H; exact n | exact n].
Qed.
```

После замены комментарий в блоке страницы (стр. 347) и сноску 4 нужно поправить в любом случае.

**(б) Поправить слова.** Стр. 347: `Proof. (* ... *) Qed.` (если доказательство заменено) либо оставить как есть
(если нет). Сноска 4:

> Нынешнее доказательство `distinction_asymmetric` в репозитории использует аксиому `classic` — техническое
> свидетельство $L3$ в CIC (Глава I.6), — но само утверждение её не требует: «$P$ и $\neg P$ не совпадают»
> доказывается без допущений. В общей форме — для всякого различения — различность сторон есть теорема
> `sides_distinct` (файл `DistinctionCoDefinition.v`): она следует из двух правил записи, несовместности ($L2$)
> и исчерпанности ($L3$ для сторон). Закон $L3$ участвует здесь как правило самой записи, а не как аксиома
> `classic`.

## Расхождение 2. Два предиката счёта описаны как ответы на вопросы о списке и о совершённых актах; в Rocq оба — свойства числа, а исключение нуля вписано в определение (стр. 498–499, 573–577, 581–582; также 615–617)

**Было:**

> (498–499) Граничный статус нуля имеет точное формальное следствие, и оно важно для всей Части II: *нуль не
> входит в счёт различений*.
>
> (573–577) `distinction_count` отвечает на вопрос *технический*: какова длина данного списка различий? Длина
> есть характеристика списка как структуры данных, и пустой список — полноправная структура с длиной нуль. Этот
> предикат нужен везде, где речь идёт о списках как таковых: о длинах, индексах, конкатенациях.
>
> (581–582) `distinction_count_from_one` отвечает на вопрос *онтологический*: сколько актов различения
> *совершено*?
>
> (615–617) Технический `distinction_count` останется там, где он уместен: в работе со списками как структурами
> данных.

**Проверка.** `src/foundation/Distinction.v:161` и `src/foundation/PrimalityOfOne.v:55, 65`:

```coq
Definition distinction_count (n : nat) : Prop :=
  exists (Ds : list Distinction), length Ds = n.

Definition distinction_count_from_one (n : nat) : Prop :=
  exists (Ds : list Distinction), length Ds = n /\ (1 <= n)%nat.

Theorem zero_not_a_count : ~ distinction_count_from_one 0.
Proof. intro H. destruct H as [_ [_ Hge]]. lia. Qed.
```

Оба предиката принимают число, а не список; список стоит под квантором существования, и годится любой.

- `distinction_count n` верен при всяком `n`: `distinction_count_any` (`Distinction.v:182`,
  `Classical_Prop.classic` — свидетелем взято `distinction_of True`; без аксиом — `Check.v`,
  `distinction_count_any_closed`, со свидетелем `distinction_true_false`).
- `distinction_count_from_one n` равносилен `1 <= n`: `count_from_one_iff_ge_one` (`Check.v`, Closed under the
  global context). В формализации обратная сторона — `positive_nat_is_distinction_count`
  (`PrimalityOfOne.v:94`, `Classical_Prop.classic`).
- Ни один из двух не зависит от того, что список составлен из различений: `count_from_one_any_type : forall (A :
  Type) (a : A) (n : nat), (exists l : list A, length l = n /\ 1 <= n) <-> 1 <= n` (`Check.v`, Closed).
- `zero_not_a_count` закрывается одним условием `1 <= 0`, вписанным в определение; список и свойства различений
  в доказательстве не участвуют (первые две компоненты отброшены). Это страница говорит сама (стр. 537–538,
  556–557).
- Употребление: `distinction_count` встречается в пяти леммах своего файла (`Distinction.v:164–187`) и больше
  нигде в `src`; `distinction_count_from_one` — только в `PrimalityOfOne.v`. С длинами и конкатенациями списков
  различений в формализации работает другое объявление — функция `distinction_count_nat (Ds : list Distinction)
  : nat := length Ds` (`src/foundation/IndivisibleDistinction.v:93`) с теоремами `count_is_natural` (длина
  конкатенации есть сумма длин), `distinction_increment`, `zero_distinctions`, `one_distinction` (все Closed).

Слова стр. 512–513 («он спрашивает лишь, существует ли список различий заданной длины») и стр. 567–568
(«различаются лишь судьбой нуля») формализации соответствуют: при `n <> 0` предикаты равносильны
(`counts_differ_only_at_zero`, `Check.v`, Closed).

**В чём расхождение.** Вопросы «какова длина данного списка» и «сколько актов совершено» обращены к списку;
предикаты же говорят о числе: первый верен всегда, второй означает «`n` не меньше единицы». Исключение нуля во
втором не получено из чего-либо, а задано условием определения; и там, где страница отводит
`distinction_count` работу с длинами и конкатенациями, формализация пользуется другой функцией.

**(а) Довести формализацию.** Возможно, без аксиом: перенести условие с числа на список — «в списке предъявлен
хотя бы один акт» — и получить исключение нуля теоремой. Блок проверен в окружении файла `PrimalityOfOne.v`
(`CheckCount.v`; пять теорем — Closed under the global context):

```coq
Definition presented (Ds : list Distinction) : Prop := Ds <> nil.

Theorem presented_iff_count_ge_one : forall Ds : list Distinction,
  presented Ds <-> (1 <= length Ds)%nat.

Theorem zero_iff_nothing_presented : forall Ds : list Distinction,
  length Ds = 0%nat <-> Ds = nil.

Theorem presented_count_starts_at_one :
  (forall Ds : list Distinction, presented Ds -> (1 <= length Ds)%nat) /\
  (forall D : Distinction, presented [D] /\ length [D] = 1%nat).

Theorem count_from_one_iff_presented_witness : forall n : nat,
  distinction_count_from_one n <->
  exists Ds : list Distinction, presented Ds /\ length Ds = n.

Theorem zero_is_not_a_presented_count :
  ~ exists Ds : list Distinction, presented Ds /\ length Ds = 0%nat.
Proof.
  intros [Ds [Hp H0]]. apply Hp. exact (proj1 (zero_iff_nothing_presented Ds) H0).
Qed.
```

С ними слова главы получают опору: нуль есть счёт того и только того списка, в котором не предъявлено ничего
(`zero_iff_nothing_presented` — «локальная граница» стр. 472–478); счёт предъявленного начинается с единицы
(`presented_count_starts_at_one`); условие `1 <= n` прежнего определения равносильно условию на сам список
(`count_from_one_iff_presented_witness`); нуль не есть счёт предъявленного уже следствием
(`zero_is_not_a_presented_count`). Определение `distinction_count_from_one` при этом не меняется. К тому же
блоку можно добавить характеристику двух предикатов как свойств числа — `count_from_one_iff_ge_one` и
`counts_differ_only_at_zero` (в окружении файла — на `classic` через свидетеля `distinction_of True`; без
аксиом — со свидетелем `distinction_true_false` из `DistinctionCoDefinition.v`, как в `Check.v`).

Чего довести нельзя: зависимости счёта от свойств различений. Длина списка одинакова для списков над любым
типом; то, что считаются именно акты различения, в формулировках выражено только типом элементов.

**(б) Поправить слова:**

> (498–499) Граничный статус нуля имеет точное формальное выражение, и оно важно для всей Части II: *нуль не
> входит в счёт различений*.
>
> (573–577) `distinction_count` отвечает на вопрос *технический*: есть ли список различий данной длины? Длина
> есть характеристика списка как структуры данных, и пустой список — полноправная структура с длиной нуль;
> поэтому ответ положителен при всяком числе, включая нуль. Этот предикат говорит о списках как таковых;
> длину данного списка, её поведение при конкатенации в репозитории даёт функция `distinction_count_nat`
> (файл `IndivisibleDistinction.v`).
>
> (581–582) `distinction_count_from_one` отвечает на вопрос *онтологический*: может ли данное число быть счётом
> *совершённых* актов различения?
>
> (615–617) Технический `distinction_count` останется там, где он уместен: в утверждениях о длинах списков как
> структур данных.

Если блок пункта (а) внесён, фразу стр. 498–499 можно оставить без правки («следствие» станет верным словом),
добавив после стр. 557 одно предложение: «То же получается и следствием, без условия на число: список нулевой
длины пуст, а в пустом списке ничего не предъявлено (`zero_is_not_a_presented_count`)».

## Расхождение 3. «Различённость двух порядков зафиксирована формально», «пара $(1,0)$ против пары $(0,1)$ содержится в `AsymmetricDistinction.v`» — в файле одна пара-константа (стр. 786–789, 830–833; сноска 5, знак на стр. 836)

**Было:**

> (786–789) В репозитории оба порядка присутствуют явно, и их различённость зафиксирована формально. Файл
> `AsymmetricDistinction.v` определяет порядок различения — порядок, в котором маркированная сторона идёт прежде
> немаркированной:
>
> (830–833) Поэтому *формальная* запись двойственности двух порядков как пары $(1,0)$ против пары $(0,1)$
> содержится именно в `AsymmetricDistinction.v` — в `distinction_order` и `one_precedes_zero_in_distinction`
>
> (сноска 5) …её следовало бы переписать через `tos_conceptual_ordering` $:= (1,0)$ и `number_ordering`
> $:= (0,1)$, как уже сделано для `distinction_order` в `AsymmetricDistinction.v`.

**Проверка.** `src/foundation/AsymmetricDistinction.v:121–130`:

```coq
(** ★ 1 PRECEDES 0 in the order of distinction.
    "Something" (1, marked) is prior to "nothing" (0, unmarked).
    This is NOT the usual natural number ordering (0 < 1).
    This is the DISTINCTION ordering (marked before unmarked). *)

Definition distinction_order := (1%nat, 0%nat).  (* marked first, unmarked second *)

Theorem one_precedes_zero_in_distinction :
  fst distinction_order = 1%nat /\ snd distinction_order = 0%nat.
Proof. split; reflexivity. Qed.
```

Обе — Closed under the global context. `distinction_order` есть пара чисел, вписанная рукой; от записи
`Distinction`, от `mark` и `unmark` она не зависит. Теорема читает две компоненты этой пары. Пары $(0,1)$ в файле
нет; утверждения, сопоставляющего пару с числовым порядком или отличающего один порядок от другого, нет ни в
этом файле, ни в `PrimalityOfOne.v` (там числовой порядок записан неравенством: `numerical_ordering : (0 < 1)%nat`,
`:136`). Различие двух порядков названо в комментарии над определением.

**В чём расхождение.** Формально записан один объект — пара $(1,0)$. «Различённость» и «двойственность» двух
порядков, о которых говорит страница, в теоремы не входят; пары $(0,1)$, с которой пара $(1,0)$ сопоставлена, в
репозитории нет. Слова сноски «как уже сделано» относятся к половине предложенного.

**(а) Довести формализацию.** Записать вторую пару и теорему об их соотношении можно, без аксиом (`Check.v`, все —
Closed under the global context):

```coq
Definition tos_conceptual_ordering : nat * nat := (1, 0).
Definition number_ordering : nat * nat := (0, 1).

Theorem distinction_order_is_conceptual : distinction_order = tos_conceptual_ordering.

Theorem orderings_dual_pairs :
  fst tos_conceptual_ordering = snd number_ordering /\
  snd tos_conceptual_ordering = fst number_ordering /\
  tos_conceptual_ordering <> number_ordering.
```

Это доводит формализацию до слов стр. 830–833 и сноски 5: две пары записаны, они зеркальны и различны. Обе
пары при этом остаются вписанными рукой, и теорема есть свойство этих двух записей. Пару $(1,0)$ можно связать
со счётом: `distinction_order = (length [D], length (@nil Distinction))` для всякого `D` (`Check.v`,
`distinction_order_from_counts`, Closed) — первая компонента есть счёт списка из одного акта, вторая — счёт
пустого списка.

Довести до теоремы сам порядок обоснования («единица обосновывает нуль») честно нельзя: в записи `Distinction`
стороны входят взаимно (`sides_codetermined`, `DistinctionCoDefinition.v:85`: каждая сторона равносильна
отрицанию другой), перестановка сторон определена для всякого различения, а «дана» и «выведена» — свойства
способа построения `distinction_of`, которые утверждением о записи не выражаются. Пара остаётся регистрацией
прочтения — как и говорит о ней страница на стр. 799–801.

**(б) Поправить слова:**

> (786–789) В репозитории оба порядка присутствуют явно: числовой — неравенством $0 < 1$, порядок различения —
> парой; их различённость названа в комментарии к определению пары. Файл `AsymmetricDistinction.v` записывает
> порядок различения — порядок, в котором маркированная сторона идёт прежде немаркированной, — так:
>
> (830–833) Поэтому *формальная* запись онтологического порядка как пары $(1,0)$ содержится именно в
> `AsymmetricDistinction.v` — в `distinction_order` и `one_precedes_zero_in_distinction` (пара $(0,1)$ числового
> порядка отдельным объектом в репозитории не записана: числовой порядок представлен неравенством $0 < 1$), — а
> `PrimalityOfOne.v` регистрирует ту же мысль в более слабой форме: …
>
> (сноска 5) …её следовало бы переписать через `tos_conceptual_ordering` $:= (1,0)$ и `number_ordering`
> $:= (0,1)$ — по образцу `distinction_order` в `AsymmetricDistinction.v`, где пара $(1,0)$ уже записана.

## Расхождение 4. `tos_ordering` названа задающей порядок обоснования; она утверждает числовой порядок $0 < 1$ (стр. 866–867)

**Было:** «…`tos_first`, отмечающее единицу как первую распознаваемую величину; `tos_absence`, читающее нуль как
границу; `tos_ordering`, задающее порядок обоснования.»

**Проверка.** `src/foundation/PrimalityOfOne.v:141–145`:

```coq
Definition tos_first := 1%nat.
Definition tos_absence := 0%nat.

Theorem tos_ordering : (tos_absence < tos_first)%nat.
Proof. unfold tos_absence, tos_first. lia. Qed.
```

Closed under the global context. Утверждение конвертируемо в `0 < 1`: равенство `(tos_absence < tos_first) =
(0 < 1)` закрывается рефлексивностью (`Check.v`, `tos_ordering_is_numerical_ordering`). Сама страница сорока
строками выше читает теорему так же: «по существу $0 < 1$» (стр. 823–826).

**В чём расхождение.** Порядок обоснования, по главе, направлен от единицы к нулю; `tos_ordering` утверждает,
что нуль меньше единицы, — это числовой порядок, который страница от порядка обоснования отличает.

**(а) Довести формализацию.** Не требуется и по существу невозможно (см. расхождение 3, пункт «а»): теоремы
о порядке обоснования, не сводящейся к записи вписанных рукой чисел, сформулировать не удаётся. Если нужна
формальная запись пары, она дана в расхождении 3.

**(б) Поправить слова:**

> …`tos_first`, отмечающее единицу как первую распознаваемую величину; `tos_absence`, читающее нуль как границу;
> `tos_ordering`, сохраняющее при этом чтении числовой порядок $0 < 1$.

## Блоки кода и имена (мелкие несовпадения)

1. **Стр. 559–560, разорванное имя.** Имя `first_count_is_one` разбито переносом строки внутри обратных кавычек
   (`first_count` / `_is_one`) и на странице читается с пробелом. Стало: имя целиком на одной строке.
2. **Стр. 543–546 и 556–557, текст доказательства `zero_not_a_count`.** На странице:
   `intros [Ds [_ H]]. inversion H.` и слова «`inversion` это закрывает». В файле (`PrimalityOfOne.v:67–69`):
   `intro H. destruct H as [_ [_ Hge]]. lia.` — тактики `inversion` нет. Вариант страницы собирается (`Check.v`,
   `zero_not_a_count_page`, Closed). Стало (если держаться исходника): блок по файлу и слова «условие $1 \le 0$
   ложно, и `lia` это закрывает».
3. **Стр. 548–552, текст доказательства `first_count_is_one`.** На странице: `exists (cons (distinction_of True)
   nil). split. reflexivity. apply le_n.`; в файле (`:60–63`): `exists [distinction_of True]. split; [reflexivity |
   lia].` Тот же свидетель; вариант страницы собирается.
4. **Стр. 517–518, `zero_distinctions`.** На странице `Theorem` и `exists nil`; в файле (`Distinction.v:164`)
   `Lemma` и `exists []`. Утверждение то же.
5. **Стр. 254–255, `mark` и `unmark`.** Имя второго аргумента на странице `h`, в файле `holds_positive` и
   `holds_negative`.
6. **Стр. 508–509, 533–534.** Скобки вокруг связанной переменной и пометка `%nat` в файле; на странице их нет.
7. **Стр. 792–795, `distinction_order`.** На странице `Definition distinction_order : nat * nat := (1, 0).` и
   равенства без пометок; в файле `Definition distinction_order := (1%nat, 0%nat).` и `= 1%nat`, `= 0%nat`. Тип
   тот же (`Check distinction_order : nat * nat`). В окружении файла, где после `QArith` открыта область
   `Q_scope`, дословный текст страницы не собирается: «The term "(1, 0)" has type "(Q * Q)%type" while it is
   expected to have type "(nat * nat)%type"» (`CheckBlock.v`).
8. **Стр. 287–296, предложенный блок `DistinctionSide`.** В том же окружении строка `side_value Unmarked <
   side_value Marked.` не собирается: «The term "side_value Unmarked" has type "nat" while it is expected to have
   type "Q"». С пометкой `(side_value Unmarked < side_value Marked)%nat` блок собирается (`CheckBlock.v`,
   Closed). При внесении блока в файл пометку нужно добавить; на странице достаточно оставить как есть, если блок
   читается как набросок.

Блоки, совпадающие с исходником: `one_from_distinction`, `one_is_first_from_existence` (стр. 143–147),
`positive_is_given`, `negative_depends_on_positive` (221–227), `marked_greater_than_unmarked` (257–259, включая
доказательство), `distinction_asymmetric` (344–346, формулировка), `before`, `after`, `before_after_exclusive`,
`before_after_exhaustive` (370–376), `zero_from_no_distinction`, `zero_is_absence` (456–459), `zero_not_a_count`,
`first_count_is_one` (формулировки), `tos_first`, `tos_absence`, `tos_ordering`, `orderings_dual` (810–818, включая
доказательства).

## Сомнительные места (не расхождения)

1. **Стр. 161–162, «проверяет его непротиворечивость».** Код, о котором идёт речь, — определение-константа и
   теорема, которая после раскрытия определения есть `1 = 1`. Утверждения о непротиворечивости прочтения в файле
   нет; определение, не зависящее от аргумента, противоречия дать и не может. Статус в целом назван честно
   («регистрирует», «не теоремой»). Точнее: «код регистрирует выбранное прочтение, но обосновывается это
   прочтение…».
2. **Стр. 211–214, 233–234, 335–357, асимметрия сторон.** Формальное содержание файла в этой части: две леммы
   о сторонах `distinction_of P` (верны по определению), `distinction_asymmetric` (`P <> ~P`), константы `mark` и
   `unmark`. Сама запись `Distinction` относительно перестановки сторон симметрична: `swap_distinction` определена
   для всякого `D` и дважды применённая возвращает те же стороны (`swap_involution_positive`,
   `swap_involution_negative`); каждая сторона равносильна отрицанию другой (`sides_codetermined`,
   `DistinctionCoDefinition.v:85`, Closed); для всякой `P` есть и зеркальная запись, где `P` стоит на
   отрицательной стороне, а `~P` — на положительной (`swap_distinction (distinction_of P)`; `Check.v`,
   `mirrored_canonical_distinction`). Слова «обратное неверно» (стр. 234) и «определительная первичность есть
   свойство устройства различения, а не выбор того, кто на различие смотрит» (стр. 355–357) относятся к способу
   построения `distinction_of`; как утверждение о записи они в формализации не выражены. Теорема стр. 344
   доказывает названное на стр. 340–341 — перестановка даёт другое различение, — причём в общем виде это верно
   для всякого `D` и без аксиом (расхождение 1).
3. **Стр. 269–282, `marked_greater_than_unmarked`.** Страница верно отмечает, что доказательства обеих сторон
   одного различения одновременно невозможны. Следствие, которое на странице не названо: при таких посылках
   доказуемо любое заключение, в том числе обратное неравенство — `forall D p n, mark D p < unmark D n`
   (`Check.v`, `marked_less_than_unmarked_too`, Closed). Доказательство в файле посылок не использует: `mark` и
   `unmark` от аргументов не зависят, и теорема есть `0 < 1`. Содержательные формы с выполнимыми посылками —
   `mark D p = 1`, `unmark D n = 0` по отдельности и сравнение сторон двух различений
   (`marked_gt_unmarked_two_distinctions`, с примером) — проверены там же. Возможное добавление к стр. 280–282:
   «…при несовместных посылках она верна при любых числах, и потому сама приоритета не устанавливает».
   Связь роли с записью, которой в предложенном блоке стр. 287–296 нет, проверена в `Check.v`: `side_holds D s`
   (какая сторона выполнена) и `exactly_one_side_holds : forall D, exists s, side_holds D s /\ forall s',
   side_holds D s' -> s' = s` (Closed) — у всякого различения выполнена ровно одна роль-сторона.
4. **Стр. 350–353, «переход к различию $\neg P$».** У `swap_distinction (distinction_of P)` стороны `~P` и `P`; у
   `distinction_of (~P)` — `~P` и `~~P`. Положительные стороны совпадают, отрицательные равносильны ценой
   `classic` (`Check.v`, `swap_vs_distinction_of_neg`; снятие двойного отрицания для всех `P` равносильно
   исключённому третьему — `double_negation_elimination_is_EM`, Closed). Как записи они не равны. Слова верны
   с точностью до этой равносильности.
5. **Стр. 448–478, «в данном списке, на данной стадии».** `zero_from_no_distinction` — константа `0` без
   аргументов: ни списка, ни стадии в определении нет, и страница это читает точно. Формальной опорой слов о
   «рассматриваемом списке» служит другая лемма, которую глава не называет: `zero_distinctions :
   distinction_count_nat nil = 0%nat` (`IndivisibleDistinction.v:115`, Closed) — счёт пустого списка; обратная
   сторона («счёт нуль — только у пустого списка») проверена в `CheckCount.v` (`zero_iff_nothing_presented`).
6. **Стр. 466–471, населённость типа.** Леммы `one_distinction_exists` и `two_distinctions_exist` стоят на
   `Classical_Prop.classic`: свидетелем взято `distinction_of True`. Цены страница здесь не называет. Тип населён
   и без аксиом: `distinction_exists_without_axiom` (`DistinctionCoDefinition.v:321`, Closed), свидетель —
   `distinction_true_false`.
7. **Стр. 138–148, единица при акте.** Наряду с константой `one_from_distinction` в формализации есть
   вычисляемая форма, которую глава не называет: `one_distinction : forall D : Distinction, distinction_count_nat
   (D :: nil) = 1%nat` (`IndivisibleDistinction.v:118`, Closed) — единица как счёт списка из одного акта.
   Константа с ней согласована: `one_from_distinction D = distinction_count_nat [D]` (`Check.v`, рефлексивность).
8. **Стр. 395–396, «Шапка файла».** Слова о времени и веществе стоят в комментарии после шапки (строки 34–35
   файла): «structural asymmetry propagates to matter/antimatter (η > 0), time (arrow), counting (1 before 0)».
   Это комментарий; страница говорит «отмечает».
9. **Отсылки к Части I.** Стр. 578–579 и 763–765 ссылаются на Главу I.6 как на место, где введён «слой
   синтаксиса» и проведено различение порядка построения и порядка обоснования. В Главе I.6 «Три слоя формальной
   работы» — это слой A (платформа CIC), слой B (свидетельства $L3$ и $L4$), слой C (определения и теоремы ToS);
   слов «слой синтаксиса», «слой онтологии», «порядок обоснования» на страницах Части I поиском не найдено.
   Стр. 239 и 317 называют Главу I.2 при словах «со-определение сторон»; со-определению посвящена Глава I.5,
   Глава I.2 о нём упоминает и отсылает вперёд. Отсылка стр. 310 к Главе I.7 (позитивная онтология)
   подтверждается.
10. **Стр. 725–731 и 879–881, тип `Level`.** Объявлений `Level` в формализации пять. Для типа ядра
    (`TheoryOfSystems_Core_ERR.v:59`) взаимно обратные отображения с `nat` доказаны в `LevelNatIso.v:43, 46`, для
    отдельной копии — в `L5_NatFromHierarchy.v:29, 32` (все Closed). Какой из файлов называет Глава II.3 —
    предмет её ведомости.

## Вне главы: шапки и состав файлов

Для сведения (в этом участке главы эти строки не цитируются):

- `AsymmetricDistinction.v:6` — «STATUS: 25 Qed»; действительный счёт 17. `asymmetric_distinction_theorem_count :=
  25` (`:207`).
- `PrimalityOfOne.v:6` — «STATUS: 20 Qed»; действительный счёт 15. `primality_theorem_count := 20` (`:176`).
  Шапка называет элементы и правила `ToS_nat`, `one_is_first`, `zero_from_absence`, `succ_from_distinction`:
  объявлений с такими именами в файле нет.
- «0 new axioms» в обеих шапках: `distinction_asymmetric`, `asymmetric_distinction_summary`
  (`AsymmetricDistinction.v`); `first_count_is_one`, `succ_is_new_distinction`,
  `positive_nat_is_distinction_count`, `primality_summary` (`PrimalityOfOne.v`) — `Classical_Prop.classic`. Во
  всех случаях, кроме `distinction_asymmetric`, аксиома приходит через свидетеля `distinction_of True`.
- `AsymmetricDistinction.v:59`, `negation_presupposes_affirmation : forall A : Prop, ~A -> exists B, B = A` —
  посылка отбрасывается (`intros A _`), заключение верно без неё.
- `AsymmetricDistinction.v:133`, `positive_has_content : positive D -> exists witness : positive D, True` —
  свидетелем служит сама посылка.
- `AsymmetricDistinction.v:153`, `direction_stable` — `x = x`; `:178`, `asymmetry_inherent` — три равенства по
  рефлексивности, из них два вида `x = x`.
- `PrimalityOfOne.v:84`, `succ_is_new_distinction` — «новое различение» в доказательстве есть то же
  `distinction_of True`, добавленное в список ещё раз; список может состоять из равных элементов.
- `PrimalityOfOne.v:121`, `one_generates_Q : forall q : Q, exists n d, q = n # d` — разбор значения типа `Q` на
  числитель и знаменатель; единица в утверждение не входит.
- Имя `zero_distinctions` носят две леммы с разными утверждениями: `Distinction.v:164` (`distinction_count 0`) и
  `IndivisibleDistinction.v:115` (`distinction_count_nat nil = 0%nat`).
- `MatterAsymmetry.v:89–97` — единственное употребление `unmark` и `marked_greater_than_unmarked` вне своего
  файла; `one_from_distinction`, `zero_from_no_distinction`, `tos_first`, `tos_absence`, `distinction_order`
  вне своих файлов не употребляются.

## Дополнительные проверки

- Файлы `Distinction.v`, `AsymmetricDistinction.v`, `PrimalityOfOne.v`, `DistinctionCoDefinition.v`,
  `IndivisibleDistinction.v` в репозитории и в собранной копии совпадают побайтно.
- Счёт `Qed` (`grep -c 'Qed\.'`): `AsymmetricDistinction.v` — 17, `PrimalityOfOne.v` — 15, `Distinction.v` — 20.
  Чисел такого рода в этом участке страницы нет.
- `Print Assumptions` снят для всех названных в участке объявлений. Closed under the global context:
  `one_from_distinction`, `one_is_first_from_existence`, `positive_is_given`, `negative_depends_on_positive`,
  `mark`, `unmark`, `marked_greater_than_unmarked`, `swap_distinction`, `swap_changes_positive`, `before`, `after`,
  `before_after_exclusive`, `before_after_exhaustive`, `zero_from_no_distinction`, `zero_is_absence`,
  `distinction_count`, `zero_distinctions`, `distinction_count_from_one`, `zero_not_a_count`, `distinction_order`,
  `one_precedes_zero_in_distinction`, `tos_first`, `tos_absence`, `tos_ordering`, `orderings_dual`,
  `numerical_ordering`. `Classical_Prop.classic`: `distinction_asymmetric`, `one_distinction_exists`,
  `two_distinctions_exist`, `first_count_is_one`. Третьего имени в выводе компилятора нет; `L4_witness` не
  встречается.
- Ответ `Print nat`: `Inductive nat : Set := O : nat | S : nat -> nat.` — блоки стр. 41 и 682 совпадают
  с точностью до записи типов конструкторов.
- Имена без объявления, стоящие в участке: `DistinctionSide`, `side_value`, `Marked`, `Unmarked`,
  `marked_role_gt_unmarked_role` (сноска 3 говорит, что их нет), `tos_conceptual_ordering`, `number_ordering`
  (сноска 5 говорит то же). Поиск по `src` это подтверждает.
- Слова страницы о теореме `orderings_dual` (стр. 827–830: оба конъюнкта сводятся к $0 < 1$) и об определениях
  `one_from_distinction`, `zero_from_no_distinction` (стр. 150–166, 462–478) формализации соответствуют: статус
  в этих местах назван точно.
