# Глава II.1 «Первичность единицы», вторая половина (стр. 971–1940, сноски 10–15) — заметки к ведомости (13.11.2026)

Ведомость: `part02-ch01b.json` — 30 ручных записей; `merge --dry` проходит без замечаний; в списке «без сверки»
остаются только имена первой половины главы (`one_is_first_from_existence`, `marked_greater_than_unmarked`,
`zero_is_absence`, `one_distinction_exists`, `two_distinctions_exist`, `zero_not_a_count`, `first_count_is_one`,
`tos_ordering`, `orderings_dual`, `distinction_asymmetric` — последнее стоит в сноске 4, знак которой на стр. 353).
Вердикты ручных записей: ok — 18, mismatch-statement — 7, missing-name — 5.

Двенадцать записей с расхождением относятся к пяти местам: две — о предикате счёта (расхождение 1), одна — об
описании `process_equiv` (расхождение 2), три — о теоремах про девятки (расхождение 3), одна — о паре
`distinction_order` (расхождение 4), пять — об именах из шапки файла (расхождение 5).

Участок: окончание исторического раздела (Плотин, Фреге, Кантор, Спенсер-Браун), разделы «Счёт как присутствие, а
не наращивание от нуля», «Делимость как акт», «Процесс и атом: о записи $0{,}999…$» с разбором E/R/R и итогом
главы, сноски 10–15 (их знаки стоят на стр. 1002, 1033, 1039, 1069, 1375, 1807). Блоков кода в участке нет. О
формализации участок говорит в шести местах: стр. 1090–1093, 1161–1164, 1241–1250, 1740–1773, 1800–1853 (со сноской
15), 1890–1891; остальной текст — слово автора и здесь не оценивался.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part02/ch01b/`: `Check.v` (равносильность предиката счёта
условию $1 \le n$; набросок счёта данного списка; `process_equiv` без сходимости и с ней; теоремы о девятках одной
связкой) и `Check2.v` (набросок добавления в конец `PrimalityOfOne.v` — с теми же подключениями, что у самого
файла). Оба собираются; все 34 ответа `Print Assumptions` — «Closed under the global context». В `src` и в собранной
копии ничего не менялось; файлы `foundation/PrimalityOfOne.v`, `foundation/AsymmetricDistinction.v`,
`foundation/Distinction.v`, `foundation/IndivisibleDistinction.v`, `foundation/L5_NatFromHierarchy.v`,
`process/ProcessCore.v`, `process/ProcessNinePoint.v`, `RealPointSetoid.v` в репозитории и в собранной копии
совпадают побайтно.

## Что проверить не удалось

- Первая половина главы (стр. 1–970) не сверялась: её проверяет другой помощник. Из неё прочитаны только § 1.3.3
  (стр. 496–634) и § 1.4.3 (стр. 780–887) — чтобы знать, как глава сама описывает предикат счёта и пару
  `distinction_order`, на которые ссылается вторая половина.
- Отсылки к другим главам и частям (Главы I.2, I.3, I.4, I.7; Главы II.2–II.5; Части III и IV) по содержанию не
  сверялись. Проверено только, что нумерация частей совпадает с сайтом (Часть III — рациональные числа, Часть IV —
  процессные действительные числа) и что разбор девяток в Части IV есть — Глава IV.3, § 3.7.
- Слова стр. 1269–1275 о том, что развернёт Глава II.2 («онтологический предикат счёта, лемма о реализуемости
  каждого числа, происхождение индукции из повторимости акта… получит там полный формальный аппарат»), — предмет
  ведомости главы II.2. Для неё существенно установленное здесь: лемма о реализуемости —
  `positive_nat_is_distinction_count : forall n, (1 <= n)%nat -> distinction_count_from_one n`
  (`PrimalityOfOne.v:94`; `Axioms: Classical_Prop.classic`), а её заключение равносильно её посылке (расхождение 1).
- Слова стр. 1872–1875 «все четыре [пути] начинаются с единицы» — предмет ведомостей глав II.2–II.5; проверен один
  факт (см. «Сомнительные места», п. 4).
- Утверждения о стандартной математике (три построения действительного числа, стр. 1641–1654; «в режиме
  действительных чисел равенство корректно», стр. 1662–1672) с формализацией не сверялись: в участке они не
  привязаны ни к одному объявлению.
- Исторические сведения (Плотин и Прокл, Фреге, Кантор, Спенсер-Браун; сноски 10–13) и пример с кварком (сноска
  14) вне предмета аудита.
- Наброски пункта «а» проверены как отдельные файлы против собранных модулей; в сами файлы `src` они не
  вставлялись, и общая сборка с ними не запускалась.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Предикат `distinction_count_from_one` равносилен условию $1 \le n$ и числа совершённых актов не фиксирует (стр. 1241–1250)

**Было:**

> **Согласие с предикатом счёта.** Наконец, картина присутствия — это прямое прочтение предиката
> `distinction_count_from_one` (§ 1.3.3). Этот предикат говорит: число $n$ *есть* в системе постольку, поскольку
> существует список из $n$ совершённых различий. Он не описывает накопления от нуля — он регистрирует *наличие*
> совершённых актов и их число. «Сосчитать» в смысле этого предиката есть в точности «установить, для какого $n$
> налицо список из $n$ различений». Картина присутствия — словесное выражение того, что предикат
> `distinction_count_from_one` выражает формально.

**Проверка.** `src/foundation/PrimalityOfOne.v:55`:

```coq
Definition distinction_count_from_one (n : nat) : Prop :=
  exists (Ds : list Distinction), length Ds = n /\ (1 <= n)%nat.
```

Closed under the global context. Список стоит под `exists`; условие на него одно — длина. Список нужной длины есть
всегда (достаточно $n$ раз повторить одно различение), поэтому первый конъюнкт ничего не ограничивает. В пробном
файле (`Check.v`):

```coq
Definition D_TF : Distinction :=
  mkDistinction True False (fun H => proj2 H) (or_introl I).

Lemma count_from_one_iff_positive : forall n : nat,
  distinction_count_from_one n <-> (1 <= n)%nat.
Proof.
  intro n. split.
  - intros [Ds [_ H]]. exact H.
  - intro H. exists (repeat D_TF n). split; [apply repeat_length | exact H].
Qed.

Lemma count_from_one_holds_for_all_positive :
  distinction_count_from_one 1 /\ distinction_count_from_one 2 /\
  distinction_count_from_one 5 /\ distinction_count_from_one 1000.
```

Обе леммы — Closed under the global context. Следствие для теорем файла о счёте: `first_count_is_one` (`:58`) по
содержанию есть $1 \le 1$; `succ_is_new_distinction` (`:84`) — $1 \le n \to 1 \le n + 1$ (`Check.v`,
`succ_is_new_distinction_content`); `positive_nat_is_distinction_count` (`:94`) — $1 \le n \to 1 \le n$. Все три
отвечают компилятору `Axioms: Classical_Prop.classic` — только потому, что свидетелем взято `distinction_of True`;
с другим свидетелем они закрыты (`Check.v`, `succ_is_new_distinction_closed`).

**В чём расхождение.** Предикат отвечает на вопрос «положительно ли $n$», а не на вопрос «сколько различений
совершено»: он верен сразу для всех $n \ge 1$, и ни совершённые акты, ни их число в него не входят. Из двух вещей,
о которых говорит абзац, — «счёт начинается с единицы» и «счёт фиксирует число наличных актов» — формально он
выражает первую.

**(а) Довести формализацию.** Возможно, без аксиом. Нужно отношение между *данным* списком совершённых различений
и числом; тогда «нуль не есть счёт наличного» становится следствием наличия акта, а не приписанным условием.
Набросок проверен (`Check2.v`; подключения — те же, что у `PrimalityOfOne.v`, так что его можно дописать в конец
этого файла; все восемь ответов — Closed under the global context):

```coq
Definition counts (Ds : list Distinction) (n : nat) : Prop := length Ds = n.

Definition counts_from_one (Ds : list Distinction) (n : nat) : Prop :=
  Ds <> [] /\ length Ds = n.

Theorem counts_functional : forall Ds n m, counts Ds n -> counts Ds m -> n = m.

Theorem presence_starts_at_one : forall Ds n, counts_from_one Ds n -> (1 <= n)%nat.
Proof.
  intros Ds n [Hne Hlen].
  destruct Ds as [| D Ds']; [exfalso; apply Hne; reflexivity | simpl in Hlen; lia].
Qed.

Theorem zero_counts_nothing_present : forall Ds, ~ counts_from_one Ds 0%nat.

Theorem every_count_starts_with_one : forall Ds : list Distinction, Ds <> [] ->
  exists (D : Distinction) Ds', Ds = Ds' ++ [D] /\ counts_from_one [D] 1%nat.

Theorem from_one_iff_some_present_list : forall n,
  distinction_count_from_one n <-> exists Ds, counts_from_one Ds n.
```

Здесь у данного списка число одно (`counts_functional`); единица как нижняя граница получена из непустоты списка
(`presence_starts_at_one`); всякий счёт наличного начат одним актом со счётом один
(`every_count_starts_with_one`); прежний предикат оказывается утверждением «у некоторого непустого списка такой
счёт» (`from_one_iff_some_present_list`). Счёт данного списка в формализации уже есть — `distinction_count_nat
(Ds : list Distinction) : nat := length Ds` (`src/foundation/IndivisibleDistinction.v:93`) с леммами
`one_distinction` (`:118`), `distinction_increment` (`:111`), `count_is_natural` (`:98`), все Closed; глава на этот
файл не ссылается. Оговорка: число при этом остаётся значением `nat` — длиной списка; набросок связывает число с
предъявленными актами, а типа чисел из различений не строит.

**(б) Поправить слова:**

> **Согласие с предикатом счёта.** Наконец, картина присутствия согласована с предикатом
> `distinction_count_from_one` (§ 1.3.3). Этот предикат говорит: число $n$ *есть* в системе постольку, поскольку
> существует список из $n$ совершённых различий и $n \ge 1$. Он не описывает накопления от нуля; формально он
> равносилен условию $n \ge 1$ и потому выражает одно — границу: счёт наличного начинается с единицы. Саму
> фиксацию — какое число отвечает *данным* совершённым актам — выражает длина предъявленного списка: «сосчитать»
> есть «установить длину списка совершённых различений». Картина присутствия — словесное выражение этих двух
> формальных фактов: числом служит длина наличного списка, и нуль в счёт наличного не входит.

Если принят пункт «а», последние две фразы можно дать с именем: «…выражает отношение `counts_from_one` между
списком совершённых различений и числом; из наличия хотя бы одного акта следует $n \ge 1$
(`presence_starts_at_one`)».

## Расхождение 2. `process_equiv` описано как отношение процессов, «сходящихся к одному пределу» (стр. 1748–1750)

**Было:** «…и отношение `process_equiv` (обозначаемое `~~`), которое связывает два процесса, *сходящихся к одному
пределу*;»

**Проверка.** `src/process/ProcessCore.v:170`:

```coq
Definition process_equiv (R1 R2 : RealProcess) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (R1 n - R2 n) < eps.
```

Closed under the global context. Определение говорит о разности двух процессов: с ростом стадии она уходит ниже
всякой точности. Сходимости ни одного из процессов оно не требует, и слова «предел» в нём нет. Слова страницы
повторяют комментарий над определением (`:169`, «Two processes are equivalent if they converge to the same limit»).
В пробном файле (`Check.v`, все — Closed under the global context):

```coq
Definition stage_process : RealProcess := fun n => inject_Z (Z.of_nat n).   (* 0, 1, 2, 3, … *)

Lemma equiv_does_not_require_convergence :
  stage_process ~~ stage_process /\ ~ is_Cauchy stage_process.

Lemma stage_process_has_no_rational_limit :
  forall q : Q, ~ (stage_process ~~ const_process q).

Theorem equiv_iff_same_limit_when_one_converges : forall (R1 R2 : RealProcess) (q : Q),
  R1 ~~ const_process q -> (R1 ~~ R2 <-> R2 ~~ const_process q).
```

**В чём расхождение.** Отношение шире описанного: оно связывает и процессы, которые никуда не сходятся (всякий
процесс — с самим собой). Для процессов, имеющих рациональный предел, слова страницы точны — это третья лемма; для
пары «девятки и единица» (стр. 1761–1764) они тоже точны.

**(а) Довести формализацию.** Определение менять незачем: оно то же, что `cauchy_equiv`, и Глава IV.3 читает его
как «разность приближений уходит ниже всякого $\varepsilon$». Чтобы у слов «сходятся к одному пределу» была теорема,
достаточно добавить в `ProcessCore.v` три леммы из пробного файла — `same_limit_gives_equiv`,
`equiv_transfers_limit`, `equiv_iff_same_limit_when_one_converges`; каждая доказывается из `process_equiv_sym` и
`process_equiv_trans` в одну строку.

**(б) Поправить слова:**

> …и отношение `process_equiv` (обозначаемое `~~`), которое связывает два процесса, *расхождение которых с ростом
> стадии уходит ниже всякой точности* — для сходящихся процессов это и значит: *сходятся к одному пределу*;

## Расхождение 3. «Теорем о девятках в репозитории пока нет» — обе теоремы есть (стр. 1757–1759, 1768–1773)

**Было:**

> (1757–1759) В этом языке позиция ToS по поводу $0{,}999…$ формулируется точно — и это удобный мост к будущей
> формализации.
>
> (1768–1773) Формальная проверка этой картины — через теоремы вида «процесс девяток не поточечно равен
> `const_process` $1$» и «процесс девяток `process_equiv` `const_process` $1$» — относится к Части IV;
> `ProcessCore.v` даёт для неё готовый язык, но самих этих теорем о девятках в репозитории пока нет.

**Проверка.** Файл `src/process/ProcessNinePoint.v` (8 `Qed`; в репозитории с 01.06.2026, коммит dac7f92; дополнен
12.11.2026 при аудите Части IV):

```coq
Definition nine_raw : RealProcess := fun n => 1 - 1 / ten_pow (S n).     (* :66 *)

Lemma nine_raw_lt_one : forall n, nine_raw n < 1.                        (* :72 *)

Theorem nine_equiv_one : nine_raw ~~ const_process 1.                    (* :84 *)

Theorem nine_raw_is_Cauchy : is_Cauchy nine_raw.                         (* :114 *)

Theorem nine_process_equiv_one : cauchy_equiv nine_process one_process.  (* :150 *)
```

`Print Assumptions` для каждого из пяти объявлений: Closed under the global context. Формула `nine_raw` — та же,
что на стр. 1760: $n \mapsto 1 - 1/10^{n+1}$ (`nine_raw 0 == 9 # 10`, `:122`; значения $99/100$ и $999/1000$ на
следующих стадиях проверены в `Check.v`). Вся картина стр. 1757–1768 собрана в пробном файле одной теоремой
(Closed under the global context):

```coq
Theorem nines_three_modes :
  (forall n : nat, nine_raw n < const_process 1 n) /\
  (forall n : nat, ~ (nine_raw n == const_process 1 n)) /\
  nine_raw ~~ const_process 1.
```

Том эти теоремы уже разбирает: Глава IV.3, § 3.7 («Формальное доказательство: файл `ProcessNinePoint.v`»).

**В чём расхождение.** Страница отстала от формализации: о проверенном она говорит как о предстоящем.

**(а) Довести формализацию.** Не требуется: формализация содержит больше, чем названо. При желании к файлу можно
добавить связку `nines_three_modes` и лемму `nines_not_pointwise_equal` (обе в `Check.v`) — тогда «не поточечно
равен» получит теорему с дословно такой формулировкой.

**(б) Поправить слова:**

> (1757–1761) В этом языке позиция ToS по поводу $0{,}999…$ формулируется точно — и в репозитории уже проверена.
> Запись $0{,}999…$ отвечает процессу $n \mapsto 1 - 1/10^{ n+1}$ (в файле `src/process/ProcessNinePoint.v` —
> `nine_raw`); единица отвечает постоянному процессу `const_process` $1$.
>
> (1768–1773) Формальная проверка этой картины в репозитории есть — файл `ProcessNinePoint.v`: теорема
> `nine_raw_lt_one` (на каждой стадии процесс девяток строго меньше единицы) и теорема `nine_equiv_one` (процесс
> девяток `process_equiv` `const_process` $1$), обе без аксиом; их разбор относится к Части IV (Глава IV.3).

## Расхождение 4. Порядок «$1$ прежде $0$» «опирается» на пару, вписанную рукой (стр. 1808–1813)

**Было:**

> Оговорка о статусе: «система» здесь — содержательная интерпретация; `one_from_distinction` машинно проверяет
> *выбранную регистрацию* (каждому различению — отпечаток $1$), а не *доказывает* первичность, и онтологический
> порядок «$1$ прежде $0$» опирается на `distinction_order` (§ 1.2, § 1.4).

**Проверка.** `src/foundation/AsymmetricDistinction.v:126–130`:

```coq
Definition distinction_order := (1%nat, 0%nat).  (* marked first, unmarked second *)

Theorem one_precedes_zero_in_distinction :
  fst distinction_order = 1%nat /\ snd distinction_order = 0%nat.
Proof. split; reflexivity. Qed.
```

Оба объявления — Closed under the global context. Определение есть пара двух чисел; запись `Distinction` и
определения `mark`, `unmark` в него не входят. Теорема возвращает компоненты пары. Поиск по `src`: имя
`distinction_order` встречается только в этих двух строках — ни одна теорема на него не опирается. Первая часть той
же фразы названа точно: `one_from_distinction (D : Distinction) : nat := 1` (`PrimalityOfOne.v:40`) — константа, от
`D` не зависящая, а `one_is_first_from_existence` (`:46`) закрыта `reflexivity`.

**В чём расхождение.** Оговорка называет регистрацией одно из двух определений-констант, а о втором говорит как об
опоре порядка. Статус у них один: пара $(1, 0)$ — запись порядка, а не его вывод. В первой половине главы это
сказано точнее: «порядок обоснования, записанный как объект» (стр. 800–801).

**(а) Довести формализацию.** Для самой пары — нельзя по существу: что бы ни доказывалось о паре $(1, 0)$, это
будет утверждение о написанной рукой записи; порядок обоснования не есть отношение на `nat`, которое можно было бы
получить теоремой из записи `Distinction`. Содержательная часть тезиса — «единица есть первый счёт наличного, нуль
есть отсутствие актов» — доказуема без аксиом на счёте данного списка (расхождение 1, `Check2.v`):
`presence_starts_at_one` (всякий счёт наличного не меньше единицы), `every_count_starts_with_one` (всякий непустой
список начат одним актом со счётом один), `zero_from_absence` (счёт нуль — в точности у пустого списка). На эти
теоремы порядок мог бы опираться в прямом смысле слова.

**(б) Поправить слова:**

> Оговорка о статусе: «система» здесь — содержательная интерпретация; `one_from_distinction` машинно проверяет
> *выбранную регистрацию* (каждому различению — отпечаток $1$), а не *доказывает* первичность, и онтологический
> порядок «$1$ прежде $0$» в репозитории тоже *записан*, а не выведен — парой `distinction_order` (§ 1.2, § 1.4).

## Расхождение 5 (имена). `one_is_first`, `succ_from_distinction`, `zero_from_absence`, `ToS_nat` — слова из шапки файла, объявлений нет (стр. 1816–1819, 1837–1838, 1852)

**Было:**

> (1816–1819) Конституция — правило регистрации: первый акт различения отмечается единицей (`one_is_first`), всякое
> следующее различение даёт следующее число (`succ_from_distinction`); нуль — из отсутствия различения
> (`zero_from_absence`), а не из счёта.
>
> (1837–1838) Элементы — сами акты различения, которые счёт и пересчитывает (`ToS_nat` — счёт, основанный на
> различениях).
>
> (1852) | акты различения (`ToS_nat`) | носители (конечны, $P4$) | Element |

**Проверка.** Шапка `src/foundation/PrimalityOfOne.v:2–4`:

```
    Elements: ToS_nat, primality of 1, distinction-based counting
    Roles:    1 = first distinction, 0 = absence of distinction
    Rules:    one_is_first, zero_from_absence, succ_from_distinction
```

Поиск по `src` и `Architecture_of_Reasoning`: каждое из четырёх слов встречается только в этих строках комментария;
объявлений с такими именами нет (`Locate` в собранной копии: «No object of basename …»). Ближайшие объявления
файла:

| слово шапки | что объявлено | утверждение | допущения |
|---|---|---|---|
| `one_is_first` | `one_is_first_from_existence` (`:46`) | `forall D : Distinction, one_from_distinction D = 1%nat` — `reflexivity` на константе; слова «первый» в утверждении нет | Closed |
| `succ_from_distinction` | `succ_is_new_distinction` (`:84`) | `forall n, distinction_count_from_one n -> distinction_count_from_one (S n)` — по расхождению 1 это $1 \le n \to 1 \le n + 1$ | `Classical_Prop.classic` |
| | `add_distinction_increments` (`:79`) | `forall Ds D, length (add_distinction Ds D) = S (length Ds)` | Closed |
| `zero_from_absence` | `zero_from_no_distinction` (`:43`), `zero_is_absence` (`:51`) | `zero_from_no_distinction : nat := 0`; `zero_from_no_distinction = 0%nat` — `reflexivity` на константе | Closed |
| `ToS_nat` | — | своего типа чисел в файле нет: числа — значения `nat`, пересчитываемое — `list Distinction` | — |

**В чём расхождение.** Три правила и носитель названы в обратных кавычках, как имена формализации; в файле это
слова комментария. Пересказ шапки на стр. 1804–1807 при этом точен.

**(а) Довести формализацию.** Для трёх правил — возможно, без аксиом: дать именам шапки теоремы с содержанием.
Набросок проверен (`Check2.v`, Closed under the global context):

```coq
Theorem one_is_first : forall D : Distinction,
  counts_from_one [D] 1%nat /\ (forall n, counts_from_one [D] n -> n = 1%nat).
Proof.
  intro D. split.
  - split; [discriminate | reflexivity].
  - intros n [_ H]. simpl in H. lia.
Qed.

Theorem succ_from_distinction : forall Ds (D : Distinction) n,
  counts_from_one Ds n -> counts_from_one (D :: Ds) (S n).
Proof.
  intros Ds D n [_ H]. split; [discriminate | simpl; rewrite H; reflexivity].
Qed.

Theorem zero_from_absence : forall Ds : list Distinction, counts Ds 0%nat <-> Ds = [].
Proof.
  intro Ds. unfold counts. split.
  - destruct Ds; [reflexivity | discriminate].
  - intro H. subst. reflexivity.
Qed.
```

Первая говорит: один совершённый акт, каким бы ни было различение, считается единицей и только ею; вторая —
следующее различение (любое, а не `distinction_of True`) даёт следующее число; третья — счёт нуль в точности у
пустого списка. Для `ToS_nat` честного содержания нет: отдельный тип чисел файлу не нужен, и глава сама настаивает,
что тип `nat` не переопределяется (стр. 1822–1824, 1890–1891). Слово лучше убрать из шапки и со страницы.

**(б) Поправить слова** (если формализацию не трогать):

> (1816–1819) Конституция — правило регистрации: первый акт различения отмечается единицей
> (`one_is_first_from_existence`), всякое следующее различение даёт следующее число (`succ_is_new_distinction`);
> нуль — из отсутствия различения (`zero_is_absence`), а не из счёта (`zero_not_a_count`).
>
> (1837–1838) Элементы — сами акты различения, которые счёт и пересчитывает (список `list Distinction` — счёт,
> основанный на различениях).
>
> (1852) | акты различения (`list Distinction`) | носители (конечны, $P4$) | Element |

При этом варианте сила названных теорем остаётся такой, как в таблице выше (`zero_not_a_count : ~
distinction_count_from_one 0`, `PrimalityOfOne.v:65`, Closed under the global context — по расхождению 1 это
$\neg (1 \le 0)$); оговорка о статусе на стр. 1808–1813 это покрывает.

## Сомнительные места (не расхождения)

1. **Стр. 992 и 1066–1067, «выводя её из устройства акта различения», «различению, из которого ToS число и
   выводит».** Формализация в этих местах не названа, это слово автора. Для сведения: в `PrimalityOfOne.v` число не
   выводится из записи `Distinction` — единица приписана определением-константой, числа суть значения `nat`
   стандартной библиотеки; сама глава говорит это на стр. 1810–1812.
2. **Стр. 1810, «машинно проверяет».** `one_from_distinction` — определение; проверкой служит теорема
   `one_is_first_from_existence`, закрытая `reflexivity`. Точнее было бы «задаёт *выбранную регистрацию*».
3. **Стр. 1820–1821, «(`distinction_order`, § 1.2.3)».** В § 1.2.3 носителем асимметрии названы `mark`, `unmark`
   и `marked_greater_than_unmarked`; `distinction_order` там стоит только в сноске 3, основное место — § 1.4 (стр.
   787–841).
4. **Стр. 1872–1875, «все четыре [пути] начинаются с единицы».** В файле иерархического пути базовому уровню
   отвечает нуль: `level_to_nat LBase = O` (`src/foundation/L5_NatFromHierarchy.v:17`, лемма `peano_zero`, `:52`).
   Как это согласовано со словами о начале с единицы — вопрос к главе II.3.
5. **Стр. 1709–1718 и 1764–1767, «классы эквивалентности», «классы по `process_equiv`».** Фактортипа в
   формализации нет; «класс» там — отношение эквивалентности на процессах: `process_equiv_Equivalence :
   Equivalence process_equiv` (`src/RealPointSetoid.v:61`, Closed). Слова «эти классы совпадают» формально означают
   `nine_raw ~~ const_process 1`. Глава IV.3 говорит об этом прямо («фактортип не построен»); здесь оговорки нет.
6. **Стр. 1702–1707, «множества и классы эквивалентности суть… режим рассмотрения».** Формальная опора схемы
   «список → мультимножество → множество» есть — `src/settheory/ListModes.v` (10 `Qed`, добавлен при аудите Части
   I); она о списках, не о классах процессов. Глава на файл не ссылается.
7. **Стр. 1456–1469, уровень списка.** Слова «удлинить список — значит присоединить к нему ещё одно различие»
   отвечают леммам `add_distinction_increments` (`PrimalityOfOne.v:79`) и `distinction_increment`
   (`IndivisibleDistinction.v:111`); раздел о делимости формализацию не называет.
8. **Сноска 15 (стр. 1932), «асимметрия „единица прежде нуля“ — в `AsymmetricDistinction.v`».** Файл назван
   верно; по содержанию это пара `distinction_order` (расхождение 4).
9. **Стр. 1745, «ядро этого аппарата».** Имя `RealProcess` объявлено в `src` десять раз (`ProcessCore.v:34` и
   девять местных копий); страница называет файл, так что неоднозначности нет.

## Вне главы: шапки и состав файлов

Для сведения (в участке эти строки не цитируются):

- `PrimalityOfOne.v:6` — «STATUS: 20 Qed», `primality_theorem_count := 20` (`:176`); действительный счёт `Qed` —
  15. Там же «0 new axioms»: четыре теоремы файла (`first_count_is_one`, `succ_is_new_distinction`,
  `positive_nat_is_distinction_count`, `primality_summary`) отвечают `Axioms: Classical_Prop.classic` — из-за
  свидетеля `distinction_of True`.
- `PrimalityOfOne.v:156`, `primality_summary` — конъюнкция пяти утверждений; первые два закрыты `reflexivity` на
  константах, пятое (`one_generates_Q`, `:121`) есть разбор значения типа `Q` на числитель и знаменатель — единица
  в его формулировку не входит.
- `AsymmetricDistinction.v:6` — «STATUS: 25 Qed», `asymmetric_distinction_theorem_count := 25` (`:207`);
  действительный счёт — 17.
- `ProcessCore.v:6` и `:20` — «STATUS: 25 Qed»; действительный счёт — 19.
- `ProcessNinePoint.v:27` — «STATUS: 8 Qed»; действительный счёт — 8.

## Дополнительные проверки

- `Print Assumptions` снят для всех объявлений, названных в записях ведомости, и для соседних: в
  `PrimalityOfOne.v` — 14 объявлений (четыре на `Classical_Prop.classic`, перечислены выше; остальные Closed); в
  `AsymmetricDistinction.v` — `distinction_order`, `one_precedes_zero_in_distinction`,
  `marked_greater_than_unmarked` (Closed); в `ProcessCore.v` — `process_equiv_refl`, `process_equiv_sym`,
  `process_equiv_trans`, `equiv_cauchy_l`, `const_equiv_const` (Closed); в `ProcessNinePoint.v` — шесть объявлений
  (Closed); `process_equiv_Equivalence` (Closed); в `IndivisibleDistinction.v` — `distinction_count_nat`,
  `one_distinction`, `distinction_increment`, `count_is_natural` (Closed). Третьего имени аксиомы ни в одном ответе
  нет.
- Счёт `Qed` (`grep -c 'Qed\.'`): `PrimalityOfOne.v` — 15, `AsymmetricDistinction.v` — 17, `Distinction.v` — 20,
  `ProcessCore.v` — 19, `ProcessNinePoint.v` — 8, `IndivisibleDistinction.v` — 18, `RealPointSetoid.v` — 7. Чисел
  такого рода в участке нет.
- Слов о цене («без аксиом», «на classic», число аксиом) в участке нет; сноска 4 о `classic` относится к первой
  половине главы.
- Библиотека `Reals` в `src` не подключается (поиск по строкам подключений); слова стр. 1783–1785 «ToS не строит
  $\mathbb{R}$ как готовое множество» формализации не противоречат.
- Пересказ шапки файла на стр. 1804–1807 сверен со строками 2–4 `PrimalityOfOne.v` построчно.
