# Глава VIII.1 «Задача Коши и решение как процесс» — заметки к ведомости (18.11.2026)

Ведомость: `part08-ch01.json` — 46 ручных записей + 3 автоматические (упоминания файлов `ProcessODE.v`,
`stdlib/ODE.v`, `analysis/PicardLindelof.v`); `merge --dry` проходит без замечаний, список «без сверки» пуст.
Вердикты ручных записей: ok — 23, mismatch-price — 12, mismatch-statement — 11. Имён без объявления и неверных
чисел нет.

Двадцать три записи с расхождением относятся к семи местам: двенадцать записей цены — к расхождению 1 (слова
«Коши-сходимость наследует `classic`»); из одиннадцати записей формулировки одна — к расхождению 2
(`banach_fixed_point`), три — к расхождению 3 (опущенная посылка ограниченности), три — к расхождению 4
(«существование решения» при теореме о скалярном шаге), одна — к расхождению 5 (`ode_is_process`), две — к
расхождению 6 («на пространстве функций»), одна — к расхождению 7 (шапки файлов).

Глава называет шесть файлов: `src/FixedPoint.v` (20 `Qed`), `src/stdlib/ODE.v` (22),
`src/analysis/PicardLindelof.v` (23), `src/process/ProcessODE.v` (20), `src/process/ProcessPicard.v` (32),
`src/process/ProcessPicardOperator.v` (11). Все шесть прочитаны целиком; строк `Axiom`, `Parameter`, `Admitted`
в них нет. Для всех 176 объявлений этих файлов (определения и утверждения) снят `Print Assumptions` — каждое
«Closed under the global context» (`PA.v`). Исходники в репозитории и в собранной копии совпадают (`cmp`).
Единственное число главы — «22 доказанных утверждения» в `stdlib/ODE.v` — верно.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part08/ch01/`:

- `status.txt` — вывод `tom-status.cjs chapter 08/01`;
- `PA.v`, `PA.out` — `Print Assumptions` всех объявлений шести файлов;
- `Check.v`, `Check.out` — пробные доказательства, разделы 1–7 по местам главы. Собирается; из 47 команд
  `Print Assumptions` 45 дают «Closed under the global context» (девять имён главы, `Qpow_limit_zero` и 35
  новых утверждений), две — `Classical_Prop.classic` (`Qpow_cauchy`, `geometric_series_cauchy`: взяты для
  сравнения, см. расхождение 1);
- `checklines.cjs` — сверка номеров строк ведомости со страницей (46 записей, несовпадений нет).

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Отсылки к другим главам и частям по содержанию не сверялись — это предмет их ведомостей. Сверены адреса:
  Главы 8.2–8.5 — «Метод Эйлера: решение на сетке», «Пикар–Линделёф: оператор-сжатие на пространстве функций»,
  «Устойчивость, единственность, неравенство Гронуолла», «Экспонента, линейные уравнения, применения»; Часть III,
  Глава 4 — «От позиции к процессу»; Глава 4.3 — «Точка как класс эквивалентности процессов»; Глава 7.1 —
  «Ортонормированные системы и коэффициенты Фурье»; Часть V содержит главы «Интеграл» и «Основная теорема
  анализа»; `integral_process` введён в Главе V.5 как «интеграл-процесс».
- Как сама Глава 8.3 описывает `ProcessPicardOperator.v`, не сверялось. Расхождение 6 и п. 1 сомнительных мест
  касаются того же файла и должны решаться вместе с ведомостью Главы 8.3.
- Предложенные дополнения проверены как пробный файл поверх собранных модулей (`Check.v`); как файл `src` с
  записью в `_CoqProject` они не собирались.
- Переход по измельчению (стадия $N$ интеграла-процесса или шаг сетки $h \to 0$) не пробовался: доказано
  Коши-свойство итераций при каждой фиксированной стадии; что роль-пределы при разных стадиях сближаются
  (сходимость метода Эйлера), остаётся недоказанным (расхождение 4, пункт «а»).
- Не проверялось, служит ли свидетель `picard_error_bound M L h n` из доказательства `ode_is_process` оценкой
  ошибки скалярной итерации: в утверждении теоремы от него требуется только неотрицательность.
- Сведения о классической математике (теоремы Пикара–Линделёфа и Пеано; значение $e^{1/2} \approx 1{,}6487$,
  с которым в расхождении 4 сравнивается предел скалярной итерации) в Rocq не проверялись.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Коши-сходимость наследует `classic` через `Qpow_vanish`»: по компилятору она доказана без аксиом (стр. 55–58, 62, 228–230; сноски 2, 6, 7)

**Было:**

> (55–58) В текущем формальном слое сам переход от геометрического убывания итератов к их *Коши-сходимости* и
> к завершённому пределу наследует закон исключённого третьего (L3); это честно отмечается там, где
> используется, и не маскируется под конструкцию.[^2]
>
> (62) …доказаны точно, без аксиом; Коши-свойство наследует `classic` (сноски 2 и 6).
>
> (228–230) …сама Коши-сходимость и завершённый предел в текущем формальном слое наследуют L3 через
> `Qpow_vanish` и честно помечаются по `Print Assumptions`.
>
> (сноска 2) Банахова теорема о неподвижной точке (`banach_fixed_point`) и Коши-сходимость итератов
> (`iterate_is_cauchy`) в `FixedPoint.v` наследуют `classic` через лемму о затухании $c^n$ (`Qpow_vanish`) —
> шапка файла отмечает это прямо, и в нём стоят `Print Assumptions` для обеих. … Стержень главы — именно это
> различие: алгебра сжатия и зазор строятся без аксиом, переход к завершённому пределу — L3-слой.
>
> (сноска 6) Переход от сжатия к самой *Коши-сходимости* итератов (`euler_picard_cauchy` там же;
> `iterate_is_cauchy` в `FixedPoint.v`) идёт через лемму о затухании $c^n$ (`Qpow_vanish`) и потому наследует
> `classic`. Иными словами, «приближения образуют процесс Коши» распадается на конструктивную алгебру сжатия и
> L3-зависимый предельный переход — что и проверяется `Print Assumptions`.
>
> (сноска 7) …а явная обёртка «итераты $\to$ завершённое решение» честно отнесена к этому L3-слою.

**Проверка.** Вывод компилятора (`tom-pa.cjs`; повторено в `Check.v`, раздел 8, и в `PA.v`):

```
Qpow_vanish               (src/SeriesConvergence.v:164)        Closed under the global context
iterate_is_cauchy         (src/FixedPoint.v:263)               Closed under the global context
banach_fixed_point        (src/FixedPoint.v:386)               Closed under the global context
euler_picard_cauchy       (src/process/ProcessPicard.v:206)    Closed under the global context
euler_picard_contraction  (src/process/ProcessPicard.v:165)    Closed under the global context
```

`Qpow_vanish` (`forall r eps, 0 < r -> r < 1 -> 0 < eps -> exists N, Qpow r N < eps`) доказана через
неравенство Бернулли (`bernoulli_ineq`) и архимедовость (`nat_archimedean`); теоремой о монотонной сходимости
она не пользуется. Доказательство `iterate_is_cauchy` идёт через телескопическую оценку `iterate_diff_bound` и
`Qpow_vanish` (`FixedPoint.v:290`) — оба без аксиом. Ни одно из 176 объявлений шести файлов главы аксиом не
использует.

`classic` в слое рядов действительно есть, но в других леммах: `Qpow_cauchy` (`SeriesConvergence.v:232`),
`geometric_series_cauchy` (`:389`), `comparison_test` (`:404`) — они опираются на теоремы о монотонной
ограниченной последовательности из `MonotoneConvergence.v` (`q_inc_bounded_cauchy`, `:134`:
`Classical_Prop.classic`). Файлы главы ими не пользуются.

Шапка `FixedPoint.v` (`:12`: «AXIOMS: classic (inherited from MonotoneConvergence via Qpow_vanish)») называет
цену по подключённым модулям; команды `Print Assumptions iterate_is_cauchy` и `Print Assumptions
banach_fixed_point` в файле стоят (`:730`, `:731`), и обе дают «Closed under the global context». Теоремы о
завершённом пределе (с допущением `classic` или без него) в названных файлах нет; «явной обёртки» в
`ProcessPicardOperator.v` тоже нет — о ней говорит только комментарий (`:20–22`, `:230–233`).

**В чём расхождение.** Страница называет цену по шапке файла, а компилятор показывает, что Коши-сходимость
итератов доказана без аксиом; шага к завершённому пределу в формальном слое нет вовсе, так что L3 в нём не
используется.

**(а) Довести формализацию до слов главы.** Не требуется: формализация здесь сильнее слов главы. Стоит
поправить комментарии в исходниках (см. раздел «Вне главы»). Обёртка, о которой говорит комментарий
`ProcessPicardOperator.v`, доказывается без аксиом — `Check.v`, разделы 4 и 5:

```coq
(* Номер K зависит только от r, C, eps -- общий для всех последовательностей с таким зазором. *)
Theorem geom_gap_modulus : forall (r C eps : Q),
  0 <= r -> r < 1 -> 0 <= C -> 0 < eps ->
  exists K : nat, forall a : nat -> Q,
    (forall n, Qabs (a (S n) - a n) <= Qpow r n * C) ->
    forall m n, (K <= m)%nat -> (K <= n)%nat -> Qabs (a m - a n) < eps.

Corollary geom_gap_is_cauchy : forall (a : nat -> Q) (r C : Q),
  0 <= r -> r < 1 -> 0 <= C ->
  (forall n, Qabs (a (S n) - a n) <= Qpow r n * C) -> is_cauchy a.

(* Итерации сеточного оператора Пикара -- процесс Коши равномерно по узлам k <= N. *)
Theorem picard_iter_sup_cauchy : forall (f : Q -> Q -> Q) (L : Q),
  0 < L ->
  (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) ->
  forall (h : Q), 0 <= h -> forall (y0 : Q) (N : nat),
  L * Tlen h N < 1 ->
  forall eps, 0 < eps ->
  exists K : nat, forall m n, (K <= m)%nat -> (K <= n)%nat ->
    forall k, (k <= N)%nat ->
      Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps.
```

Доказательство `geom_gap_modulus` — телескопическая оценка `(1 - r) * |a m - a n| <= C * (r^n - r^m)`
(`geom_gap_tel`, индукция по `m`) и лемма `Qpow_limit_zero` (`SeriesConvergence.v:261`, без аксиом);
`picard_iter_sup_cauchy` получается из `picard_iter_gap` и `geom_gap_modulus`, первый зазор берётся как
`gmax` по узлам. Все три — «Closed under the global context». (На сетке верно и большее: итерации приходят к
решению за конечное число шагов — расхождение 4, пункт «а».)

**(б) Поправить слова.**

Стр. 55–58:

> В текущем формальном слое переход от геометрического убывания итератов к их *Коши-сходимости* доказан без
> аксиом; к завершённому пределу формальный слой не переходит вовсе — предел остаётся ролью, и это честно
> отмечается, а не маскируется под конструкцию.[^2]

Стр. 62:

> …доказаны точно, без аксиом, как и Коши-свойство итераций (сноски 2 и 6).

Стр. 226–231:

> *Существование решения — роль-свойство процесса: сходится ли он. Доказано конструктивно (0 аксиом) — алгебра
> сжатия, геометрический зазор итератов (Глава 8.3, `picard_iter_gap`) и сама Коши-сходимость итераций
> скалярного шага (`euler_picard_cauchy`; лемма о затухании `Qpow_vanish` аксиом не требует — `Print
> Assumptions`: «Closed under the global context»). Завершённого предела формальный слой не строит: он —
> роль-предел, не актуализируемый как функция-объект.*

Сноска 2:

> Коши-сходимость итератов (`iterate_is_cauchy`) в `FixedPoint.v` и запись итератов как процесса Коши
> (`banach_fixed_point`) аксиом не требуют: лемма о затухании $c^n$ (`Qpow_vanish`) доказана через неравенство
> Бернулли и архимедовость, и `Print Assumptions` для обеих даёт «Closed under the global context» (шапка
> файла, называющая `classic`, отстала от компилятора). Так же без аксиом — алгебраическая оценка *сжатия*
> (`euler_picard_contraction`, `ProcessPicard.v`) и — в расширенном слое Главы 8.3 — *геометрический зазор*
> итератов и *единственность* решения на сетке (`picard_iter_gap`, `picard_unique` в
> `ProcessPicardOperator.v`). Стержень главы — различие иного рода: сжатие, зазор и Коши-свойство суть
> утверждения о рациональных стадиях и строятся без аксиом; перехода к завершённому пределу как объекту в
> формальном слое нет — по § «Где появляется граница» это уже не конструкция, а постулат L3.

Сноска 6 (второе и третье предложения; о первом — расхождение 3):

> Переход от сжатия к самой *Коши-сходимости* итератов (`euler_picard_cauchy` там же; `iterate_is_cauchy` в
> `FixedPoint.v`) идёт через лемму о затухании $c^n$ (`Qpow_vanish`) и тоже аксиом не требует. Иными словами,
> «приближения образуют процесс Коши» конструктивно целиком — и алгебра сжатия, и предельная оценка, — что и
> проверяется `Print Assumptions`; за пределами конструкции остаётся только завершённый предел.

Сноска 7 — текст дан в расхождении 2.

Тезис § «Где появляется граница» (стр. 211–215) о том, что актуализация предела как объекта есть постулат L3,
— слово автора; он не правится. Правятся только ссылки на формальный слой и на `Print Assumptions`.

## Расхождение 2. `banach_fixed_point` — определение процесса Коши, а не теорема «неподвижная точка существует» (сноска 7; сноска 2, первые слова)

**Было:**

> (сноска 7) Полная банахова теорема в форме «неподвижная точка *существует*» (`banach_fixed_point`) наследует
> `classic`; …
>
> (сноска 2) Банахова теорема о неподвижной точке (`banach_fixed_point`) …

**Проверка.** `src/FixedPoint.v:386`:

```coq
Definition banach_fixed_point (f : Q -> Q) (a b c x : Q)
  (Hc : is_contraction f a b c) (Hxa : a <= x) (Hxb : x <= b)
  : CauchySeq :=
  mkCauchy (fun n => iterate f x n)
           (iterate_is_cauchy f a b c x Hc Hxa Hxb).
```

Это определение: по сжатию и начальной точке оно строит запись `CauchySeq` (последовательность итератов вместе
с доказательством её Коши-свойства). Утверждения вида `exists p, f p == p` в файле нет. `Print Assumptions
banach_fixed_point`: Closed under the global context. Ближайшие теоремы файла: `approximate_fixed_point`
(`:393`, $|f(x_n) - x_n| \to 0$), `contraction_unique_fixed` (`:153`, неподвижных точек не более одной) — обе
без аксиом.

**В чём расхождение.** Именем теоремы существования названо определение, которое существования неподвижной
точки не утверждает; цена его тоже иная — без аксиом.

**(а) Довести формализацию до слов главы.** Нельзя: над ℚ утверждение «у сжатия отрезка есть неподвижная
точка» неверно, и закон исключённого третьего этого не меняет. Контрпример проверен (`Check.v`, раздел 7,
Closed under the global context):

```coq
Definition newton2 (x : Q) : Q := (1#2) * x + / x.

Lemma newton2_contraction : is_contraction newton2 1 2 (1#2).

Theorem newton2_no_rational_fixed_point : forall p : Q,
  1 <= p -> p <= 2 -> ~ newton2 p == p.
Proof.
  intros p H1 H2 Hfix. unfold newton2 in Hfix.
  apply (Sqrt2Irrational.no_rational_sqrt2 p).
  assert (E : p * / p == 1) by (apply Qmult_inv_r; lra).
  assert (E2 : / p == (1#2) * p) by lra.
  rewrite E2 in E. lra.
Qed.

Theorem contraction_without_rational_fixed_point :
  is_contraction newton2 1 2 (1#2) /\
  is_cauchy (fun n => iterate newton2 1 n) /\
  (forall p : Q, 1 <= p -> p <= 2 -> ~ newton2 p == p).
```

Отображение $x \mapsto x/2 + 1/x$ — сжатие отрезка $[1, 2]$ рациональных чисел с коэффициентом $1/2$; его
итерации образуют процесс Коши; неподвижная точка удовлетворяла бы $p^2 = 2$. Более слабое и содержательное
уже доказано: итераты образуют процесс Коши (`iterate_is_cauchy`), приближённо неподвижны
(`approximate_fixed_point`), неподвижная точка единственна, если есть (`contraction_unique_fixed`). Контрпример
подтверждает слово главы «предел — роль-предел» и стоит того, чтобы войти в формализацию (новым файлом рядом с
`FixedPoint.v`).

**(б) Поправить слова.** Сноска 7:

> В `FixedPoint.v` `banach_fixed_point` — определение: оно записывает итераты сжатия как процесс Коши
> (`CauchySeq`) и аксиом не требует. Утверждения «неподвижная точка *существует*» как рационального числа в
> формальном слое нет, и над ℚ его быть не может: сжатие $x \mapsto x/2 + 1/x$ отрезка $[1,2]$ не имеет
> рациональной неподвижной точки ($x^2 = 2$) — предел остаётся ролью. Доказаны приближённая неподвижность
> итератов (`approximate_fixed_point`) и единственность неподвижной точки (`contraction_unique_fixed`). См.
> также `ProcessPicardOperator.v` (Глава 8.3), где *сжатие на пространстве сеточных функций*, *единственность*
> решения на сетке и *геометрический зазор* итератов доказаны без аксиом; явной обёртки «итераты $\to$
> завершённое решение» в файле нет.

Первые слова сноски 2 — в тексте расхождения 1 (вместо «Банахова теорема о неподвижной точке» — «запись
итератов как процесса Коши»).

## Расхождение 3. Скалярное сжатие доказано при липшицевости и ограниченности правой части; на странице ограниченность не названа (стр. 48–51, 196–199; сноска 6, первое предложение)

**Было:**

> (48–51) Доказанное ядро — конкретное: траектория Эйлера и (скалярная) итерация Эйлера–Пикара суть
> рациональные процессы; при липшицевости и достаточно малом шаге итерация есть *сжатие*, а значит — процесс
> Коши (банахова неподвижная точка).[^1]
>
> (196–199) Если $f$ липшицева по $y$ с константой $L$, то на достаточно малом шаге итерация Эйлера–Пикара —
> *сжатие*: расстояние между образами двух приближений строго меньше расстояния между самими приближениями, с
> коэффициентом $r < 1$.
>
> (сноска 6) В скалярном слое: `euler_picard_contraction` (`ProcessPicard.v`) доказывает, что отображение
> $y \mapsto y_0 + f(y) h$ есть сжатие (`is_contraction`) с коэффициентом $Lh$ при $Lh<1$ — это конструктивно,
> 0 аксиом.

**Проверка.** `src/process/ProcessPicard.v:165`, `:206`:

```coq
Theorem euler_picard_contraction : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  is_contraction (euler_picard g y0 h) (y0 - M * h) (y0 + M * h) (L * h).

Theorem euler_picard_cauchy : forall g y0 h L M,
  0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M ->
  L * h < 1 ->
  is_cauchy (euler_picard_process g y0 h).
```

Здесь `g : Q -> Q` — автономная правая часть, `euler_picard g y0 h y := y0 + g y * h`,
`is_bounded_auto g M := 0 < M /\ forall y, Qabs (g y) <= M` (`:85`) — ограниченность на всём ℚ. Обе теоремы —
«Closed under the global context»; цена на странице названа верно.

Посылка ограниченности существенно сужает теорему: линейная правая часть ей не удовлетворяет ни при каком $M$
(`Check.v`, `id_not_bounded_auto`, `linear_not_bounded_auto`: `~ a == 0 -> ~ is_bounded_auto (fun y => a * y)
M`). Поиском по `src` не найдено ни одной функции, для которой доказано `is_bounded_auto`; примеры
`ProcessODEExamples.v` (правые части $y$, $-\alpha y$, $Ly$) доказывают липшицевость, а ограниченность — только
на отрезке $[-M, M]$ (`exp_rhs_bounded_on`, `:67`), что посылкой теоремы не является. Посылки при этом
выполнимы — им удовлетворяет постоянная правая часть (`const_satisfies_both_premises`), так что теоремы
содержательны, но к линейным правым частям в нынешнем виде не применяются.

**В чём расхождение.** В теореме три условия — липшицевость, ограниченность правой части на всём ℚ и малость
шага, — а страница называет два.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом: посылка ограниченности не нужна. При
$Lh < 1$ отрезок $[y_0 - R, y_0 + R]$ с $R = |g(y_0)| h / (1 - Lh)$ переходит в себя. Проверено (`Check.v`,
раздел 1; все — Closed under the global context):

```coq
Definition ep_radius (g : Q -> Q) (y0 h L : Q) : Q :=
  Qabs (g y0) * h / (1 - L * h).

Lemma ep_radius_eq : forall g y0 h L, L * h < 1 ->
  ep_radius g y0 h L * (1 - L * h) == Qabs (g y0) * h.
Proof. intros g y0 h L Hc. unfold ep_radius. field. lra. Qed.

Lemma euler_picard_interval_lip : forall g y0 h L y,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  y0 - ep_radius g y0 h L <= y -> y <= y0 + ep_radius g y0 h L ->
  y0 - ep_radius g y0 h L <= euler_picard g y0 h y /\
  euler_picard g y0 h y <= y0 + ep_radius g y0 h L.
Proof.
  intros g y0 h L y Hh [HL Hlip] Hc Hlo Hhi.
  pose proof (ep_radius_eq g y0 h L Hc) as HR.
  set (R := ep_radius g y0 h L) in *.
  assert (Hy : Qabs (y - y0) <= R) by (apply Qabs_Qle_condition; split; lra).
  pose proof (Hlip y y0) as Hg.
  assert (HLy : L * Qabs (y - y0) <= L * R)
    by (apply FixedPoint.Qmult_le_compat_l; [ exact Hy | lra ]).
  pose proof (Qabs_triangle (g y0) (g y - g y0)) as Htri.
  assert (Heq : g y0 + (g y - g y0) == g y) by ring.
  rewrite Heq in Htri.
  assert (Hg2 : Qabs (g y) <= Qabs (g y0) + L * R) by lra.
  assert (Hgh : Qabs (g y) * h <= (Qabs (g y0) + L * R) * h)
    by (apply Qmult_le_compat_r; [ exact Hg2 | exact Hh ]).
  assert (E1 : (Qabs (g y0) + L * R) * h == Qabs (g y0) * h + L * h * R) by ring.
  assert (E2 : R * (1 - L * h) == R - L * h * R) by ring.
  assert (Hb : Qabs (g y * h) <= R).
  { rewrite Qabs_Qmult, (Qabs_pos h Hh). lra. }
  apply Qabs_Qle_condition in Hb. destruct Hb as [Hb1 Hb2].
  unfold euler_picard. split; lra.
Qed.

Theorem euler_picard_contraction_lip : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  is_contraction (euler_picard g y0 h)
    (y0 - ep_radius g y0 h L) (y0 + ep_radius g y0 h L) (L * h).
Proof.
  intros g y0 h L Hh Hlip Hc.
  unfold is_contraction. split; [ | split; [ | split ] ].
  - destruct Hlip as [HL _]. apply Qmult_le_0_compat; [ lra | exact Hh ].
  - exact Hc.
  - intros u Hu1 Hu2. apply euler_picard_interval_lip; assumption.
  - intros u v _ _ _ _. apply euler_picard_lip; assumption.
Qed.

Theorem euler_picard_cauchy_lip : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  is_cauchy (euler_picard_process g y0 h).

(* Для правой части f(t, y), взятой в фиксированный момент t. *)
Corollary euler_picard_cauchy_vf : forall (f : VectorField) (t y0 h L : Q),
  0 <= h -> is_lipschitz f L -> L * h < 1 ->
  is_cauchy (euler_picard_process (f t) y0 h).
```

После такого дополнения (новым файлом, например `src/process/ProcessPicardLipschitz.v`; существующие файлы не
меняются) слова страницы «при липшицевости и достаточно малом шаге» верны без правки; в сносках 1 и 6 достаточно
назвать новые теоремы рядом с прежними.

**(б) Поправить слова** (если формализацию не дополнять).

Стр. 48–51:

> Доказанное ядро — конкретное: траектория Эйлера и (скалярная) итерация Эйлера–Пикара суть рациональные
> процессы; при липшицевости и ограниченности правой части и достаточно малом шаге итерация есть *сжатие*, а
> значит — процесс Коши (банахова неподвижная точка).[^1]

Стр. 196–199 — общий текст с расхождением 4, дан там.

Сноска 6, первое предложение:

> В скалярном слое: `euler_picard_contraction` (`ProcessPicard.v`) доказывает, что при $|f| \le M$ отображение
> $y \mapsto y_0 + f(y) h$ есть сжатие (`is_contraction`) отрезка $[y_0 - Mh, y_0 + Mh]$ с коэффициентом $Lh$
> при $Lh<1$ — это конструктивно, 0 аксиом.

## Расхождение 4. «Существование решения»: Коши-свойство доказано для итерации одного скалярного шага; её роль-предел — значение одного неявного шага Эйлера, а не решение на отрезке (стр. 67–68, 196–207, 220–221)

**Было:**

> (67–68) Первые два уровня глава ведёт как доказанные (с явной отметкой там, где предел требует L3), третий —
> как честно помеченную границу.
>
> (196–200) Если $f$ липшицева по $y$ с константой $L$, то на достаточно малом шаге итерация Эйлера–Пикара —
> *сжатие*: … А сжатие, по банаховой схеме, порождает процесс Коши: последовательные приближения сближаются
> геометрически.[^6]
>
> (202–207) Таким образом существование решения переписывается *без* обращения к завершённой функции:
> *приближения, порождённые уравнением, образуют процесс Коши*. Это утверждение о рациональной
> последовательности — его можно сформулировать и доказать, не вызывая к существованию ни одного бесконечного
> объекта. Конструктивное ядро теоремы Пикара–Линделёфа — именно это: не «есть функция», а «процесс сжимается».
>
> (220–221) Доказано конечное и процессное: уравнение порождает процесс приближений, и при липшицевости этот
> процесс — Коши.

**Проверка.** Теорема, на которую опираются эти места, — `euler_picard_cauchy` (`ProcessPicard.v:206`, текст в
расхождении 3). Последовательность в ней (`:188`, `:192`):

```coq
Definition euler_picard (g : Q -> Q) (y0 h : Q) (y : Q) : Q := y0 + g y * h.
Definition euler_picard_iterate (g : Q -> Q) (y0 h : Q) (n : nat) : Q :=
  iterate (euler_picard g y0 h) y0 n.
```

то есть $y_{n+1} = y_0 + h\,g(y_n)$ при одном фиксированном шаге $h$. Это не траектория Эйлера
($y_{n+1} = y_n + h f(t_n, y_n)$, `euler_method`, `ProcessODE.v:48`) и не итерации Пикара на функциях
(`picard_iterate`, `ProcessPicard.v:313`). Неподвижная точка этого отображения есть решение уравнения
$p = y_0 + h\,g(p)$ — значение одного неявного шага Эйлера длины $h$ (`Check.v`, `euler_picard_fixed_iff`). На
примере $y' = y$, $y_0 = 1$, $h = 1/2$ (`Check.v`, раздел 2, Closed under the global context):

```coq
Lemma linear_scalar_iteration_value : forall n,
  euler_picard_iterate (fun y : Q => y) 1 (1#2) n == 2 - Qpow (1#2) n.

Theorem linear_scalar_iteration_limit : forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (euler_picard_iterate (fun y : Q => y) 1 (1#2) n - 2) < eps.

Lemma explicit_euler_one_step :       euler_method (fun _ y : Q => y) 0 1 (1#2) 1 == 3#2.
Lemma explicit_euler_two_half_steps : euler_method (fun _ y : Q => y) 0 1 (1#4) 2 == 25#16.
```

Итерация сходится к $2 = y_0/(1 - h)$; явный метод Эйлера даёт для той же точки $3/2$ и $25/16$; классическое
значение решения в точке $1/2$ — $e^{1/2} \approx 1{,}6487$ (в Rocq не проверялось). При другом шаге предел
другой.

О траектории Эйлера в `ProcessODE.v` доказаны только леммы развёртывания определения и свойства одного шага
(`euler_step_bounded`, `euler_step_lip`). О `picard_step`, `picard_iterate`, `picard_process` в `ProcessPicard.v` доказаны только три
леммы развёртывания определения (`picard_iterate_0`, `picard_process_0`, `picard_iterate_succ`). Определение
решения в дифференциальном смысле (`is_ode_solution`, `stdlib/ODE.v:61`) ни в одной теореме `src` не
используется.

Страница оговаривает слой словом «(скалярная)» (стр. 49) и словами «В скалярном слое» (сноска 6). Но в той же
главе «скалярным» названо само уравнение (стр. 40–41: «для скалярного уравнения первого порядка»), и нигде не
сказано, что итерация идёт при одном фиксированном шаге и что её предел — не решение.

**В чём расхождение.** Доказано, что сходится итерация, решающая уравнение одного неявного шага; страница
делает из этого вывод о существовании решения задачи Коши и о процессе приближений к нему.

**(а) Довести формализацию до слов главы.** Частично возможно, без аксиом. Проверены два уровня, на которых
слова «приближения, порождённые уравнением, образуют процесс Коши» становятся теоремой о приближениях к решению
(`Check.v`, разделы 5 и 6; все — Closed under the global context).

*Сетка* (`ProcessPicardOperator.v`). Сеточный оператор Пикара имеет неподвижной точкой траекторию явного метода
Эйлера, и итерации приходят к ней за конечное число шагов — в узле $k$ начиная с $n = k$. Условие $LT < 1$ и
липшицевость для этого не нужны: достаточно, чтобы $f$ уважала равенство `Qeq` по второму аргументу (из
липшицевости это следует — `lipschitz_wd`).

```coq
Section GridPicard.
Variable f : Q -> Q -> Q.
Hypothesis Hwd : forall t y1 y2, y1 == y2 -> f t y1 == f t y2.
Variables h y0 : Q.

Fixpoint grid_euler (k : nat) : Q :=
  match k with
  | O => y0
  | S k' => grid_euler k' + h * f (tgrid h k') (grid_euler k')
  end.

Lemma picard_op_grid_euler : forall k,
  picard_op f h y0 grid_euler k == grid_euler k.

Theorem picard_fixed_is_grid_euler : forall (N : nat) (y : nat -> Q),
  (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) ->
  forall k, (k <= N)%nat -> y k == grid_euler k.
Proof.
  intros N y Hy k. induction k as [k IH] using lt_wf_ind. intro HkN.
  transitivity (picard_op f h y0 y k); [ symmetry; apply Hy; exact HkN | ].
  transitivity (picard_op f h y0 grid_euler k); [ | apply picard_op_grid_euler ].
  unfold picard_op, picard_sum.
  apply Qplus_comp; [ reflexivity | ]. apply Qmult_comp; [ reflexivity | ].
  apply q_sum_ext_lt. intros j Hj. apply Hwd. apply IH; lia.
Qed.

Theorem picard_iter_stabilizes : forall n k, (k <= n)%nat ->
  picard_iter f h y0 n k == grid_euler k.
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (k = 0%nat) by lia. subst k. cbn. reflexivity.
  - cbn [picard_iter].
    transitivity (picard_op f h y0 grid_euler k); [ | apply picard_op_grid_euler ].
    unfold picard_op, picard_sum.
    apply Qplus_comp; [ reflexivity | ]. apply Qmult_comp; [ reflexivity | ].
    apply q_sum_ext_lt. intros j Hj. apply Hwd. apply IH. lia.
Qed.

Theorem picard_iter_is_Cauchy : forall k,
  is_Cauchy (fun n => picard_iter f h y0 n k).

Theorem picard_iter_reaches_solution : forall (N n k : nat),
  (N <= n)%nat -> (k <= N)%nat ->
  picard_iter f h y0 n k == grid_euler k /\
  picard_op f h y0 (picard_iter f h y0 n) k == picard_iter f h y0 n k.
End GridPicard.
```

*Функции ℚ → ℚ* (`picard_step`, `picard_iterate` из `ProcessPicard.v` — оператор с интегралом-процессом, тот
самый, что описан на стр. 172–177). При каждой стадии $N$ интеграла-процесса оператор — сжатие в равномерном
расстоянии на $[0, t]$, а итерации образуют равномерный процесс Коши на $[0, T]$ при $LT < 1$:

```coq
Theorem picard_step_contraction :
  forall (f : VectorField) (L y0 : Q) (y z : Q -> Q) (D t : Q) (N : nat),
  is_lipschitz f L -> 0 <= t -> 0 <= D ->
  (forall s, 0 <= s -> s <= t -> Qabs (y s - z s) <= D) ->
  Qabs (picard_step f y0 y t N - picard_step f y0 z t N) <= (L * t) * D.

Theorem picard_iterate_gap :
  forall (f : VectorField) (L y0 T C : Q) (N n : nat),
  is_lipschitz f L -> 0 <= T -> 0 <= C ->
  (forall t, 0 <= t -> t <= T ->
     Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= C) ->
  forall t, 0 <= t -> t <= T ->
    Qabs (picard_iterate f y0 (S n) t N - picard_iterate f y0 n t N)
      <= Qpow (L * T) n * C.

Theorem picard_iterate_uniformly_cauchy :
  forall (f : VectorField) (L y0 T C : Q) (N : nat),
  is_lipschitz f L -> 0 <= T -> L * T < 1 -> 0 <= C ->
  (forall t, 0 <= t -> t <= T ->
     Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= C) ->
  forall eps, 0 < eps ->
  exists K : nat, forall m n, (K <= m)%nat -> (K <= n)%nat ->
    forall t, 0 <= t -> t <= T ->
      Qabs (picard_iterate f y0 m t N - picard_iterate f y0 n t N) < eps.

(* Первый зазор ограничен, когда f(s, y0) ограничена на [0, T]. *)
Lemma picard_first_gap_bound : forall (f : VectorField) (y0 T M0 : Q) (N : nat),
  0 <= T -> 0 <= M0 ->
  (forall s, 0 <= s -> s <= T -> Qabs (f s y0) <= M0) ->
  forall t, 0 <= t -> t <= T ->
    Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= M0 * T.
```

Доказательство `picard_step_contraction` — разность сумм Римана есть сумма Римана разности (`riemann_sum_sub`),
оценка `riemann_sum_abs_bound` (`RiemannIntegration.v:134`) по узлам `walk_point 0 (t/(N+1)) k`, которые лежат
в $[0, t]$ (`walk_point_0_range`); `picard_iterate_gap` — индукция по $n$; Коши-свойство — `geom_gap_modulus`
(расхождение 1). Посылки выполнимы: пример `picard_iterate_linear_uniformly_cauchy` — $f(t, y) = y$,
$y_0 = 1$, отрезок $[0, 1/2]$, любая стадия $N$. Полные тексты — `Check.v`, раздел 6.

*Что остаётся недоведённым.* Роль-предел во всех трёх теоремах — неподвижная точка оператора при
фиксированной сетке или фиксированной стадии $N$ интеграла (на сетке — траектория Эйлера), то есть приближение
к решению, а не оно само. Чтобы слова «решение — предел процесса приближений» стали теоремой, нужна ещё оценка
по измельчению: траектории Эйлера (или неподвижные точки при стадиях $N$ и $2N$) сближаются, когда шаг
убывает. Для этого от $f$ требуется больше, чем липшицевость по $y$: модуль непрерывности по $t$ (например,
липшицевость по $t$) и оценка $|f|$ на прямоугольнике. Без условия по $t$ утверждение неверно (довод на
бумаге, в Rocq не проверялся: при $f(t, y) = \varphi(t)$, где $\varphi$ равна 1 в двоично-рациональных точках
и 0 в остальных, суммы по сеткам из $2^k$ узлов и из $3^k$ узлов идут к разным значениям). Такая теорема
честно формулируется над ℚ и аксиом не требует, но здесь не пробовалась. Связь с дифференциальной формой («предел удовлетворяет уравнению») потребует определения
решения; `is_ode_solution` сейчас ни в одной теореме не участвует.

**(б) Поправить слова.**

Стр. 67–68:

> Первый уровень глава ведёт как доказанный, второй — как чтение доказанного, третий — как честно помеченную
> границу.

Стр. 196–200 (вместе с расхождением 3; слова «и ограничена» не нужны, если принято дополнение расхождения 3):

> Если $f$ липшицева по $y$ с константой $L$ и ограничена, то на достаточно малом шаге $h$ итерация
> Эйлера–Пикара одного шага — отображение $y \mapsto y_0 + h f(y)$ — *сжатие*: расстояние между образами двух
> приближений строго меньше расстояния между самими приближениями, с коэффициентом $r < 1$. А сжатие, по
> банаховой схеме, порождает процесс Коши: последовательные приближения сближаются геометрически.[^6]

Стр. 202–207 (если формализацию не дополнять):

> Таким образом существование решения переписывается *без* обращения к завершённой функции: *приближения,
> порождённые уравнением, образуют процесс Коши*. Это утверждение о рациональной последовательности — его
> можно сформулировать и доказать, не вызывая к существованию ни одного бесконечного объекта. В формальном слое
> оно доказано для одного шага: итерации отображения $y \mapsto y_0 + h f(y)$ при фиксированном $h$ образуют
> процесс Коши, и его роль-предел — неподвижная точка шага (значение одного неявного шага Эйлера), ещё не
> решение на отрезке; для итераций Пикара на сеточных функциях то же ядро — сжатие оператора и геометрический
> зазор — доказано в Главе 8.3. Конструктивное ядро теоремы Пикара–Линделёфа — именно это: не «есть функция», а
> «процесс сжимается».

Стр. 202–207 (если принято дополнение пункта «а») — среднее предложение иное:

> …В формальном слое оно доказано на трёх уровнях: для одного скалярного шага (`euler_picard_cauchy`), для
> итераций Пикара на сетке (они приходят к траектории Эйлера за конечное число шагов) и для итераций Пикара на
> функциях при каждой стадии интеграла-процесса (равномерный процесс Коши на $[0, T]$ при $LT < 1$);
> роль-предел в каждом случае — приближение при данном шаге или данной стадии, а сближение этих приближений при
> измельчении — следующий шаг, здесь не доказанный. …

Стр. 220–221:

> Доказано конечное и процессное: уравнение порождает процесс приближений, и при липшицевости итерации одного
> шага образуют процесс Коши, а итерации Пикара на сетке имеют геометрический зазор (Глава 8.3).

## Расхождение 5. `ode_is_process`: «процесс-ошибка» в утверждении не связан с процессом-решением (сноска 4)

**Было:**

> Что решение *есть* процесс, а не его предел, зафиксировано в `ode_is_process` (`ProcessODE.v`): пара
> «процесс-решение / процесс-ошибка», где процесс-решение совпадает с итерацией Эйлера–Пикара.

**Проверка.** `src/process/ProcessODE.v:333`:

```coq
Theorem ode_is_process : forall g y0 h L M,
  is_lipschitz_auto g L -> is_bounded_auto g M ->
  0 < h -> L * h < 1 ->
  exists sol_proc err_proc : RealProcess,
    (forall n, sol_proc n == euler_picard_iterate g y0 h n) /\
    (forall n, 0 <= err_proc n) /\
    is_Cauchy sol_proc.
```

`Print Assumptions ode_is_process`: Closed under the global context. От `err_proc` требуется только
`forall n, 0 <= err_proc n`; с `sol_proc` он в утверждении не связан, и условию удовлетворяет любой
неотрицательный процесс. Проверено (`Check.v`, `ode_is_process_with_zero_err`): то же заключение выполняется
при `err_proc := fun _ => 0`. Первый и третий члены конъюнкции повторяют `euler_picard_is_Cauchy`
(`ProcessPicard.v:220`). Процесс-решение — скалярная итерация расхождения 4.

**В чём расхождение.** Теорема утверждает существование процесса Коши, равного скалярной итерации, и
существование какого-нибудь неотрицательного процесса; пары «решение / его ошибка» в ней нет.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом и без посылки ограниченности: процесс-ошибка
$e_n = |g(y_0) h| (Lh)^n / (1 - Lh)$ ограничивает расстояние от стадии $n$ до всякой более поздней стадии и
стремится к нулю. Проверено (`Check.v`, раздел 3; Closed under the global context):

```coq
Definition ep_err (g : Q -> Q) (y0 h L : Q) : RealProcess :=
  fun n => Qabs (g y0 * h) * Qpow (L * h) n / (1 - L * h).

Theorem euler_picard_error_process : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  forall n m, (n <= m)%nat ->
    Qabs (euler_picard_iterate g y0 h m - euler_picard_iterate g y0 h n)
      <= ep_err g y0 h L n.
Proof.
  intros g y0 h L Hh Hlip Hc n m Hnm.
  pose proof (ep_radius_nonneg g y0 h L Hh Hc) as HR.
  pose proof (euler_picard_contraction_lip g y0 h L Hh Hlip Hc) as Hcon.
  assert (Ha : y0 - ep_radius g y0 h L <= y0) by lra.
  assert (Hb : y0 <= y0 + ep_radius g y0 h L) by lra.
  pose proof (iterate_diff_bound _ _ _ _ y0 Hcon Ha Hb n m Hnm) as Htel.
  assert (Hd : euler_picard g y0 h y0 - y0 == g y0 * h) by (unfold euler_picard; ring).
  rewrite Hd in Htel.
  assert (Hc0 : 0 <= L * h) by (destruct Hcon as [H _]; exact H).
  assert (Hpm : 0 <= Qpow (L * h) m) by (apply SeriesConvergence.Qpow_nonneg; exact Hc0).
  assert (Hdm : 0 <= Qabs (g y0 * h) * Qpow (L * h) m)
    by (apply Qmult_le_0_compat; [ apply Qabs_nonneg | exact Hpm ]).
  unfold euler_picard_iterate, ep_err.
  apply Qle_shift_div_l; [ lra | ].
  lra.
Qed.

Theorem ep_err_vanishes : forall g y0 h L,
  0 <= h -> is_lipschitz_auto g L -> L * h < 1 ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> ep_err g y0 h L n < eps.

Theorem ode_is_process_err : forall g y0 h L,
  is_lipschitz_auto g L -> 0 <= h -> L * h < 1 ->
  exists sol_proc err_proc : RealProcess,
    (forall n, sol_proc n == euler_picard_iterate g y0 h n) /\
    (forall n m, (n <= m)%nat -> Qabs (sol_proc m - sol_proc n) <= err_proc n) /\
    (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> err_proc n < eps) /\
    is_Cauchy sol_proc.
```

С такой теоремой слова сноски верны, если заменить в ней имя на `ode_is_process_err`; оговорка расхождения 4
(процесс-решение — итерация одного шага) остаётся.

**(б) Поправить слова** (если формализацию не дополнять):

> Что решение *есть* процесс, а не его предел, зафиксировано в `ode_is_process` (`ProcessODE.v`): существует
> процесс Коши, совпадающий с итерацией Эйлера–Пикара одного шага; о втором процессе теоремы
> («процессе-ошибке») в ней утверждается только неотрицательность.

## Расхождение 6. «Сжатие оператора Пикара на пространстве функций»: теорема говорит о сеточных функциях и о другом операторе, чем названный в той же сноске `picard_step` (стр. 30–34; сноска 5; сноска 7)

**Было:**

> (30–34) Конкретные методы (Эйлер на сетке — Глава 8.2), полноценная теорема Пикара–Линделёфа как сжатие на
> пространстве функций (центр Части, Глава 8.3), …
>
> (сноска 5) Интегральный шаг Пикара `picard_step` определён в `ProcessPicard.v`; интеграл в нём — процесс
> накопления Части V. Полноценная теорема о сжатии оператора Пикара *на пространстве функций* (а не только
> скалярного шага) — центр Части, Глава 8.3 (`ProcessPicardOperator.v`).
>
> (сноска 7) …где *сжатие на пространстве функций*, …

**Проверка.** `src/process/ProcessPicardOperator.v:61–64`, `:102`:

```coq
Definition picard_sum (y : nat -> Q) (k : nat) : Q :=
  q_sum (fun j => f (tgrid j) (y j)) k.
Definition picard_op (y : nat -> Q) : nat -> Q :=
  fun k => y0 + h * picard_sum y k.

Theorem picard_op_contraction : forall (y z : nat -> Q) (D : Q) (k : nat),
  0 <= D ->
  (k <= N)%nat ->
  (forall j, (j <= N)%nat -> Qabs (y j - z j) <= D) ->
  Qabs (picard_op y k - picard_op z k) <= (L * Tlen) * D.
```

Предмет теоремы — сеточные функции `nat -> Q`, сравниваемые на узлах $k \le N$ (точка $ℚ^{N+1}$); оператор —
$\Phi(y)_k = y_0 + h \sum_{j<k} f(t_j, y_j)$, левая сумма Римана с шагом самой сетки. Его неподвижная точка на
сетке есть траектория явного метода Эйлера (`Check.v`, `picard_fixed_is_grid_euler`). Шапка файла говорит это
сама: «on the SPACE OF FUNCTIONS (finite grid)». Теоремы существования решения в файле нет (11 `Qed`: оценка
разности сумм, сжатие, пять лемм о максимуме, единственность, две леммы о неотрицательности, геометрический
зазор).

`picard_step` (`ProcessPicard.v:308`) — другой оператор: на функциях `Q -> Q`, с интегралом
`integral_process … 0 t N` (сумма Римана с $N + 1$ отрезками на $[0, t]$). О нём в формализации нет ни одной
теоремы о сжатии; `ProcessPicardOperator.v` его не подключает.

**В чём расхождение.** Страница говорит о сжатии оператора Пикара на пространстве функций; доказана оценка для
сеточного оператора на конечной сетке, а о названном рядом интегральном шаге `picard_step` не доказано ничего.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом — для того самого оператора, который назван в
сноске: `picard_step_contraction`, `picard_iterate_gap`, `picard_iterate_uniformly_cauchy` (тексты в расхождении
4, пункт «а»; `Check.v`, раздел 6). Это сжатие на функциях `Q -> Q` в равномерном расстоянии по рациональным
точкам отрезка $[0, t]$, при всякой стадии $N$ интеграла-процесса. Завершённого пространства $C([a,b])$ в
формализации нет и быть не должно; «пространство функций» здесь — функции `Q -> Q` с равномерной оценкой на
рациональных точках отрезка. С таким дополнением слова сноски 5 верны без правки (достаточно назвать новые
теоремы); в стр. 30–34 и в сноске 7 для теоремы Главы 8.3 остаётся уточнение «сеточных».

**(б) Поправить слова** (если формализацию не дополнять).

Стр. 30–34:

> Конкретные методы (Эйлер на сетке — Глава 8.2), полноценная теорема Пикара–Линделёфа в сеточной форме — как
> сжатие на пространстве сеточных функций (центр Части, Глава 8.3), устойчивость и единственность (Глава 8.4),
> экспонента и линейные уравнения (Глава 8.5) разворачивают этот каркас в подробностях.

Сноска 5:

> Интегральный шаг Пикара `picard_step` определён в `ProcessPicard.v`; интеграл в нём — процесс накопления
> Части V. Полноценная теорема о сжатии оператора Пикара *на пространстве сеточных функций* (а не только
> скалярного шага; оператор взят в сеточной форме $\Phi(y)_k = y_0 + h\sum_{j<k} f(t_j, y_j)$) — центр Части,
> Глава 8.3 (`ProcessPicardOperator.v`).

Сноска 7 — в тексте расхождения 2 («сжатие на пространстве сеточных функций»).

## Расхождение 7. Разметка E/R/R, приписанная шапкам `ProcessODE.v` и `ProcessPicard.v`, в этих шапках стоит в другом виде (сноска 8)

**Было:**

> Шапки дают разметку прямо: `ProcessODE.v` и `ProcessPicard.v` — Elements: рациональные приближения, узлы
> сетки, шаг $h$; Roles: приближение — стадия, решение — предел, $f$ — поле скорости; Rules: шаг Эйлера /
> оператор Пикара, сжатие при липшицевости.

**Проверка.** Шапки названных файлов:

```
ProcessPicard.v:2–4   Elements: Picard iterates y_n(t) (rational approximations)
                      Roles:    Cauchy process converging to ODE solution
                      Rules:    Lipschitz contraction via FixedPoint.v
ProcessODE.v:2–4      Elements: Euler method iterates, Picard-Lindelöf process
                      Roles:    existence and uniqueness of ODE solutions via process convergence
                      Rules:    Picard contraction + Gronwall stability → ODE well-posedness
```

Узлов сетки и шага среди элементов, «$f$ — поля скорости» среди ролей и шага Эйлера среди правил в них нет.
Эти слова стоят в шапках двух других файлов главы:

```
analysis/PicardLindelof.v:10–12   Elements: ODE rhs f, grid points t_k, trajectory values y_k
                                  Roles:    f -> VectorField, y_k -> Approximation, h -> StepSize
                                  Rules:    Euler recurrence (constitution), Lipschitz contraction (bound)
stdlib/ODE.v:5–7                  Elements: state trajectories (Q-valued)
                                  Roles:    f -> VectorField, h -> StepSize, x0 -> InitialCondition
                                  Rules:    Euler method (discrete constitution), Lipschitz condition
```

В них шаг $h$ назван ролью (StepSize), а не элементом; правая часть $f$ в `PicardLindelof.v` стоит и среди
элементов, и среди ролей.

**В чём расхождение.** Сноска приводит как прямую разметку двух шапок сводку, составленную из четырёх шапок, и
относит шаг $h$ к элементам, тогда как шапки называют его ролью.

**(а) Довести формализацию.** Речь о комментариях; при желании автора шапки `ProcessODE.v` и `ProcessPicard.v`
можно привести к разметке главы (правка комментариев, на компиляцию не влияет). Шапки этих файлов всё равно
требуют обновления чисел (раздел «Вне главы»).

**(б) Поправить слова:**

> Шапки дают разметку: `ProcessPicard.v` — Elements: итераты Пикара $y_n(t)$ (рациональные приближения);
> Roles: процесс Коши, сходящийся к решению; Rules: сжатие при липшицевости. `analysis/PicardLindelof.v` —
> Elements: узлы сетки $t_k$, значения траектории $y_k$; Roles: $f$ — поле скорости, $y_k$ — приближение,
> $h$ — шаг; Rules: шаг Эйлера, сжатие при липшицевости. В таблице главы шаг $h$ отнесён к элементам как
> рациональное число; шапки называют его по роли.

## Сомнительные места (расхождением не являются)

1. **`picard_unique`: заключение верно без посылок раздела** (сноски 2 и 7, «*единственность* решения на
   сетке»). Теорема (`ProcessPicardOperator.v:183`) стоит под посылками `Hlip` (липшицевость) и `Hrate`
   ($L \cdot T < 1$) и доказана через сжатие. Сеточный оператор берёт сумму по узлам $j < k$, поэтому значение
   неподвижной точки в узле $k$ определяется значениями в предыдущих узлах, и единственность верна при любой
   $f$, уважающей `Qeq`, при любом шаге и любой длине отрезка (`Check.v`, `picard_unique_any_step`, Closed
   under the global context). Слова страницы доказанному соответствуют; но «банахова единственность при
   $LT < 1$» здесь есть свойство рекуррентности Эйлера, а не сжатия. То же о `picard_iter_gap`: истинный зазор
   в узле $k$ обращается в нуль при $n \ge k$ (`picard_iter_stabilizes`). Предмет Глав 8.3–8.4.
2. **Правило существования в каркасе и разборе E/R/R** (стр. 80–83, 255–257: «при липшицевости итерация есть
   сжатие, поэтому процесс приближений — процесс Коши; решение — его предел (неподвижная точка оператора)»).
   Это правило системы в чтении автора; как доказанное в Rocq оно там не подаётся, и записей в ведомости для
   этих строк нет. При правке стр. 196–207 (расхождения 3 и 4) формулировки стоит согласовать.
3. **Тезис об L3** (стр. 211–215, 257–259: «„Процесс Коши сходится к пределу“ — шаг, который над ℚ … опирается
   на закон исключённого третьего»; «L3, делающий завершённый предел объектом»). Слово автора, не
   оценивается. К сведению: в формальном слое главы этого шага нет ни с L3, ни без него, а над ℚ рационального
   предела может не быть (расхождение 2, контрпример). В проекте L3 действительно стоит на соседнем шаге —
   «ограниченная монотонная последовательность есть процесс Коши» (`q_inc_bounded_cauchy`,
   `MonotoneConvergence.v:134`: `Classical_Prop.classic`).
4. **Интегральная форма** (стр. 164–170: «Перепишем задачу Коши в интегральной форме (по сеточно-процессной
   основной теореме анализа Части V…)»). Равносильность дифференциальной и интегральной форм в названных
   файлах теоремой не записана; страница доказанной её и не называет. Определение `is_ode_solution`
   (`stdlib/ODE.v:61`) в теоремах не используется.
5. **Слово «скалярная»** (стр. 49, 61; сноска 6). Употреблено в смысле «итерация на числах, а не на функциях»;
   в той же главе (стр. 40–41) «скалярным» названо уравнение. См. расхождение 4.
6. **«Запись `ODE` с шагом Эйлера как `GenProcess`»** (сноска 1). В самой записи `ODE` (`stdlib/ODE.v:33`: поля
   `ode_f`, `ode_x0`, `ode_h`) поля типа `GenProcess` нет; как `GenProcess Q` оформлена траектория
   `euler_process` (`:52`). В сноске 4 «шаг Эйлера оформлен как `GenProcess`» — то же: оформлена
   последовательность шагов.
7. **Одноимённые объявления.** `ODE` — запись в `stdlib/ODE.v:33` и определение `Q -> Q -> Q` в
   `analysis/PicardLindelof.v:31`; `euler_step` — четыре объявления, в `ProcessODE.v:44` порядок аргументов
   `f t y h`, в `PicardLindelof.v:33` — `f h t y`; `euler_process` — в `ProcessODE.v:57` и в
   `stdlib/ODE.v:52`. Страница файлы называет, путаницы на ней нет.
8. **«22 доказанных утверждения»** (сноска 1). Число верно. Два из них содержания не несут:
   `picard_constant_fixed` (`stdlib/ODE.v:299`) есть `x == x`, `picard_step_constant` (`:293`) — равенство по
   определению.
9. **`euler_traj`** (сноска 4, «траектория Эйлера на рациональной сетке»). Определена для сетки отрезка
   $[0, 1]$: шаг $1/N$, узлы $k/N$, начальный момент $0$ (`PicardLindelof.v:28–41`). Задача главы записана с
   общим $t_0$; в `euler_method` (`ProcessODE.v:48`) $t_0$ и $h$ произвольны.
10. **`picard_step` берёт одну стадию интеграла** (сноска 5, «интеграл в нём — процесс накопления»).
    `integral_process` — процесс по стадиям $n$; в `picard_step f y0 y_prev t N` взято его значение на стадии
    $N$, то есть одна сумма Римана. Отрезок интегрирования — $[0, t]$ (начальный момент $0$).
11. **«Строго меньше»** (стр. 198). `is_contraction` даёт $|f(x) - f(y)| \le c\,|x - y|$ при $c < 1$; строгое
    неравенство получается при $x \ne y$.

## Вне главы (замечено в исходниках; страницы не касается)

- **Шапки с ценой по подключённым модулям.** `FixedPoint.v:12` — «AXIOMS: classic (inherited from
  MonotoneConvergence via Qpow_vanish)»: ни одно из объявлений файла `classic` не использует.
  `SeriesConvergence.v:12` — «AXIOMS: classic (inherited from MonotoneConvergence)» относит аксиому ко всему
  файлу; по компилятору она стоит у `Qpow_cauchy`, `geometric_series_cauchy`, `comparison_test`,
  `geometric_limit`, а `Qpow_vanish`, `Qpow_limit_zero`, `absolute_convergence` — без аксиом.
  `ProcessPicardOperator.v:20–22` и `:230–233` — «the explicit is_cauchy/limit wrapper … reuses the repo's
  geometric-series layer, which is L3/classic-based»: обёртка доказывается без аксиом (расхождение 1).
- **Шапки с устаревшим счётом.** `ProcessODE.v:22` — «STATUS: 30 Qed» (действительно 20; строка 6 той же
  шапки называет 20). `ProcessPicard.v:6` — «24 Qed», `:24` — «35 Qed» (действительно 32).
- **`picard_lindelof`** (`ProcessODE.v:180`) и **`ode_well_posed`** (`:279`). Часть «существование» в обеих —
  `exists proc : RealProcess, is_Cauchy proc`: ей удовлетворяет любой постоянный процесс, с уравнением она не
  связана. Третий член `ode_well_posed`, подписанный «Stability of Picard iterates», —
  `euler_picard_iterate g y0 h n == euler_picard_process g y0 h n`, равенство по определению. Глава VIII.1 этих
  теорем не называет.
- **`euler_picard_duality`** (`ProcessPicard.v:465`): `exists euler_proc picard_proc, is_Cauchy euler_proc /\
  picard_proc = picard_process f y0 0 0` — свидетели: постоянный процесс и сам `picard_process`; посылки в
  доказательстве не используются.
- **`picard_from_vf`** (`ProcessPicard.v:428`): для поля `f : Q -> Q -> Q` берётся его срез `f 0` в момент
  $0$, а время $t$ подставлено на место шага; утверждение — существование процесса Коши в отрезке
  $[y_0 - Mt, y_0 + Mt]$.
- **Посылка `is_bounded_auto`** не доказана в `src` ни для одной функции (расхождение 3).
- **`is_ode_solution`** (`stdlib/ODE.v:61`) — определение без единого употребления.
