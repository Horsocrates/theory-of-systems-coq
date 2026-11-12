# Глава V.3 «Непрерывность» — заметки к ведомости (12.11.2026)

Ведомость: `part05-ch03.json` — 130 ручных записей + 20 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты ручных записей: ok — 106, mismatch-statement — 13, mismatch-price — 3,
wrong-number — 2, missing-name — 6 (с автоматическими: ok — 126).

Тринадцать записей mismatch-statement относятся к девяти местам (расхождения 1–9): четыре записи об одной
равносильности, две — об одной фразе про `UniformConvergence.v`.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part05/ch03/`: `Check.v`, `CheckEVT.v`, `CheckIdx.v`,
`CheckArgmax.v`, `CheckEval.v`. Все пять собираются; ответы `Print Assumptions` приведены по месту. В `src` и в
собранной копии ничего не менялось.

## Что проверить не удалось

- Расхождение 8 (на какой лемме стоит `ivt_cauchy_real`) установлено чтением доказательства: зависимости между
  леммами компилятор не печатает.
- «Опорных файлов девять» (расхождение 13): глава не говорит, какие файлы считаются опорными; счёт сверен с
  перечнем файлов, названных в главе.
- Отсылки к другим главам (§ 2.2, § 2.5–2.7, Главы 4.6 и 5.1) не сверялись. Проверена одна — цена
  `bolzano_weierstrass`: `Classical_Prop.classic` и `ToS_Axioms.L4_witness`; слова стр. 540–541 («требовал $L3$»)
  с ней согласуются, $L4$ там не назван.
- Замечание о теореме Дини над ℚ (расхождение 9) — математическое, компилятором не проверялось.
- Доказательство теоремы об экстремуме без `classic` (раздел «Наблюдение») собрано для `EVT_idx.v`; для
  `EVT_ERR.v` и `ProcessEVT.v` оно не пересобиралось.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Два описания непрерывности названы равносильными, доказана одна сторона (стр. 189–191, 221–222, 243–246, 285)

**Было:**

> (189–191) И его ToS не постулирует отдельно, а *выводит* из $\delta$-$\varepsilon$ определения — показывая, что
> два описания непрерывности суть одно.
>
> (221–222) непрерывная функция — ровно та, что уважает топологическую структуру, построенную предыдущей главой.
>
> (243–246) Сама непрерывность есть *конституция* — в двух равносильных формах: локальной ($\delta$-$\varepsilon$)
> и топологической («прообраз открытого открыт»); § 3.2.3 показал, что это одно правило, записанное дважды.
>
> (285) | непрерывность ($\delta$-$\varepsilon$ $\equiv$ прообраз открытого открыт) | конституция | Rule (конструкт.) |

**Проверка.** `continuous_preserves_open_preimage` (`src/stdlib/Topology.v:235`):
`forall f, continuous f -> forall S, is_open S -> is_open (fun x => S (f x))` — Closed under the global context.
Обратного утверждения нет ни в `Topology.v` (просмотрены все 19 лемм), ни в других файлах `src`.

**В чём расхождение.** Доказано, что дельта-эпсилон непрерывность влечёт открытость прообразов; обратного вывода
в формализации нет, а глава говорит о равносильности.

**(а) Довести формализацию.** Возможно, без допущений: в качестве открытого множества берётся шар радиуса ε
вокруг `f x`. Набросок проверен (`Check.v`), обе теоремы — Closed under the global context:

```coq
Theorem open_preimage_implies_continuous : forall f : Q -> Q,
  (forall S : Q -> Prop, is_open S -> is_open (fun x => S (f x))) ->
  continuous f.
Proof.
  intros f H x eps Heps.
  destruct (H (open_ball (f x) eps)
              (open_ball_is_open (f x) eps Heps)
              x
              (open_ball_center (f x) eps Heps)) as [delta [Hd Hb]].
  exists delta. split; [exact Hd |].
  intros y Hy. apply Hb. exact Hy.
Qed.

Theorem continuous_iff_open_preimage : forall f : Q -> Q,
  continuous f <->
  (forall S : Q -> Prop, is_open S -> is_open (fun x => S (f x))).
Proof.
  intro f. split.
  - intros Hc S HS. exact (continuous_preserves_open_preimage f Hc S HS).
  - apply open_preimage_implies_continuous.
Qed.
```

После добавления этих двух теорем в `Topology.v` (счёт файла станет 21 Qed) слова главы верны без правки.

**(б) Поправить слова** (если формализацию не трогать):

> (189–191) И его ToS не постулирует отдельно, а *выводит* из $\delta$-$\varepsilon$ определения: функция,
> непрерывная в этом смысле, сохраняет открытость при взятии прообраза.
>
> (221–222) непрерывная функция уважает топологическую структуру, построенную предыдущей главой.
>
> (243–246) Сама непрерывность есть *конституция* в локальной форме ($\delta$-$\varepsilon$); из неё § 3.2.3
> вывел топологическую форму («прообраз открытого открыт»).
>
> (285) | непрерывность ($\delta$-$\varepsilon$ $\Rightarrow$ прообраз открытого открыт) | конституция | Rule (конструкт.) |

## Расхождение 2. `process_EVT` не переносит результат теоремы об экстремуме (стр. 993–997)

**Было:**

> Третий файл — `ProcessEVT.v` (133 строки) — играет ту же роль, что `ProcessIVT.v` для теоремы о промежуточном
> значении: тонкая обёртка, переносящая результат на язык процессов `ProcessCore`. Мосты Cauchy-совместимости
> (`evt_cauchy_ compat`), `sup_process_cauchy`, `process_EVT`;

**Проверка.** `process_EVT` (`src/process/ProcessEVT.v:89`):

```coq
Theorem process_EVT : forall (f : ContinuousFunction) (a b : Q),
  a < b ->
  EVT_ERR.uniformly_continuous_on f a b ->
  exists (sup_proc : RealProcess),
    ProcessCore.is_Cauchy sup_proc /\
    exists (maximizer : RealProcess),
      ProcessCore.in_interval a b maximizer.
```

`Print Assumptions`: `Classical_Prop.classic`. В заключении функция `f` не участвует. В пробном файле
(`CheckEVT.v`) то же заключение доказано для любой `f` при одной посылке `a < b` — постоянными процессами `0` и
`a`; ответ компилятора — Closed under the global context. Для сравнения: `process_IVT` (`ProcessIVT.v:128`)
переносит все три члена `IVT_process`.

**В чём расхождение.** Теорема утверждает существование какого-то процесса Коши и какого-то процесса в отрезке;
равенство $f(c)=M$ и мажорирующее свойство из `EVT_complete` на язык `ProcessCore` не перенесены. Содержательна в
файле `sup_process_cauchy` (свойство Коши процесса значений).

**(а) Довести формализацию.** Возможно; набросок проверен (`CheckEVT.v`), цена — та же, что у `EVT_complete`
(`Classical_Prop.classic`):

```coq
Theorem process_EVT_full : forall (f : Q -> Q) (a b : Q),
  a < b ->
  EVT_ERR.uniformly_continuous_on f a b ->
  exists (M c : ProcessCore.RealProcess),
    ProcessCore.is_Cauchy M /\
    ProcessCore.in_interval a b c /\
    (forall n : nat, f (c n) == M n) /\
    (forall x : Q, a <= x <= b ->
       forall eps : Q, 0 < eps ->
         exists N : nat, forall n : nat, (N <= n)%nat -> f x <= M n + eps).
Proof.
  intros f a b Hab Hcont.
  destruct (EVT_complete f a b Hab Hcont) as [M [c [HM [Hc [Hfc Hle]]]]].
  exists M, c. split; [| split; [| split]].
  - apply evt_cauchy_to_process. exact HM.
  - intro n. exact (Hc n).
  - intro n. exact (Hfc n).
  - intros x Hx eps Heps.
    destruct (Hle x Hx eps Heps) as [N HN].
    exists (S N). intros n Hn. apply HN. lia.
Qed.
```

Этой формулировкой можно заменить нынешнюю `process_EVT`: в `src` на неё никто не ссылается.

**(б) Поправить слова:**

> Третий файл — `ProcessEVT.v` (137 строк) — задуман как такая же обёртка, что `ProcessIVT.v` для теоремы о
> промежуточном значении. На язык процессов `ProcessCore` в нём перенесено свойство Коши процесса значений: мосты
> Cauchy-совместимости (`evt_cauchy_compat`) и теорема `sup_process_cauchy`. Теорема `process_EVT` записана
> слабее: она утверждает существование процесса Коши и процесса в отрезке, не связывая их с функцией; равенство
> $f(c)=M$ и мажорирующее свойство из `EVT_complete` на этот язык пока не перенесены.

## Расхождение 3. `evt_convergence_rate`: число записано определением (стр. 998)

**Было:** «`evt_convergence_rate` фиксирует темп — $1/2$.»

**Проверка.** `Definition evt_convergence_rate : Q := 1 # 2.` (`ProcessEVT.v:121`); единственная лемма о нём —
`evt_rate_valid : 0 < evt_convergence_rate /\ evt_convergence_rate < 1`. Процесс значений —
`sup_process f a b := fun n => max_on_grid f a b (S n)` (`EVT_ERR.v:117`): сетка шага $n$ состоит из $n+1$ отрезка,
её шаг $(b-a)/(n+1)$. Вычисление (`CheckEval.v`) для $f(x)=x(1-x)$ на $[0,1]$: отклонение $1/4 -$ `sup_process n`
при $n = 2, 4, 6, 8, 10, 12$ равно $1/36,\ 1/100,\ 1/196,\ 1/324,\ 1/484,\ 1/676$ — убывает как $1/(n+1)^2$, не
вдвое за шаг. Шапка файла говорит «doubling points at each step»; определению сетки это не соответствует.

**В чём расхождение.** Число $1/2$ с процессом значений ни одной теоремой не связано, и для сетки, которая на
каждом шаге получает один новый отрезок, такого темпа нет.

**(а) Довести формализацию.** До слов «темп $1/2$» — нельзя: для этой сетки утверждение неверно. Можно доказать
действительную оценку — для функции с константой Липшица $K$ (проверено в `CheckIdx.v`, Closed under the global
context):

```coq
Lemma lipschitz_grid_rate : forall f a b n x K,
  a < b -> (n > 0)%nat -> a <= x <= b -> 0 <= K ->
  (forall y z, a <= y <= b -> a <= z <= b -> Qabs (f y - f z) <= K * Qabs (y - z)) ->
  f x <= max_on_grid f a b n + K * ((b - a) / inject_Z (Z.of_nat n)).
```

Замечание: константа `evt_convergence_rate` используется в `src/process/ProcessUnified.v` (равенства
`ivt_convergence_rate == evt_convergence_rate` и подобные); правка определения затронет этот файл.

**(б) Поправить слова:** фразу снять, закончив перечисление на «`sup_process_cauchy`, `process_EVT`.»; либо:

> Константа `evt_convergence_rate` в файле записана, но с процессом значений теоремой не связана: сетка шага $n$
> состоит из $n+1$ отрезка, и её шаг убывает как $1/n$.

## Расхождение 4. В `EVT_strong_process` нет мажорирующего свойства (стр. 985–986)

**Было:** «То же честное содержание, что и в `EVT_complete` (§ 3.6.4): сходимость доказана для процесса *значений*;»

**Проверка.** `EVT_strong_process` (`src/EVT_idx.v:663`):
`a < b -> uniformly_continuous_on f a b -> is_Cauchy (sup_process f a b) /\ (forall n, a <= argmax_process f a b n <= b) /\ (forall n, sup_process f a b n = f (argmax_process f a b n))`
— три члена; третий верен по определению (`max_is_f_of_argmax`, доказательство — `reflexivity`). В `EVT_complete`
(`EVT_ERR.v:929`) есть четвёртый: `forall x, a <= x <= b -> process_le (fun _ => f x) M`. Нужное свойство в
`EVT_idx.v` доказано леммой `f_bounded_by_grid_max` (`:506`), но в теорему не внесено. Цена `EVT_strong_process` —
`EVT_idx.classic`.

**В чём расхождение.** Без мажоранты теорема не говорит, что процесс значений приближает именно наибольшее
значение функции на отрезке; содержание рекомендуемой версии уже, чем у исторической.

**(а) Довести формализацию.** Возможно; набросок проверен (`CheckIdx.v`), цена — `EVT_idx.classic`, как у всего
файла:

```coq
Theorem EVT_idx_majorant : forall f a b,
  a < b ->
  uniformly_continuous_on f a b ->
  forall x, a <= x <= b ->
    forall eps, eps > 0 ->
      exists N, forall n, (n > N)%nat -> f x <= sup_process f a b n + eps.
Proof.
  intros f a b Hab Hcont x Hx eps Heps.
  destruct (Hcont eps Heps) as [delta [Hdelta Hdc]].
  assert (Hba : b - a > 0) by (apply Qlt_minus_pos; exact Hab).
  destruct (Archimedean_nat (b - a) delta Hba Hdelta) as [N [HN_pos HN]].
  exists N. intros n Hn.
  assert (Hspacing : (b - a) / inject_Z (Z.of_nat (S n)) < delta).
  { apply Qle_lt_trans with ((b - a) / inject_Z (Z.of_nat N)).
    - apply Qdiv_le_compat_l;
        [exact Hba | unfold Qlt, inject_Z; simpl; lia | unfold Qle, inject_Z; simpl; lia].
    - exact HN. }
  apply Qlt_le_weak. unfold sup_process.
  apply f_bounded_by_grid_max with delta; try assumption.
  lia.
Qed.
```

Этот член можно внести четвёртым в `EVT_strong_process` (в `src` на неё никто не ссылается) — тогда слова главы
верны без правки. Вариант без допущений — см. раздел «Наблюдение».

**(б) Поправить слова:**

> Содержание — три первых члена `EVT_complete` (§ 3.6.4): процесс значений — Коши, позиции лежат в отрезке,
> значение равно $f$ от позиции. Мажорирующего свойства в формулировке `EVT_strong_process` нет; в index-версии
> оно доказано отдельной леммой `f_bounded_by_grid_max`. Сходимость доказана для процесса *значений*;

## Расхождение 5. Процесс позиций: утверждение без теоремы и неверный довод (стр. 826–831; то же на стр. 987–989)

**Было:**

> Но и детерминированности мало: даже с однозначно выбираемой позицией процесс `argmax_process` над $ℚ$ Cauchy
> быть не обязан. Максимум может приближаться к иррациональной точке, и тогда процесс рациональных приближений
> позиции к Cauchy-процессу не сводится; или позиция может перескакивать с одной стороны на другую при измельчении
> сетки.

**Проверка.** В `src` нет ни теоремы о свойстве Коши у `argmax_process`, ни контрпримера; источник слов —
комментарий `EVT_idx.v:699` («may not be Cauchy (limit could be irrational)»). Первый довод неверен: позиции,
сходящиеся к иррациональной точке, образуют процесс Коши — как корень в § 3.4; у такого процесса нет лишь
рационального предела. Второй довод верен и проверен: в пробном файле `CheckArgmax.v` для функции с двумя равными
пиками в $1/3$ и $1/2$ доказано

```coq
Definition tent (c x : Q) : Q := 1 - 6 * Qabs (x - c).
Definition two_peaks (x : Q) : Q := Qmax 0 (Qmax (tent (1#3) x) (tent (1#2) x)).

Theorem two_peaks_uniformly_continuous : forall a b, uniformly_continuous_on two_peaks a b.
Theorem argmax_two_peaks_not_Cauchy : ~ is_Cauchy (argmax_process two_peaks 0 1).
Theorem argmax_process_need_not_be_Cauchy :
  exists f : Q -> Q, uniformly_continuous_on f 0 1 /\ ~ is_Cauchy (argmax_process f 0 1).
```

(определения — из `EVT_idx.v`; все три — Closed under the global context). Ход: на сетке из $6N+2$ отрезков узел
$1/2$ есть, узла $1/3$ нет, и позиция равна $1/2$; на сетке из $6N+3$ отрезков — наоборот, позиция равна $1/3$;
разность $1/6$ не становится меньше $1/12$. Обе точки рациональны, процесс значений на этих шагах равен $1$.

**В чём расхождение.** Глава утверждает факт о формальном объекте, которого формализация не доказывает, и
объясняет его причиной, которая свойству Коши не мешает.

**(а) Довести формализацию.** Возможно: внести контрпример теоремой (например, файлом рядом с `EVT_idx.v`); полный
текст — `CheckArgmax.v`, 253 строки, 22 Qed, без допущений. Тогда слова «не обязан быть Коши» (стр. 815,
826, 987, 1139, 1182) получают машинную опору.

**(б) Поправить слова** (нужно в обоих случаях — довод об иррациональной точке следует снять):

> (826–831) Но и детерминированности мало: даже с однозначно выбираемой позицией процесс `argmax_process` Cauchy
> быть не обязан. Если у функции два равноценных максимума, сетки разных шагов попадают то в один, то в другой, и
> позиция перескакивает между ними, сколько бы шагов ни прошло. (Приближение позиции к иррациональной точке
> свойству Коши не мешает: такой процесс — Коши, у него лишь нет рационального предела, как у корня в § 3.4.)
> Процесс значений от этого перескока свободен.
>
> (987–989) о процессе позиций комментарий `EVT_idx.v` говорит прямо — Коши он быть не обязан.

## Расхождение 6. Максимизатор назван Cauchy-процессом в отрезке (стр. 264–266)

**Было:** «искомый объект — корень или максимизатор — играет роль *Cauchy-процесса в $[a,b]$*, сходящегося к
перемене знака или к супремуму.[^2]»

**Проверка.** Для корня верно: `bisection_is_Cauchy` (`IVT_ERR.v:219`), `bisection_in_interval` (`:182`). Для
максимизатора доказано только `argmax_in_interval` (`EVT_ERR.v:321`, `EVT_idx.v:634`) — принадлежность отрезку;
свойства Коши нет. Процесс Коши — процесс значений, и он «в $[a,b]$» не лежит. Слова взяты из шапки
`ProcessEVT.v` (строки 2–3: «Elements: grid maximizers… Roles: Cauchy process in [a,b], approaching supremum»).

**В чём расхождение.** Шапка файла приписывает максимизатору свойство, которого теоремы не дают; та же глава в
§ 3.6.3 говорит обратное.

**(а) Довести формализацию.** Нельзя: утверждение неверно (контрпример расхождения 5). Стоит поправить шапку
`ProcessEVT.v`.

**(б) Поправить слова:**

> В двух больших теоремах роль иная: корень играет роль *Cauchy-процесса в $[a,b]$*, сходящегося к перемене
> знака; у максимума эту роль несёт процесс *значений*, приближающий супремум, а процесс позиций лишь лежит в
> $[a,b]$.[^2]

## Расхождение 7. `lipschitz_uniform_cont`: в блоке кода опущена посылка (стр. 428–435)

**Было:** блок

```coq
Theorem lipschitz_uniform_cont : forall f a b L,
  Lipschitz_on f a b L ->
  uniformly_continuous_on f a b.
```

**Проверка.** `src/analysis/HeineBorelComplete.v:307`:
`forall f a b K, a <= b -> Lipschitz_on f a b K -> uniformly_continuous_on f a b` — Closed under the global
context. Посылка `a <= b` в доказательстве не используется. Теорема без неё — `lipschitz_uniform`
(`src/analysis/Continuity.v:64`); в пробном файле утверждение `HeineBorelComplete` без посылки получено из неё
одной строкой.

**В чём расхождение.** Блок, поданный как запись из `HeineBorelComplete.v`, совпадает с теоремой другого файла.

**(а) Довести формализацию.** Возможно: снять неиспользуемую посылку `a <= b` в `HeineBorelComplete.v:307`;
единственное применение — в том же файле, строка 541 (`apply lipschitz_uniform_cont with K; [exact Hab|].`), его
нужно поправить вместе с теоремой.

**(б) Поправить слова:** либо вписать в блок посылку (`forall f a b K, a <= b -> Lipschitz_on f a b K -> …`), либо
сослаться на головной файл:

> Этот вывод формализован в головном файле `analysis/Continuity.v` теоремой:
>
> ```coq
> Theorem lipschitz_uniform : forall f a b K,
>   Lipschitz_on f a b K -> uniformly_continuous_on f a b.
> ```
>
> (в `HeineBorelComplete.v`, с которым глава встречалась в § 2.6, стоит та же теорема под именем
> `lipschitz_uniform_cont`, с дополнительной посылкой $a \le b$).

## Расхождение 8. `ivt_cauchy_real` на лемме `continuous_compose_cauchy` не стоит (стр. 723–725)

**Было:** «Главная теорема `ivt_cauchy_real` и её следствие `ivt_cauchy_real_equiv` (которое выражает результат
через `cauchy_equiv` с постоянным нулём) стоят на этой лемме.»

**Проверка.** Доказательство `ivt_cauchy_real` (`src/IVT_CauchyReal.v:320–329`) применяет
`bisection_cauchy_seq`, `bisection_cauchy_in_interval`, `bisection_f_converges_to_zero`; леммы
`continuous_compose_cauchy` в нём нет. Её применяет следствие — через `compose_cauchy_seq` (`:137`, `:351`).
Следствие объявлено словом `Corollary`, но выводится не из `ivt_cauchy_real`, а заново.

**В чём расхождение.** На лемме стоит одно следствие, не главная теорема.

**(а) Довести формализацию.** Не требуется: формализация верна, расходятся слова.

**(б) Поправить слова:**

> На этой лемме стоит следствие `ivt_cauchy_real_equiv` (которое выражает результат через `cauchy_equiv` с
> постоянным нулём): лемма превращает $f \circ c$ в объект типа `CauchySeq`. Главная теорема `ivt_cauchy_real`
> обходится без неё — её заключение записано прямо, через $|f(c_n)| < \varepsilon$.

## Расхождение 9. `UniformConvergence.v`: «обмен с производной» и «теорема Дини» (стр. 1076–1078)

**Было:** «Файл `UniformConvergence.v` — шире этой одной теоремы: в нём есть и обмен предела с интегралом, и обмен
с производной, и теорема Дини.»

**Проверка.**

- Обмен с интегралом — `integral_limit_exchange` (`:310`): суммы Римана функций `fn k` и предельной `f` на любой
  сетке отличаются не больше чем на `eps * (b - a)` при больших `k`. Содержательно.
- «Обмен с производной» — `derivative_limit_exchange` (`:517`). Заключение:
  `Qabs ((f x - f a) - (fn n x - fn n a)) <= eps * (b - a)` при больших `n`. Предельная производная `g` в него не
  входит, а посылки о производных (`udiff_on (fn n) (fn' n) a b`, `uniform_converges fn' g a b`) в доказательстве
  не используются. В пробном файле (`Check.v`, `derivative_exchange_conclusion_from_pointwise`) то же заключение
  получено из одной поточечной сходимости. Теоремы «предел дифференцируем, и его производная есть `g`» в файле
  нет; первая попытка её записать (`:470`) оборвана командой `Abort`.
- «Теорема Дини» — `dini_monotone` (`:641`): если в каждом из конечного числа узлов сетки значения `fn n`
  становятся меньше `eps`, то есть общий номер для всех узлов. Монотонности в условии нет, посылка `a < b` не
  используется, о сходимости на отрезке заключение не говорит.

Все три — Closed under the global context.

**В чём расхождение.** Из трёх названных результатов в файле в полном смысле есть один; два других носят имена
теорем, содержания которых не утверждают.

**(а) Довести формализацию.** Теорему Дини в классической форме над ℚ довести нельзя: она неверна по той же
причине, что теорема Кантора–Гейне (пример: $g_n(x)=\max(0,\,1-n\,|x^2-2|)$ на $[1,2]\capℚ$ — монотонно убывает и
поточечно стремится к нулю, но верхняя грань при каждом $n$ равна единице; компилятором не проверялось). Теорема
об обмене предела с производной — предмет главы о производной; что именно там доказывать, решается при её аудите.

**(б) Поправить слова:**

> Файл `UniformConvergence.v` — шире этой одной теоремы: в нём есть обмен предела с интегралом (для сумм Римана),
> оценки приращений при равномерной сходимости и сеточная лемма о конечном числе узлов.

Соответственно на стр. 1083–1084 и 1146–1148 слова «обмен предела с интегралом и производной» стоит свести к
«обмен предела с интегралом».

## Расхождение 10 (цена). «Аксиомы понадобятся … к двум большим теоремам» (стр. 228–229)

**Было:** «Аксиомы понадобятся дальше — когда глава перейдёт к двум большим теоремам анализа.»

**Проверка.** `IVT_process`, `process_IVT`, `ivt_cauchy_real` — Closed under the global context; `EVT_complete` —
`Classical_Prop.classic`; `EVT_strong_process` — `EVT_idx.classic`. Сама глава на стр. 69–71 и 644–647 говорит,
что теорема о промежуточном значении обходится без допущений.

**(б) Стало:** «Аксиома понадобится дальше — когда глава перейдёт к теореме об экстремуме; теорема о промежуточном
значении обойдётся без неё.»

## Расхождение 11 (цена). Пометка $L3$ в таблице разбора (стр. 287)

**Было:** «| равномерность как требование (Кантор–Гейне над $ℚ$ неверна) | усиление правила | Rule (неполнота, $L3$) |»

**Проверка.** `cantor_heine_fails_Q`, `lipschitz_uniform`, `lipschitz_uniform_cont`, `IVT_process` — Closed under
the global context. В теореме об экстремуме `classic` применяется в одной лемме — `x_between_grid_points` (поиск
ячейки сетки); с требованием равномерности он не связан.

**(б) Стало:** «| равномерность как требование (Кантор–Гейне над $ℚ$ неверна) | усиление правила | Rule (неполнота $ℚ$) |»

## Расхождение 12 (цена, статус). Цена `uniform_limit_continuous_on` оставлена «проверке», проверка даёт ответ (стр. 1086–1099)

**Было:** «Однако без отдельной проверки `Print Assumptions` именно этой теоремы глава не утверждает её аксиомной
чистоты … суждение о его аксиомной чистоте оставляет этой проверке.»

**Проверка.** `Print Assumptions uniform_limit_continuous_on` — Closed under the global context; то же у
`uniform_limit_continuous_at` и у всех 20 утверждений файла. Шапка файла («AXIOMS: classic (inherited from
MonotoneConvergence via udiff_on)») называет цену по импортам.

**(б) Стало** (взамен абзаца на стр. 1086–1099):

> И — по уговору § 3.1 — слово об аксиомном статусе. Шапка файла `UniformConvergence.v` называет `classic`: файл
> подключает результаты о монотонной сходимости и дифференцировании. Проверка `Print Assumptions` показывает
> иное: для `uniform_limit_continuous_on` ответ — «Closed under the global context», теорема о равномерном пределе
> доказана без допущений. Это пример правила, заведённого ещё в Главе 4.6: аксиомный статус устанавливается по
> `Print Assumptions` *конкретной* теоремы, а не приписывается ей от заголовка файла.

## Расхождение 13 (числа)

- **Стр. 98:** «Опорных файлов девять, все сверены с репозиторием дословно.» В главе названо 12 файлов `.v`
  (`Topology`, `UniformConvergence`, `analysis/Continuity`, `HeineBorelComplete`, `IVT_ERR`, `ProcessIVT`,
  `IVT_CauchyReal`, `EVT_ERR`, `EVT_idx`, `ProcessEVT`, `ProcessContinuity`, `ToS_Axioms`) и ещё `CantorHeineQ.v` —
  теоремами сноски 3. Девять получается без `analysis/Continuity.v`, `ProcessContinuity.v` и `ToS_Axioms.v`; первый
  из них § 3.3.1 называет головным. Из 16 блоков кода три отличаются от исходника: стр. 119 (запись неравенств —
  по смыслу то же), стр. 206 (порядок кванторов и слово `Theorem` — по смыслу то же), стр. 432 (расхождение 7).
  Предложение: «Опорных файлов десять — с головным `analysis/Continuity.v`; блоки кода сверены с репозиторием.»
  Какое число верно, зависит от того, что считать опорным, — решает автор.
- **Стр. 993:** «`ProcessEVT.v` (133 строки)» — в файле 137 строк (правка 12.11 добавила пять строк и убрала одну).
  Стало: «(137 строк)».

Остальные числа главы верны: `IVT_ERR.v` — 424 строки и 23 Qed; `ProcessIVT.v` — 175 строк; `IVT_CauchyReal.v` —
382 строки; `ProcessContinuity.v` — 36 строк; `CantorHeineQ.v` — 11 Qed.

## Расхождение 14 (имена)

- **Стр. 177–178, 996–997, 1147–1148:** имена в обратных кавычках разорваны переводом строки и на странице
  читаются с пробелом: «identity_ continuous», «evt_cauchy_ compat», «Uniform Convergence.v». Объявления и файл
  существуют; нужно поставить каждое имя на одну строку.
- **Стр. 687:** «как и теорема `IVT_ERR`» — теоремы с таким именем нет, это имя файла. Стало: «как и теорема
  `IVT_process`».
- **Стр. 806–807:** «`argmax`» — такого имени в формализации нет; позицию дают `argmax_list` и `argmax_on_grid`
  (`EVT_ERR.v:89`, `:99`), в index-версии — `argmax_idx` и `argmax_on_grid` (`EVT_idx.v:93`, `:617`). Стало:
  «*Позиция* максимума — `argmax_on_grid`, тот узел…».
- **Стр. 1125:** «(`continuous_at`, `continuous`, `continuous_on`) … (`Topology.v`)» — `continuous_on` объявлено не
  в `Topology.v`, а в `UniformConvergence.v:142` (и, в другой записи, в `analysis/Continuity.v:41`). Стало:
  «$\delta$-$\varepsilon$ определение (`continuous_at`, `continuous` в `Topology.v`; `continuous_on` в
  `UniformConvergence.v`), алгебра непрерывных функций, прообраз открытого открыт; конструктивно, без аксиом.»

## Наблюдение (не расхождение): теорема об экстремуме доказуема без допущений

Слова главы о цене теоремы об экстремуме (стр. 68–71, 100, 1134, 1176) совпадают с ответом компилятора:
`EVT_complete` — `Classical_Prop.classic`, `EVT_strong_process` — `EVT_idx.classic`. Проверка показала, откуда
берётся это допущение: в обеих версиях `classic` применяется в одной лемме — `x_between_grid_points`
(`EVT_idx.v:403`, `EVT_ERR.v:364`), которая для точки отрезка находит ячейку сетки. Этот шаг вычислим: сравнение
дробей разрешимо (`Qlt_le_dec`), перебор узлов конечен. В пробном файле (`CheckIdx.v`, модуль `Constructive`)
лемма доказана без `classic`:

```coq
Lemma x_between_aux : forall a b n x m,
  (m <= n)%nat -> (0 < m)%nat ->
  grid_point a b n O <= x -> x <= grid_point a b n m ->
  exists k, (k < m)%nat /\ grid_point a b n k <= x <= grid_point a b n (S k).
Proof.
  intros a b n x m. induction m as [|m' IH]; intros Hmn Hpos Hlo Hhi.
  - lia.
  - destruct (Qlt_le_dec x (grid_point a b n m')) as [Hlt | Hge].
    + destruct m' as [|m''].
      * exfalso. apply (Qlt_irrefl x).
        apply Qlt_le_trans with (grid_point a b n O); assumption.
      * assert (H1 : (S m'' <= n)%nat) by lia.
        assert (H2 : (0 < S m'')%nat) by lia.
        destruct (IH H1 H2 Hlo (Qlt_le_weak _ _ Hlt)) as [k [Hk Hbetween]].
        exists k. split; [lia | exact Hbetween].
    + exists m'. split; [lia | split; assumption].
Qed.

Lemma x_between_grid_points : forall a b n x,
  a < b -> (n > 0)%nat -> a <= x <= b ->
  exists k, (k < n)%nat /\ grid_point a b n k <= x <= grid_point a b n (S k).
Proof.
  intros a b n x Hab Hn [Hax Hxb].
  apply (x_between_aux a b n x n); [lia | lia | |].
  - rewrite grid_point_0 by lia. exact Hax.
  - rewrite grid_point_n_is_b by lia. exact Hxb.
Qed.
```

С этой леммой доказательства `near_grid_point`, `f_bounded_by_grid_max`, `sup_process_is_Cauchy` из `EVT_idx.v`
проходят дословно, и полная index-версия — с мажорантой расхождения 4 —

```coq
Theorem EVT_idx_complete : forall f a b,
  a < b ->
  uniformly_continuous_on f a b ->
  is_Cauchy (sup_process f a b) /\
  (forall n, a <= argmax_process f a b n <= b) /\
  (forall n, sup_process f a b n = f (argmax_process f a b n)) /\
  (forall x, a <= x <= b ->
     forall eps, eps > 0 ->
       exists N, forall n, (n > N)%nat -> f x <= sup_process f a b n + eps).
```

получает ответ «Closed under the global context». Если эту правку внести в `EVT_idx.v` (заменить доказательство
одной леммы и снять локальное `Axiom classic`, строка 338), обе большие теоремы главы окажутся без допущений, и
слова о цене на стр. 68–85, 99–100, 228–229, 1009–1021, 1134, 1174–1179 потребуют пересмотра. В `EVT_ERR.v`
`classic` применяется в той же единственной лемме (строка 384), так что тем же способом должны освободиться и
`EVT_complete`, и три теоремы `ProcessEVT.v`; для `EVT_ERR.v` цепочка в пробном файле не пересобиралась. Решение —
за автором.

## Сомнительные места (не расхождения)

- **Два определения `continuous_on`** (стр. 134–147, 341–343, 1081–1082, 1140). Блок § 3.2.1 и теорема о
  равномерном пределе используют запись через приращение (`UniformConvergence.v:142`); каноном § 3.3.1 называет
  другую запись — через $x$ и $x_0$ (`analysis/Continuity.v:41`), на ней стоит контрпример сноски 3; третья —
  `HeineBorel_ERR.v:562`. Моста между ними в формализации нет. Проверено (`Check.v`): каноническая запись влечёт
  запись через приращение без условий (`canon_continuous_on_to_increment`); обратно — для функций, уважающих
  равенство дробей (`increment_continuous_on_to_canon`); теорема о равномерном пределе верна и для канонической
  записи (`uniform_limit_continuous_canon`). Все три — Closed under the global context. Слова стр. 143–147
  («главная интервальная форма») и стр. 340–343 («канон») называют главными разные записи.
- **Стр. 426–427, случай $L=0$.** `Lipschitz_on` требует $K>0$ (`HeineBorelComplete.v:72`, `Continuity.v:55`):
  вырожденный случай определением исключён и в формализации не разбирается (потери общности нет). В доказательстве
  `lipschitz_uniform_cont` $\delta = \varepsilon/(K+1)$, в `lipschitz_uniform` — $\varepsilon/K$, как в главе.
- **Стр. 680, `ivt_convergence_rate`.** Это тоже число, записанное определением (`ProcessIVT.v:172`), и
  `ivt_rate_valid` даёт лишь $0<1/2<1$. В отличие от расхождения 3, сам темп доказан: `bisection_width_bound`
  (`ProcessIVT.v:155`), ширина равна $(b-a)/2^n$. Слово «фиксирует» читается как «записывает».
- **Стр. 936–938, «доказывается одним словом `reflexivity`».** Словом `reflexivity` закрывается только равенство;
  принадлежность узла списку доказана отдельно, всё доказательство `max_on_grid_attained` — одиннадцать строк
  (`EVT_idx.v:216–226`). Одним словом доказана соседняя `max_is_f_of_argmax` (`:625`).
- **Стр. 894–896, «доказать её в задуманном виде не удалось».** `max_list_attained` в задуманном виде неверна:
  если запасное значение `d` больше всех элементов списка, максимум равен `d` и в списке не лежит (комментарий
  `EVT_ERR.v:587–590`). Обходной вариант `max_list_attained_classical`, вопреки имени, — Closed under the global
  context.
- **Стр. 815–822, пример постоянной функции.** Для действующих определений позиция у постоянной функции
  постоянна: вычислено на $[0,1]$ — $b$ в `EVT_ERR`, $a$ в `EVT_idx`. Глава это оговаривает («без фиксированного
  правила выбора»); комментарий `EVT_ERR.v:923–924` («constant functions have non-Cauchy argmax») для действующего
  определения неверен.
- **Стр. 968–980, какой узел выделен.** Вычислено: список узлов идёт от $b$ к $a$, обновление при равенстве
  выбирает последний по списку — то есть самый левый узел (на плато $[1/4,3/4]$ index-версия даёт $1/4$,
  argmax-версия — $3/4$). Комментарий файла называет его «первым». Осторожность главы оправдана; можно назвать
  узел прямо.
- **Стр. 1138 и 1181–1182, теорема Кантора–Гейне в списках «Не построено» и «что остаётся открытым».** Отказ
  теоремы машинно доказан (`cantor_heine_fails_Q`, сноска 3). Не построена сама теорема, потому что она ложна;
  контрпример построен, и его место — в списке «Построено и проверено».
- **Стр. 68–69, «`classic` — объект из файла `ToS_Axioms.v`».** `ToS_Axioms.v` аксиому не объявляет, а
  переэкспортирует из стандартной библиотеки (строка 31); в рекомендуемой версии `EVT_idx.v` аксиома объявлена
  локально (`:338`) — об этом сама глава говорит в § 3.7.4.
- **Стр. 670, «`Archimedean_ERR`, откуда пришла бисекция».** Бисекция определена в `IVT_ERR.v`; из
  `Archimedean_ERR.v` приходит определение `is_Cauchy`.
- **Тип `ContinuousFunction` в блоках кода** (стр. 520, 552, 614, 701) — это `Q -> Q` (`IVT_ERR.v:49`);
  непрерывности он не требует, условие несёт отдельная посылка. На формулировки не влияет.
- **Стр. 776–779, «измельчаем сетку, добавляя узлы».** Сетка шага $n+1$ не содержит сетку шага $n$: каждый шаг
  строит новую равномерную сетку с одним лишним отрезком. Процесс значений поэтому не монотонен (вычислено для
  $f(x)=x(1-x)$: отклонение от $1/4$ равно нулю при $n = 1, 3, 5, 7$ и положительно при $n = 2, 4, 6, 8$).

## Вне главы: шапки файлов

Для сведения (в главе эти строки не цитируются, кроме отмеченных выше):

- `IVT_ERR.v:29` — «AXIOMS: classic (L3) + Archimedean»; `IVT_CauchyReal.v:19` — «AXIOMS: classic»;
  `ProcessIVT.v:22` — «inherits classic from IVT_ERR». По компилятору допущений нет ни у одной теоремы этих файлов,
  названной в главе.
- `UniformConvergence.v:15` — «AXIOMS: classic»; все 20 утверждений файла — Closed under the global context.
- `ProcessEVT.v:6` — «0 axioms»; три теоремы из девяти стоят на `Classical_Prop.classic`. Там же, строка 4, —
  «doubling points at each step» (сетка получает один отрезок за шаг).
- `EVT_ERR.v:12` — «34 Qed» (в файле 35); `:28` — «grid has 2^n points» (узлов $n+2$ на шаге $n$).
- `HeineBorelComplete.v:16` — «22 Qed» (в файле 28).

## Дополнительные проверки

- Все 19 лемм `Topology.v`, все 13 утверждений `ProcessIVT.v`, все 6 теорем `analysis/Continuity.v`, все 4 леммы
  `ProcessContinuity.v`, все 20 утверждений `UniformConvergence.v` — Closed under the global context.
- `ProcessEVT.v` после правки 12.11: шесть утверждений без допущений, три (`sup_process_cauchy`, `process_EVT`,
  `evt_is_process_construction`) — на `Classical_Prop.classic`; теорема `evt_p4_interpretation`
  (`forall q, is_Cauchy (const_process q)`) в главе не упоминается.
- Ход доказательств `IVT_process` (оценка через левый и правый конец, слабый инвариант, архимедовость),
  `continuous_preserves_open_preimage`, `uniform_limit_continuous_at` (три слагаемых по $\varepsilon/3$) сверен с
  исходником: описан верно.
- Заключения `IVT_process`, `process_IVT`, `ivt_cauchy_real`, `EVT_complete` пересказаны в главе как
  эпсилон-утверждения; точного нуля и точного максимума глава формализации не приписывает.
