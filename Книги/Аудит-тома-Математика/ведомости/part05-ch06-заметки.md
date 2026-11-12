# Глава V.6 «Основная теорема анализа» — заметки к ведомости (12.11.2026)

Ведомость: `part05-ch06.json` — 103 ручные записи + 9 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты: ok — 97, mismatch-statement — 14 (девять расхождений, часть повторена в
нескольких местах главы), wrong-number — 1. Расхождений по цене нет: глава цену своих теорем не называет
(стр. 661–664), а `Print Assumptions` для всех 45 названных лемм и теорем даёт `Closed under the global context`
у 44 и `Classical_Prop.classic` у `monotone_bounded_Cauchy`, которую глава сама приводит как пример классической.
Отсутствующих имён нет (`Qeq`, `Proper` — стандартная библиотека; `reflexivity` — тактика; `proc_d` — связанная
переменная в утверждении теоремы); оба блока кода (стр. 88–92) совпадают с исходником.

Пробные доказательства: `C:/Users/abary/tos-audit-build/_part05/ch06/Check.v` и `Check2.v` — оба компилируются,
у всех утверждений `Closed under the global context`.

## Что проверить не удалось

- Слова главы о том, чего в формализации нет (общего цепного правила — стр. 500; аддитивности интеграла по
  отрезку — стр. 578; слабых производных и пространств Соболева — стр. 595; функции-интеграла с переменным верхним
  пределом и основной теоремы на `RealPoint` — стр. 624–625), проверены поиском по `src`, а не компилятором.
  Поиск их подтверждает.
- Верно ли точное неубывание `f a <= f b` и сходимость процесса Римановых сумм к `f b - f a` БЕЗ условия
  `Proper (Qeq ==> Qeq) f`, не устанавливалось: наброски ниже это условие используют (перенос `f` из последнего
  узла сетки в точку `b`).
- Перекрёстные ссылки на параграфы глав 5.4 и 5.5 сверены только по заголовкам страниц. Английская страница и
  LaTeX-исходник главы не смотрелись.

Остальное проверено по исходникам и компилятору.

## Расхождение 1. Доказан один уровень сетки на каждое ε — написано «сходится», «точность растёт с измельчением» (стр. 151–154, 267–270, 285–288, 347, 681–686)

**Было:**

> (151–154) …и связь между ними тоже процессная: семейство сеточных оценок, уточняющихся с измельчением.
>
> (269–270) Там, где классический анализ ставит знак равенства, здесь стоит $\le\varepsilon\cdot(b-a)$ при
> достаточно мелкой сетке.
>
> (286–288) …там процесс разностных отношений сходился к наклону, здесь процесс Римановых сумм производной
> сходится к приращению.
>
> (347) Чем мельче сетка, тем меньше этот остаток.
>
> (683–686) …семейство приближений, в котором на каждом уровне сетки Риманова сумма производной приближает
> приращение функции, а точность растёт с измельчением.

**Проверка.** `ftc_grid` (`src/RiemannIntegration.v:314`):
`udiff_on f f' a b -> 0 < eps -> exists N : nat, let step := (b - a) / inject_Z (Z.of_nat (S N)) in
Qabs (riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a)) <= eps * (b - a)`.
`Print Assumptions ftc_grid`: `Closed under the global context`. Квантор — `exists N`: один уровень сетки на
каждое `eps`. О сетках мельче найденной утверждение молчит; монотонности ошибки по уровню нет. Утверждения
`process_equiv (integral_process f' a b) (const_process (f b - f a))` в `src` нет: `integral_process`
встречается в `ProcessFTC.v`, `ProcessIntegral.v`, `ProcessLebesgue.v`, `ProcessPicard.v`, `ProcessSimple.v`, и
ни один из них сходимости к приращению не доказывает. Сама глава на стр. 100–104 говорит, что `ProcessFTC.v`
убывания ошибки не доказывает и что оценку даёт `ftc_grid`; но и `ftc_grid` убывания не утверждает. Для сравнения:
у производной сходимость записана — `deriv_process_converges` есть `process_equiv` (`ProcessDerivative.v:152`).

**Простыми словами:** доказано, что для каждой точности найдётся одна подходящая сетка; не записано, что все
более мелкие сетки тоже подходят и что процесс Римановых сумм производной сходится к приращению.

**(а) Довести формализацию до слов главы — возможно, без новых аксиом; набросок проверен.** Нужны три
утверждения. Первое — оценка `rs_tele_error_bound` на любом уровне `n`, шаг которого меньше `delta` (текст
доказательства — существующее доказательство `rs_tele_error_bound`, строки 231–306, с `n` вместо выбранного `N`;
в `Check.v` — лемма `rs_tele_error_bound_at`). Второе и третье:

```coq
Lemma walk_step_antitone : forall (a b : Q) (N n : nat),
  a < b -> (N <= n)%nat ->
  (b - a) / inject_Z (Z.of_nat (S n)) <= (b - a) / inject_Z (Z.of_nat (S N)).
Proof.
  intros a b N n Hab Hle.
  assert (HN : 0 < inject_Z (Z.of_nat (S N))) by apply inject_Z_Sn_pos.
  assert (Hmono : inject_Z (Z.of_nat (S N)) <= inject_Z (Z.of_nat (S n))).
  { rewrite <- Zle_Qle. lia. }
  assert (Hinv := Qinv_le_compat_local _ _ HN Hmono).
  unfold Qdiv.
  apply Qmult_le_l; [lra | exact Hinv].
Qed.

(* Сеточная основная теорема: оценка верна на ВСЕХ уровнях начиная с N. *)
Theorem ftc_grid_eventually : forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  0 < eps ->
  exists N : nat, forall n : nat, (N <= n)%nat ->
    Qabs (riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) -
          (f (walk_point a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)) - f a)) <=
    eps * (b - a).
Proof.
  intros f f' a b eps [Hab Hudiff] Heps.
  destruct (Hudiff eps Heps) as [delta [Hdelta Hbd]].
  destruct (walk_step_small a b delta Hab Hdelta) as [N HN].
  exists N. intros n Hn.
  assert (Hstep_n : (b - a) / inject_Z (Z.of_nat (S n)) < delta).
  { apply Qle_lt_trans with ((b - a) / inject_Z (Z.of_nat (S N)));
      [apply walk_step_antitone; assumption | exact HN]. }
  assert (Hb := rs_tele_error_bound_at f f' a b eps delta n Hab Heps Hbd Hstep_n).
  set (step := (b - a) / inject_Z (Z.of_nat (S n))) in *.
  assert (Htele : tele_sum f a step (S n) == f (walk_point a step (S n)) - f a)
    by apply telescope_collapse.
  assert (Heq : riemann_sum f' a step (S n) - (f (walk_point a step (S n)) - f a) ==
                riemann_sum f' a step (S n) - tele_sum f a step (S n)).
  { rewrite Htele. reflexivity. }
  qabs_rw Heq. exact Hb.
Qed.

(* Процессная основная теорема: процесс Римановых сумм производной
   сходится к приращению f(b) - f(a) (для f, уважающей Qeq). *)
Theorem ftc_process_converges : forall (f f' : Q -> Q) (a b : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  process_equiv (integral_process f' a b) (const_process (f b - f a)).
Proof.
  intros f f' a b Hp Hud eps Heps.
  assert (Hab : a < b) by (destruct Hud; assumption).
  assert (Hba : 0 < b - a) by lra.
  set (eps' := eps * (1#2) / (b - a)).
  assert (Heps' : 0 < eps').
  { unfold eps'. apply Qlt_shift_div_l; lra. }
  destruct (ftc_grid_eventually f f' a b eps' Hud Heps') as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  unfold integral_process, integral_step, const_process.
  assert (Hend := walk_endpoint_qeq a b n Hab).
  rewrite (Hp _ _ Hend) in HN.
  assert (Hcalc : eps' * (b - a) == eps * (1#2)).
  { unfold eps'. field. lra. }
  rewrite Hcalc in HN.
  apply Qle_lt_trans with (eps * (1#2)); [exact HN | lra].
Qed.
```

Следствие `ftc_error_process_vanishes` (`process_equiv (ftc_error_process f f' a b) (const_process 0)` при тех же
условиях) проверено там же. `Print Assumptions` у всех четырёх: `Closed under the global context`. Естественное
место — `process/ProcessFTC.v`: он подключает `ProcessDerivative` (`inject_Z_Sn_pos`, `Qinv_le_compat_local`),
`ProcessIntegral`, `MeanValueTheorem`, `RiemannIntegration`. Два замечания. Первое: после такой правки
`ProcessFTC.v` перестаёт быть только обёрткой, и слова стр. 100–110 и 671–676 потребуют обновления. Второе:
доказывается сходимость (ошибка в пределах `eps` на всех уровнях начиная с `N`), а не монотонное убывание ошибки
от уровня к уровню; слова «точность растёт с измельчением» и после правки стоит читать как «ошибка стремится к
нулю». Условие `Proper` нужно только для сравнения с `f b`; `ftc_grid_eventually` его не требует.

**(б) Поправить слова.**

> (151–154) …и связь между ними тоже процессная: семейство сеточных оценок — для каждой точности $\varepsilon$
> найдётся сетка, на которой оценка выполнена.
>
> (269–270) Там, где классический анализ ставит знак равенства, здесь стоит $\le\varepsilon\cdot(b-a)$ на
> некотором уровне сетки, своём для каждого $\varepsilon$.
>
> (286–288) …там процесс разностных отношений сходился к наклону; здесь доказано меньше: для каждого
> $\varepsilon$ найдётся уровень, на котором Риманова сумма производной отстоит от приращения не более чем на
> $\varepsilon(b-a)$. Сходимость самого процесса Римановых сумм к приращению в формализации пока не записана.
>
> (347) Для каждого $\varepsilon$ найдётся сетка, на которой этот остаток не превосходит $\varepsilon(b-a)$.
>
> (683–686) …семейство приближений: для всякой точности $\varepsilon$ найдётся уровень сетки, на котором
> Риманова сумма производной приближает приращение функции с ошибкой не больше $\varepsilon(b-a)$.

## Расхождение 2. `ftc_nonneg_integral`: заключение верно без основной теоремы и о приращении не говорит (стр. 362–369)

**Было:**

> Лемма `ftc_nonneg_integral` (`RiemannIntegration.v`): при $f'\ge 0$ Риманова сумма производной неотрицательна
> с точностью до сеточной ошибки. Содержательно: неотрицательная производная даёт неубывающее приращение — если
> функция нигде не убывает по скорости, её значение не падает. Это сеточная FTC-форма неотрицательности из § 5.5
> и мост к монотонности § 6.4: знак производной управляет ростом приращения.

**Проверка.** `ftc_nonneg_integral` (`src/RiemannIntegration.v:386`):
`udiff_on f f' a b -> (forall x, a <= x -> x <= b -> 0 <= f' x) -> 0 < eps -> exists N, let step := … in
-(eps * (b - a)) <= riemann_sum f' a step (S N)`. `Print Assumptions`: `Closed under the global context`.
В доказательстве (строки 393–439) оценка из `ftc_grid` получена (`HN1`, `Hrs_lo`), но в итог не входит: последний
шаг — `apply Qle_trans with 0`, где `0 <= riemann_sum …` взято из `riemann_sum_nonneg` (`:89`), а
`-(eps * (b - a)) <= 0` очевидно. Функция `f` в заключении не участвует; посылка `udiff_on` нужна только ради
`a < b`. При `f' >= 0` Риманова сумма неотрицательна точно и на каждом уровне; это проверено отдельной леммой
(`riemann_sum_deriv_nonneg_exact` в `Check.v`: `a < b -> (forall x, a <= x -> x <= b -> 0 <= g x) ->
0 <= riemann_sum g a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)` для любого `N`).

**Простыми словами:** лемма подана как следствие основной теоремы о приращении функции, а её вывод — более слабая
запись простого факта «сумма неотрицательных слагаемых неотрицательна»; о приращении функции она не говорит.

**(а) Довести формализацию до слов главы.** Слова «неотрицательная производная даёт неубывающее приращение»
закрываются не этой леммой, а точной теоремой о неубывании — она доказуема, см. расхождение 3
(`nonneg_deriv_nondecreasing`, набросок проверен). Саму `ftc_nonneg_integral` честно либо заменить точным
утверждением `forall N, 0 <= riemann_sum f' a step (S N)` (следствие `riemann_sum_nonneg` и
`walk_point_in_interval`, без `eps` и без `f`), либо оставить как есть и не называть FTC-формой.

**(б) Поправить слова.**

> Лемма `ftc_nonneg_integral` (`RiemannIntegration.v`): при $f'\ge 0$ Риманова сумма производной на некотором
> уровне сетки не меньше $-\varepsilon(b-a)$. Это осторожная запись более простого факта: при $f'\ge 0$ и
> положительном шаге Риманова сумма неотрицательна точно, на каждом уровне (`riemann_sum_nonneg`), и основная
> теорема для этого не нужна. Связь знака производной с приращением функции даёт не эта лемма, а монотонность
> § 6.4: там неотрицательная производная влечёт приращение, не меньшее $-\varepsilon(b-a)$.

## Расхождение 3. `ftc_monotone`: зазор ε пересказан как точная неотрицательность (стр. 385–386)

**Было:**

> Лемма `ftc_monotone`: при $f'\ge 0$ функция растёт на сетке (приращение неотрицательно);

**Проверка.** `ftc_monotone` (`src/analysis/FTC.v:225`):
`udiff_on f f' a b -> (forall x, a <= x -> x <= b -> 0 <= f' x) -> 0 < eps -> exists N, let step := … in
-(eps * (b - a)) <= f (walk_point a step (S N)) - f a`. `Print Assumptions`: `Closed under the global context`.
Утверждение то же, что у `nonneg_deriv_approx_nondec` (`MeanValueTheorem.v:558`). Оценено приращение до
последнего узла, на одном уровне `N`, с зазором `eps * (b - a)`; о промежуточных узлах лемма не говорит.

**Простыми словами:** доказано «приращение не меньше −ε(b−a) на некоторой сетке», написано «приращение
неотрицательно».

**(а) Довести формализацию до слов главы — возможно, без новых аксиом, для функций, уважающих `Qeq`; набросок
проверен.**

```coq
Theorem nonneg_deriv_nondecreasing : forall (f f' : Q -> Q) (a b : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> 0 <= f' x) ->
  f a <= f b.
Proof.
  intros f f' a b Hp Hud Hnn.
  assert (Hab : a < b) by (destruct Hud; assumption).
  destruct (Qlt_le_dec (f b) (f a)) as [Hlt | Hle]; [| exact Hle].
  exfalso.
  set (eps := (f a - f b) * (1#2) / (b - a)).
  assert (Heps : 0 < eps).
  { unfold eps. apply Qlt_shift_div_l; lra. }
  destruct (ftc_monotone f f' a b eps Hud Hnn Heps) as [N HN].
  cbv zeta in HN.
  assert (Hend := walk_endpoint_qeq a b N Hab).
  rewrite (Hp _ _ Hend) in HN.
  assert (Hcalc : eps * (b - a) == (f a - f b) * (1#2)).
  { unfold eps. field. lra. }
  rewrite Hcalc in HN. lra.
Qed.
```

`Print Assumptions`: `Closed under the global context`. Почему верно: зазор `eps` произволен, а значение в
последнем узле при `Proper f` равно `f b`; если бы `f b < f a`, половина этой разности, взятая за `eps * (b - a)`,
дала бы противоречие. Вместе с `udiff_sub_interval` (`FTC.v:622`) отсюда следует неубывание на всём отрезке:
`a <= x < y <= b -> f x <= f y`. Условие `Proper` существенно для наброска; без него вопрос не решался.

**(б) Поправить слова.**

> Лемма `ftc_monotone`: при $f'\ge 0$ приращение функции до последнего узла сетки не меньше $-\varepsilon(b-a)$ —
> для каждого $\varepsilon>0$ на своём уровне сетки (сеточная, приближённая форма неубывания);

## Расхождение 4. `ftc_error_const`: эквивалентность процессов пересказана как нуль на каждом уровне (стр. 320–322)

**Было:**

> То есть $\int_a^b c = c (b-a) = f(b)-f(a)$ *точно*: ошибка тождественно нулевая на каждом уровне. Это
> *точный процессный случай* основной теоремы.

**Проверка.** `ftc_error_const` (`src/process/ProcessFTC.v:119`):
`a < b -> process_equiv (ftc_error_process (fun x => c * x) (fun _ => c) a b) (const_process 0)`;
`process_equiv R1 R2` (`ProcessCore.v:170`) — `forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
Qabs (R1 n - R2 n) < eps`. `Print Assumptions`: `Closed under the global context`. Опорная
`integral_process_const` (`ProcessIntegral.v:64`) записана так же. В обоих доказательствах берётся `N = 0` и
разность равна нулю, но в утверждения это не вынесено; леммы с поуровневым равенством в этих файлах нет.

**Простыми словами:** лемма утверждает «начиная с некоторого уровня ошибка меньше любого ε»; глава читает
«ошибка равна нулю на каждом уровне» — это верно, но отдельным утверждением не записано.

**(а) Довести формализацию до слов главы — возможно; набросок проверен.**

```coq
Lemma integral_process_const_exact : forall c a b n,
  integral_process (fun _ => c) a b n == c * (b - a).
Proof.
  intros c a b n. unfold integral_process.
  rewrite riemann_sum_const.
  unfold integral_step. field.
  intro H. assert (Hp := inject_Z_Sn_pos n). lra.
Qed.

Lemma ftc_error_const_exact : forall c a b n,
  ftc_error_process (fun x => c * x) (fun _ => c) a b n == 0.
Proof.
  intros c a b n. unfold ftc_error_process.
  rewrite integral_process_const_exact. ring.
Qed.
```

`Print Assumptions` у обеих: `Closed under the global context`. Посылка `a < b` не нужна. Место — первая в
`ProcessIntegral.v`, вторая в `ProcessFTC.v`.

**(б) Поправить слова.**

> То есть процесс ошибки эквивалентен нулевому: начиная с некоторого уровня ошибка меньше любого $\varepsilon$.
> На деле она равна нулю уже на каждом уровне — это видно из доказательства, — но лемма записана в форме
> эквивалентности процессов. Это *точный процессный случай* основной теоремы.

## Расхождение 5. Телескоп: равенство в лемме — `Qeq`, не лейбницево (стр. 224–227)

**Было:**

> Совпадение *лейбницево-точное*, поскольку узлы заданы рекурсивной `walk_point` из § 5.4, а не замкнутой
> формулой — та же honest-деталь, что разбиралась в главе о производной.

**Проверка.** `telescope_collapse` (`src/RiemannIntegration.v:207`):
`tele_sum f a step n == f (walk_point a step n) - f a` — знак `==`, равенство рациональных чисел (`Qeq`).
`Print Assumptions`: `Closed under the global context`. Те же слова («Leibniz-exact») стоят в шапке файла,
строка 8. Лейбницево равенство (`=`) для этой пары термов неверно — проверено компилятором:

```coq
Lemma telescope_not_leibniz :
  exists (f : Q -> Q) (a step : Q) (n : nat),
    tele_sum f a step n <> f (walk_point a step n) - f a.
Proof.
  exists (fun x => x), (1#2), (1#3), 2%nat.
  vm_compute. intro H. discriminate H.
Qed.
```

(слева получается терм `864 # 1296`, справа `24 # 36`: числа равны, записи разные).

**Простыми словами:** лемма доказывает равенство чисел, а не буквальное совпадение записей; буквально совпадают
узлы сетки, и именно это избавляет от требования, чтобы функция уважала `Qeq`.

**(а) Довести формализацию до слов главы нельзя:** лейбницево равенство ложно (контрпример выше), над ℚ суммы
дробей не приводятся к несократимому виду.

**(б) Поправить слова.**

> Равенство здесь — равенство рациональных чисел (`Qeq`). Лейбницево-точны сами узлы: `walk_point` из § 5.4
> задана рекурсивно, так что $y_{k+1}$ есть буквально $y_k+\texttt{step}$, и значение $f(y_k)$ входит в соседние
> слагаемые одним и тем же термом; поэтому телескоп сворачивается без требования, чтобы $f$ уважала `Qeq`. Та же
> honest-деталь разбиралась в главе о производной.

Стоит поправить и комментарий в шапке `RiemannIntegration.v:8` («Telescoping sum collapse (Leibniz-exact)»).

## Расхождение 6. `ftc_absolute_value_bound` названа опорой § 6.5, но там не используется (стр. 410–412)

**Было:**

> Она понадобится в § 6.5: в правиле произведения и интегрировании по частям множители придётся ограничивать, и
> эта лемма даёт нужный контроль.

**Проверка.** `ftc_absolute_value_bound` (`src/analysis/FTC.v:299`) — оценка `Qabs (riemann_sum f a step (S N))
<= M * (b - a)` для произвольной `f` при границе `M` в узлах; обёртка `riemann_sum_abs_bound`. Поиск по `src`:
имя встречается только в объявлении и в строке `Check` того же файла. В `udiff_product`, `ftc_product`,
`integration_by_parts` (`IntegralApplications.v:210, 422, 447`) границы `Mf, Mg, Mf', Mg'` — посылки о значениях
функций и производных на отрезке, а не оценки Римановых сумм. `IntegralApplications.v` подключается в `FTC.v`,
а не наоборот, так что вызвать лемму в доказательствах § 6.5 нельзя.

**Простыми словами:** лемма названа инструментом § 6.5, а в доказательствах § 6.5 её нет.

**(а) Довести формализацию до слов главы.** Делать здесь нечего: правило произведения и интегрирование по частям
доказаны полностью без этой леммы; встроить её можно было бы только искусственно.

**(б) Поправить слова.**

> В § 6.5 похожий контроль понадобится для множителей — там он входит прямо в условия: правило произведения и
> интегрирование по частям требуют границ $M_f, M_g, M_{f'}, M_{g'}$ на значения функций и производных.

## Расхождение 7. В доказательстве `integration_by_parts` нет `riemann_sum_sub` (стр. 461–462)

**Было:**

> Доказательство — `ftc_product` плюс линейность Римановых сумм (`riemann_sum_add`, `riemann_sum_sub`).

**Проверка.** Доказательство `integration_by_parts` (`src/IntegralApplications.v:463–489`): `ftc_product`, затем
`riemann_sum_add` (`Hadd`), затем `Qabs_wd` и `lra`. Лемма `riemann_sum_sub` объявлена в `analysis/FTC.v:506`
(и вторая, одноимённая, в `UniformConvergence.v:255`); `FTC.v` сам подключает `IntegralApplications.v`, поэтому
в этом доказательстве она недоступна.

**Простыми словами:** названа лемма, которой в доказательстве нет и быть не может.

**(а) Довести формализацию до слов главы.** Не требуется: доказательство полно без `riemann_sum_sub`.

**(б) Поправить слова.**

> Доказательство — `ftc_product` плюс аддитивность Римановых сумм (`riemann_sum_add`).

## Расхождение 8. Аффинная замена переменной: один знак, форма основной теоремы, неназванное условие (стр. 501–508)

**Было:**

> Есть только *аффинный* случай: `udiff_chain_affine` (`FTC.v`) — цепное правило для внутренней функции
> $g = c\cdot x + d$ при $c>0$, и `udiff_chain_affine_neg` при $c<0$. На них построена аффинная замена переменной
> в интеграле `ftc_u_substitution_affine`. То есть подстановка $u = g(x)$ доказана лишь для линейной $g$; общая
> замена с произвольной гладкой $g$ не формализована.

**Проверка.** `ftc_u_substitution_affine` (`src/analysis/FTC.v:414`):
`Proper (Qeq ==> Qeq) f -> c > 0 -> udiff_on f f' (c * a + d) (c * b + d) -> a < b -> 0 < eps -> exists N,
let step := … in Qabs (riemann_sum (fun x => f' (c * x + d) * c) a step (S N) -
(f (c * walk_point a step (S N) + d) - f (c * a + d))) <= eps * (b - a)`.
`Print Assumptions`: `Closed under the global context`. Три наблюдения. (1) В доказательстве вызвана только
`udiff_chain_affine` (случай `c > 0`); `udiff_chain_affine_neg` (`:434`) дальше нигде не используется, леммы о
замене при `c < 0` нет. (2) Утверждение сравнивает Риманову сумму функции `f'(cx+d)·c` с приращением `f(cx+d)` —
это сеточная основная теорема для сложной функции, левая часть формулы замены; равенства двух интегралов (по `x`
на `[a,b]` и по `u` на `[ca+d, cb+d]`) в формализации нет. (3) У обеих цепных лемм и у леммы о замене есть посылка
`Proper (Qeq ==> Qeq) f`, в главе не названная.

**Простыми словами:** замена построена на одной цепной лемме из двух и только для `c > 0`; доказана не связь
двух интегралов, а основная теорема для `f(cx+d)`; условие «функция уважает `Qeq`» опущено.

**(а) Довести формализацию до слов главы — возможно, без новых аксиом; набросок проверен.** Точное равенство двух
Римановых сумм при аффинной замене (любой знак `c`, любой шаг, любое число узлов) и лемма о замене при `c < 0`:

```coq
Lemma riemann_sum_affine_subst :
  forall (phi : Q -> Q) (a step c d : Q) (n : nat),
  Proper (Qeq ==> Qeq) phi ->
  riemann_sum (fun x => phi (c * x + d) * c) a step n ==
  riemann_sum phi (c * a + d) (c * step) n.
Proof.
  intros phi a step c d n Hp. induction n as [| n IH].
  - reflexivity.
  - assert (HL : riemann_sum (fun x => phi (c * x + d) * c) a step (S n) ==
                 phi (c * walk_point a step n + d) * c * step +
                 riemann_sum (fun x => phi (c * x + d) * c) a step n) by reflexivity.
    assert (HR : riemann_sum phi (c * a + d) (c * step) (S n) ==
                 phi (walk_point (c * a + d) (c * step) n) * (c * step) +
                 riemann_sum phi (c * a + d) (c * step) n) by reflexivity.
    assert (Hnode : c * walk_point a step n + d ==
                    walk_point (c * a + d) (c * step) n).
    { rewrite !walk_point_qeq. ring. }
    rewrite HL, HR, IH, (Hp _ _ Hnode). ring.
Qed.

Lemma ftc_u_substitution_affine_neg :
  forall (f f' : Q -> Q) (a b c d eps : Q),
  Proper (Qeq ==> Qeq) f ->
  c < 0 ->
  udiff_on f f' (c * b + d) (c * a + d) ->
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' (c * x + d) * c) a step (S N) -
          (f (c * walk_point a step (S N) + d) - f (c * a + d))) <=
    eps * (b - a).
Proof.
  intros f f' a b c d eps Hp Hc Hud Hab Heps.
  assert (Hcomp : udiff_on (fun x => f (c * x + d)) (fun x => f' (c * x + d) * c) a b).
  { apply udiff_chain_affine_neg; assumption. }
  exact (ftc_grid _ _ a b eps Hcomp Heps).
Qed.
```

`Print Assumptions` у обеих: `Closed under the global context`. Первая лемма и есть замена переменной на уровне
сумм: узлы сетки по `x` переходят в узлы сетки по `u = cx + d` с шагом `c·step`, множитель `c` переходит в шаг.
Место — `analysis/FTC.v`, раздел 3.

**(б) Поправить слова.**

> Есть только *аффинный* случай: `udiff_chain_affine` (`FTC.v`) — цепное правило для внутренней функции
> $g = c\cdot x + d$ при $c>0$, и `udiff_chain_affine_neg` при $c<0$; обе — для внешней функции, уважающей `Qeq`
> (`Proper`). На первой построена лемма `ftc_u_substitution_affine`: при $c>0$ Риманова сумма функции
> $f'(cx+d)\cdot c$ по отрезку $[a,b]$ приближает приращение $f(cx+d)$. Это сеточная основная теорема для сложной
> функции — левая часть формулы замены; для $c<0$ такой леммы нет, и равенство двух интегралов (по $x$ и по $u$)
> отдельной теоремой не записано. Общая замена с произвольной гладкой $g$ не формализована.

## Расхождение 9. `udiff_implies_bounded`: оценено одно значение, в приложениях лемма не участвует (стр. 353–358, 521–524)

**Было:**

> (353–358) …леммы вроде `udiff_implies_bounded` (оценка значений функции через производную) и
> `lipschitz_bounded` (ограниченность липшицевой функции) помогают контролировать классы функций, на которых
> сеточные рассуждения применяются устойчиво, — это полезно для приложений § 6.4–6.5, а не для самой центральной
> оценки.
>
> (521–524) …`udiff_implies_bounded` — оценка значений через слой теоремы о среднем.

**Проверка.** `udiff_implies_bounded` (`src/analysis/FTC.v:568`):
`udiff_on f f' a b -> (forall x, a <= x -> x <= b -> Qabs (f' x) <= M) -> 0 <= M -> 0 < eps -> exists N,
let step := … in Qabs (f (walk_point a step (S N))) <= Qabs (f a) + (M + eps) * (b - a)`.
`Print Assumptions`: `Closed under the global context`. Оценено одно значение — в последнем узле одной сетки (по
числу это точка `b`); о значениях во внутренних точках отрезка лемма не говорит. `lipschitz_bounded` (`:601`)
оценивает `|f x - f a|` на всём отрезке — к ней замечаний нет. Поиск по `src`: ни та, ни другая лемма нигде не
используются; в `IntegralApplications.v` (§ 6.5) они недоступны (порядок подключения файлов обратный), и границы
значений там — посылки.

**Простыми словами:** лемма оценивает значение функции в одной точке, а названа оценкой значений функции; в
приложениях § 6.4–6.5 она не используется.

**(а) Довести формализацию до слов главы — возможно, без новых аксиом, для функций, уважающих `Qeq`; набросок
проверен** (`Check2.v`). Цепочка: точная оценка приращения → липшицевость → ограниченность на отрезке.

```coq
Lemma udiff_increment_exact : forall (f f' : Q -> Q) (a b M : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  Qabs (f b - f a) <= M * (b - a).
Proof.
  intros f f' a b M Hp Hud HM.
  assert (Hab : a < b) by (destruct Hud; assumption).
  destruct (Qlt_le_dec (M * (b - a)) (Qabs (f b - f a))) as [Hlt | Hle]; [| exact Hle].
  exfalso.
  set (D := Qabs (f b - f a)) in *.
  set (eps := (D - M * (b - a)) * (1#2) / (b - a)).
  assert (Heps : 0 < eps).
  { unfold eps. apply Qlt_shift_div_l; lra. }
  destruct (bounded_deriv_bounded_increment f f' a b M eps Hud HM Heps) as [N HN].
  cbv zeta in HN.
  assert (Hend := walk_endpoint_qeq a b N Hab).
  rewrite (Hp _ _ Hend) in HN. fold D in HN.
  assert (Hcalc : (M + eps) * (b - a) == M * (b - a) + (D - M * (b - a)) * (1#2)).
  { unfold eps. field. lra. }
  rewrite Hcalc in HN. lra.
Qed.

Theorem udiff_bounded_on : forall (f f' : Q -> Q) (a b M : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 <= M ->
  forall x : Q, a <= x -> x <= b ->
    Qabs (f x) <= Qabs (f a) + M * (b - a).
```

Доказательство `udiff_bounded_on` — через `udiff_bounded_deriv_lipschitz` (см. раздел «Возможные усиления») и
`lipschitz_bounded`; полный текст в `Check2.v`. `Print Assumptions`: `Closed under the global context`. С такой
теоремой границы значений `Mf`, `Mg` в правиле произведения можно было бы выводить из границ производных — тогда
слова «полезно для приложений § 6.5» стали бы верны.

**(б) Поправить слова.**

> (353–358) …леммы вроде `udiff_implies_bounded` (оценка значения функции в последнем узле сетки через границу
> производной) и `lipschitz_bounded` (ограниченность липшицевой функции на отрезке) — заготовки для контроля
> классов функций; в доказательствах § 6.4–6.5 они не используются, и центральной оценке не нужны.
>
> (521–524) …`udiff_implies_bounded` — оценка значения в последнем узле сетки через слой теоремы о среднем.

## Расхождение 10. Число `Qed` в `ProcessFTC.v` (стр. 655)

**Было:**

> `ProcessFTC.v` — « 8 Qed, 0 axioms ».

**Проверка.** Шапка процитирована точно (`src/process/ProcessFTC.v:6` и `:22` — «8 Qed»), но действительный
счёт — 9 (`grep -c 'Qed\.'`): `ftc_zero_deriv`, `ftc_const_deriv`, `ftc_linearity`, `ftc_scaling`,
`ftc_interval_split`, `ftc_error_const`, `ftc_rate_valid`, `ftc_is_process_construction`,
`derivative_integral_duality`. Объявлений `Axiom` и `Parameter` в файле нет; у всех девяти
`Closed under the global context`. Для справки, действительный счёт в остальных названных файлах (глава этих
чисел не приводит): `RiemannIntegration.v` — 18, `FTC.v` — 28 (столько же в его шапке), `IntegralApplications.v` —
19, `Differentiation.v` и `MeanValueTheorem.v` — по 18.

**Простыми словами:** число взято из устаревшей шапки файла; в файле на одно доказанное утверждение больше.

**(а) Со стороны формализации:** поправить шапку `ProcessFTC.v` (строки 6 и 22): 8 → 9. Код не меняется.

**(б) Поправить слова.**

> `ProcessFTC.v` — « 8 Qed, 0 axioms » (действительный счёт — 9 Qed).

После правки шапки — просто « 9 Qed, 0 axioms ».

## Возможные усиления (расхождением не являются)

Стр. 518–531: глава говорит, что теоремы «`udiff_on` ⇒ `Lipschitz_on`» в формализации нет. Это верно, статус
назван честно. Такая теорема доказуема без новых аксиом для функций, уважающих `Qeq`; набросок проверен
(`Check2.v`, `Closed under the global context`):

```coq
Theorem udiff_bounded_deriv_lipschitz : forall (f f' : Q -> Q) (a b M : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  0 <= M ->
  Lipschitz_on f a b M.
```

Ход: для `x < y` из `[a,b]` — `udiff_sub_interval` (`FTC.v:622`) и `udiff_increment_exact` на `[x,y]`; случай
`y < x` симметричен; случай `x == y` — по `Proper`. Если автор примет эту теорему в `FTC.v`, раздел
«Липшицевость и равномерная непрерывность» можно будет переписать: иерархия «равномерно дифференцируема с
ограниченной производной ⇒ липшицева ⇒ равномерно непрерывна» станет цепочкой из двух теорем.

## Сомнительные места (расхождением не являются)

- Стр. 428–430: «Во-первых, `product_decomp` раскладывает приращение произведения…». Лемма существует и содержит
  именно это тождество, но в доказательстве `udiff_product` не вызывается: тождество получено на месте тактикой
  `ring` (`IntegralApplications.v:277–280`), имя стоит только в комментарии (`:269`). Глава в похожем случае
  (`ftc_grid` в `ProcessFTC.v`) это различие оговаривает.
- Стр. 418: правило произведения названо «главным нелинейным приложением основной теоремы». `udiff_product`
  основную теорему не использует (`ftc_grid` в доказательстве нет); приложением основной теоремы является
  следующая лемма, `ftc_product`.
- Стр. 397–398: «`ftc_sum_rule` (она же `ftc_linearity`)». Имя `ftc_linearity` объявлено дважды с разными
  утверждениями: `RiemannIntegration.v:530` (сеточная форма для суммы — она и вызвана в `ftc_sum_rule`) и
  `process/ProcessFTC.v:77` (поуровневая аддитивность `integral_process`). Глава называет оба файла; стоит указать
  файл рядом с именем.
- Стр. 307, 615, 687: «точная теорема для аффинной функции». `ftc_error_const` доказана для `f(x) = c·x`, без
  свободного члена; аффинная `c·x + d` — только в `ftc_affine`, в форме `exists N`.
- Стр. 310: «единственный нетривиальный содержательный факт файла». Оценка, не утверждение о формализации;
  `ftc_zero_deriv` в том же файле тоже доказана индукцией, а не ссылкой.
- В `ProcessFTC.v` есть определение `ftc_convergence_rate : Q := 1 # 2` с леммой `ftc_rate_valid`
  (`0 < 1/2 < 1`) — число, вписанное руками, ни с какой оценкой скорости сходимости не связанное. Глава его не
  называет; это девятое `Qed` файла.
- Неиспользуемые посылки: `a < b` в `ftc_zero_deriv`, `ftc_is_process_construction`,
  `derivative_integral_duality`; `a < m`, `m < b` в `ftc_interval_split`; `0 <= M` в `ftc_increment_bound`.
  О трёх из этих утверждений глава сама говорит, что они скромны.
- Стр. 387–392: «строгий рост», «глобальное „функция растёт“». `ftc_strict_monotone` даёт положительность
  приращения до последнего узла на одном уровне сетки; рост на всём отрезке из неё получается применением к
  подотрезкам (`udiff_sub_interval`) и при `Proper f`, отдельной теоремой не записан.
- Стр. 105–106: шапка `ProcessFTC.v` пишет «udiff_on from Differentiation.v»; `udiff_on` объявлен в
  `MeanValueTheorem.v:46`. Глава эти слова не повторяет.
- Нумерация перекрёстных ссылок смешивает две схемы: «§ 5.5.1», «§ 5.5.2», «§ 5.4.4», «§ 5.8» читаются как
  «глава 5, раздел, подраздел», а «§ 5.4», «§ 5.4.2», «§ 5.5.3» — как «часть V, глава, раздел». Так, «линейность
  интеграла § 5.5.3» (стр. 401) по первой схеме указывает на раздел «Интегрируемость как свойство Коши», а
  линейность — третий раздел той главы.
- Стр. 595–601: слабых производных в `src` нет нигде. Слова «Sobolev» и «distribution» в формализации встречаются
  (`navier_stokes/ClassicalRegularity.v`: `sobolev_regularity s := s - 2`; `stdlib/ProcessDistribution.v`), но
  к слабой производной отношения не имеют; слова главы верны.
- Цена. Глава ограничивается общим правилом (стр. 661–664). По компилятору все названные в ней теоремы, кроме
  приведённой как пример `monotone_bounded_Cauchy`, замкнуты; об этом можно сказать прямо.
- Вне главы: `ftc_comparison` (`RiemannIntegration.v:550`, названа в главе 5.5) доказана предъявлением `N = 0`
  и монотонностью суммы; её заключение верно на каждом уровне без зазора `eps` и без `udiff_on`.
  `udiff_lipschitz_bridge` (`analysis/HeineBorelComplete.v:523`) в утверждении `udiff_on` не содержит: её посылка —
  сама липшицева оценка.

## Дополнительные проверки

- Блоки кода главы (стр. 88–92): `ftc_error` и `ftc_error_process` совпадают с `ProcessFTC.v:44` и `:115`.
- Ход доказательств `rs_tele_error_bound`, `ftc_grid`, `ftc_zero_deriv`, `udiff_product`, `integration_by_parts`,
  `antiderivative_unique`, `ftc_interval_split`, `derivative_integral_duality` сверен с исходниками; кроме
  отмеченного выше, описан верно.
- Пересказ шапок `FTC.v` и `ProcessFTC.v` (стр. 117–122, сноска на стр. 711) соответствует строкам
  Elements / Roles / Rules.
- Блоки `Print Assumptions` в конце файлов (стр. 666–671): `RiemannIntegration.v:599–601` (`ftc_grid`,
  `udiff_add`, `ftc_comparison`), `FTC.v:684–687` (`lipschitz_compose`, `lipschitz_uniform_cont`,
  `ftc_u_substitution_affine`, `udiff_sub_interval`); в `ProcessFTC.v` и `IntegralApplications.v` их нет — как
  сказано.
- Локальная аксиома `classic` в `EVT_idx.v:338` и `Classical_Prop.classic` у `monotone_bounded_Cauchy`
  (`ProcessArithmetic.v:311`) — как сказано на стр. 656–659.
