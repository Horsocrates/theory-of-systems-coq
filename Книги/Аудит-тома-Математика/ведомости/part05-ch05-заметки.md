# Глава V.5 «Интеграл» — заметки к ведомости (12.11.2026)

Ведомость: `part05-ch05.json` — 99 ручных записей + 8 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты (107 записей): ok — 87, mismatch-statement — 17 (записи девяти расхождений,
1–9; на первое приходится семь записей), missing-name — 2 (расхождение 10), wrong-number — 1 (расхождение 11),
mismatch-price — 0.

Цена. Расхождений по цене нет. Глава нигде не утверждает «без аксиом» о конкретной теореме и нигде не приписывает
`classic` теореме, которая на нём не стоит. `Print Assumptions` выполнен для всех 135 лемм и теорем восьми файлов
(`RiemannIntegration.v`, `process/ProcessIntegral.v`, `IntegralApplications.v`, `analysis/StepIntegral.v`,
`stdlib/ProcessIntegration.v`, `process/ProcessAnalysis.v`, `analysis/FTC.v`, `process/ProcessArithmetic.v`):
133 — `Closed under the global context`; на `Classical_Prop.classic` стоят только `monotone_bounded_Cauchy` и
`decreasing_bounded_Cauchy` из `ProcessArithmetic.v` — первую глава и называет (стр. 745–749).

Блоки кода главы (пять объявлений) совпадают с исходниками.

Пробные файлы — `C:/Users/abary/tos-audit-build/_part05/ch05/`: `Check1.v` … `Check5.v`, `PaAll.v` (вывод — `PaAll.out`),
`ProcessIntegralNoArith.v`. Все компилируются; у всех новых утверждений `Closed under the global context`.

## Что проверить не удалось

- Утверждения главы вида «в формализации этого нет» (нет предиката интегрируемости; нет общего цепного правила; нет
  леммы, связывающей `riemann_sum` со `step_fun_integral`; нет интеграла на `RealPoint`; нет теоремы о свойстве Коши
  `integral_process` для липшицевых или непрерывных функций) проверены поиском по `src` — по именам и по совместному
  вхождению определений, — а не компилятором. Все подтверждены; объявление под неожиданным именем поиск мог пропустить.
- Слова главы о соседних главах (§ 5.4, главы 5.6 и 5.7, Часть VI) сверялись только в части названных имён;
  содержание тех глав — предмет их ведомостей.
- Номера параграфов в отсылках (§ 5.1.4, § 5.5.3 и т. п.) не сверялись.
- Английская страница и LaTeX-исходник главы не смотрелись.

## Расхождение 1. Сходимость и свойство Коши процесса сумм названы собранными, а доказаны только для константы (стр. 22–24, 118–120, 145–147, 518–520, 533–536, 547–548, 780–782)

Проверка. В формализации есть одна теорема о сходимости `integral_process` — для константы:
`integral_process_const` (`src/process/ProcessIntegral.v:64`) —
`a < b -> process_equiv (integral_process (fun _ => c) a b) (const_process (c * (b - a)))`;
её следствие `const_riemann_cauchy` (`src/process/ProcessSimple.v:85`) даёт `is_Cauchy` для того же процесса константы.
Теорем вида `is_Cauchy (integral_process …)` или `process_equiv (integral_process …) (const_process …)` для
какого-либо непостоянного класса функций в `src` нет (поиск по всем `.v`; `integral_process` встречается в пяти файлах:
`ProcessIntegral.v`, `ProcessFTC.v`, `ProcessLebesgue.v`, `ProcessPicard.v`, `ProcessSimple.v`).

Сеточная оценка, на которую ссылается глава, — `ftc_grid` (`src/RiemannIntegration.v:314`):

```coq
Lemma ftc_grid : forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b -> 0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a)) <= eps * (b - a).
```

`Print Assumptions ftc_grid`: `Closed under the global context`. Квантор — `exists N`: для каждого `eps` назван **один**
уровень. Свойство Коши (`is_Cauchy`, `src/process/ProcessCore.v:68`) говорит о **всех** уровнях начиная с некоторого.
Из утверждения `ftc_grid` оно не следует: оценка на уровне `N` ничего не говорит об уровнях `N+1`, `N+2`, …

В чём расхождение простыми словами: глава говорит, что свойство Коши для регулярных классов «собирается из сеточных
оценок» и «уже поддержано» ими, а в формализации оно доказано только для константы, и названная оценка в нынешней
форме для него недостаточна.

**(а) Довести формализацию до слов главы — возможно, набросок проверен** (`Check2.v`; допущений нет).
Нужны три утверждения. Первое — оценка `ftc_grid` для всех уровней начиная с некоторого:

```coq
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
  assert (Hsmall : (b - a) / inject_Z (Z.of_nat (S n)) < delta).
  { apply Qle_lt_trans with ((b - a) / inject_Z (Z.of_nat (S N))).
    - apply grid_step_antitone; assumption.
    - exact HN. }
  assert (H := rs_tele_error_level f f' a b eps delta n Hab Heps Hbd Hsmall).
  assert (Htele := telescope_collapse f a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)).
  assert (Heq : riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) -
                (f (walk_point a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)) - f a) ==
                riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) -
                tele_sum f a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)).
  { rewrite Htele. reflexivity. }
  rewrite (Qabs_wd _ _ Heq). exact H.
Qed.
```

Она опирается на две вспомогательные леммы. `rs_tele_error_level` — оценка на одном уровне при известном `delta`;
её доказательство есть тело доказательства `rs_tele_error_bound` (строки 231–306 файла), вынесенное наружу без
изменений (полный текст — в `Check2.v`):

```coq
Lemma rs_tele_error_level : forall (f f' : Q -> Q) (a b eps delta : Q) (N : nat),
  a < b -> 0 < eps ->
  (forall x h : Q, a <= x -> x <= b -> 0 < Qabs h -> Qabs h < delta ->
     Qabs (f (x + h) - f x - f' x * h) < eps * Qabs h) ->
  (b - a) / inject_Z (Z.of_nat (S N)) < delta ->
  Qabs (riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S N))) (S N) -
        tele_sum f a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) <= eps * (b - a).
```

`grid_step_antitone` — шаг сетки не растёт с уровнем:

```coq
Lemma grid_step_antitone : forall (a b : Q) (N n : nat),
  a < b -> (N <= n)%nat ->
  (b - a) / inject_Z (Z.of_nat (S n)) <= (b - a) / inject_Z (Z.of_nat (S N)).
Proof.
  intros a b N n Hab Hn.
  assert (HpN := inject_Z_Sn_pos N). assert (Hpn := inject_Z_Sn_pos n).
  assert (Hle : inject_Z (Z.of_nat (S N)) <= inject_Z (Z.of_nat (S n))).
  { rewrite <- Zle_Qle. lia. }
  set (s := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hs : 0 < s) by (apply walk_step_pos; exact Hab).
  assert (HsN : s * inject_Z (Z.of_nat (S N)) == b - a).
  { unfold s. field. intro H. lra. }
  apply Qle_shift_div_r; [exact Hpn |].
  assert (H1 : s * inject_Z (Z.of_nat (S N)) <= s * inject_Z (Z.of_nat (S n))).
  { apply Qmult_le_l; assumption. }
  lra.
Qed.
```

Второе и третье — процессная форма и свойство Коши:

```coq
Theorem integral_process_of_derivative : forall (f f' : Q -> Q) (a b : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  process_equiv (integral_process f' a b) (const_process (f b - f a)).
Proof.
  intros f f' a b Hf Hud eps Heps.
  assert (Hab : a < b) by (destruct Hud; assumption).
  assert (Hba : 0 < b - a) by lra.
  set (e := eps / (2 * (b - a))).
  assert (He : 0 < e).
  { unfold e. apply Qlt_shift_div_l; lra. }
  destruct (ftc_grid_eventually f f' a b e Hud He) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  unfold integral_process, integral_step, const_process.
  assert (Hend : f (walk_point a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)) == f b).
  { apply Hf. apply walk_endpoint_qeq. exact Hab. }
  assert (Heq : riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) - (f b - f a) ==
                riemann_sum f' a ((b - a) / inject_Z (Z.of_nat (S n))) (S n) -
                (f (walk_point a ((b - a) / inject_Z (Z.of_nat (S n))) (S n)) - f a)).
  { rewrite Hend. reflexivity. }
  rewrite (Qabs_wd _ _ Heq).
  assert (Hhalf : e * (b - a) == eps * (1#2)).
  { unfold e. field. lra. }
  lra.
Qed.

Corollary integral_process_of_derivative_Cauchy : forall (f f' : Q -> Q) (a b : Q),
  Proper (Qeq ==> Qeq) f ->
  udiff_on f f' a b ->
  is_Cauchy (integral_process f' a b).
Proof.
  intros f f' a b Hf Hud.
  apply equiv_cauchy_l with (R1 := const_process (f b - f a)).
  - apply process_equiv_sym. apply integral_process_of_derivative; assumption.
  - apply const_is_Cauchy.
Qed.
```

`Print Assumptions` для `ftc_grid_eventually`, `integral_process_of_derivative`,
`integral_process_of_derivative_Cauchy`: `Closed under the global context`.
Условие `Proper (Qeq ==> Qeq) f` («функция уважает равенство рациональных») нужно потому, что конец сетки
`walk_point a step (S n)` равен `b` только в смысле `==` (`walk_endpoint_qeq`, `MeanValueTheorem.v:646`); то же
условие уже стоит в `udiff_chain_affine`. Место для новых утверждений: `ftc_grid_eventually` — в
`RiemannIntegration.v` рядом с `ftc_grid`; две процессные теоремы — в `ProcessIntegral.v`, раздел «Part IV:
Convergence via FTC» (сейчас в нём только лемма о шаге). После этого слова главы о «конкретном регулярном классе»
становятся буквально верными для производных равномерно дифференцируемых функций, а слова шапки `ProcessIntegral.v`
(«Rules: ftc_grid convergence») получают содержание.

**(б) Поправить слова** (если формализация не дополняется).

Стр. 22–24, было:

> равномерная дифференцируемость `udiff_on` из § 5.4 окажется
> именно тем условием, при котором суммы производной сходятся к
> приращению функции.

Стало:

> равномерная дифференцируемость `udiff_on` из § 5.4 окажется
> именно тем условием, при котором суммы производной приближают
> приращение функции с любой заданной точностью.

Стр. 118–120, было:

> Для констант это видно сразу (§ 5.2.1);
> для более широких классов функций свойство Коши собирается из
> сеточных оценок и grid-формы основной теоремы (§ 5.5).

Стало:

> Для констант это доказано (§ 5.2.1);
> для более широких классов функций свойство Коши в опорных файлах не
> доказано: сеточные оценки и grid-форма основной теоремы (§ 5.5) дают
> для него материал, но не саму теорему.

Стр. 145–147, было:

> Честная граница:
> отдельного предиката интегрируемости в ядре нет, свойство Коши
> собирается из сеточных оценок для конкретного класса функций (§ 5.5.3).

Стало:

> Честная граница:
> отдельного предиката интегрируемости в ядре нет, а свойство Коши
> процесса сумм доказано только для констант; для других классов есть
> сеточные оценки, из которых оно ещё не выведено (§ 5.5.3).

Стр. 518–520, было:

> Это его *сеточная,
> приближённая* форма: при достаточно мелкой сетке сумма производной
> сколь угодно близка к приращению.

Стало:

> Это его *сеточная,
> приближённая* форма: для всякой точности найдётся уровень сетки, на
> котором сумма производной отстоит от приращения не больше чем на эту
> точность. Что оценка сохраняется на всех более мелких уровнях, лемма
> не утверждает.

Стр. 533–536, было:

> Для некоторых достаточно регулярных классов это поведение уже
> поддержано сеточными оценками. В частности, `ftc_grid`
> контролирует Римановы суммы производной равномерно дифференцируемой
> функции через приращение самой функции (§ 5.5.2).

Стало:

> Доказано это пока только для констант (§ 5.2.1). Для производной
> равномерно дифференцируемой функции есть сеточная оценка `ftc_grid`:
> на подходящем уровне Риманова сумма близка к приращению самой функции
> (§ 5.5.2). Свойство Коши из неё в нынешней форме не следует: она
> называет один уровень для каждой точности, а свойство Коши говорит обо
> всех уровнях начиная с некоторого.

Стр. 547–548, было:

> Есть сеточные оценки для конкретных классов, из которых свойство Коши
> собирается для конкретной функции.

Стало:

> Есть сеточные оценки для конкретных классов; свойство Коши доказано
> для констант, для остальных классов оно остаётся задачей.

Стр. 780–782, было:

> его законность как интеграла даёт сходимость — свойство
> Коши, которое для конкретных регулярных классов функций собирается из
> сеточных оценок.

Стало:

> его законность как интеграла даёт сходимость — свойство
> Коши; в опорных файлах оно доказано для констант, а для производных
> равномерно дифференцируемых функций подготовлено сеточной оценкой
> `ftc_grid`.

При выборе пути (а) слова главы можно оставить, заменив стр. 533–536 на:

> Для одного регулярного класса это доказано. Если $f$ равномерно
> дифференцируема на $[a,b]$ с производной $f'$ и уважает равенство
> рациональных, то процесс `integral_process` $f' a b$ эквивалентен
> постоянному процессу $f(b)-f(a)$ (`integral_process_of_derivative`) и
> потому есть процесс Коши (`integral_process_of_derivative_Cauchy`).
> Опора — усиленная сеточная оценка `ftc_grid_eventually`: близость суммы
> к приращению на *всех* уровнях начиная с некоторого (§ 5.5.2).

Места, которые при любой правке стоит согласовать с выбранными словами: строка таблицы на стр. 174
(«интегрируемость $=$ свойство Коши (grid-FTC)»), стр. 202–203 и стр. 522–524 («измельчение действительно сближает
сумму с приращением»).

## Расхождение 2. Перечень трёх определений `riemann_sum` (стр. 73–78)

Проверка. Объявлений с именем `riemann_sum` в `src` три: `src/RiemannIntegration.v:39`,
`src/process/ProcessAnalysis.v:110`, `src/process/ProcessMCT.v:111`
(`Definition riemann_sum (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat) : Q := w * q_sum (fun i => f (pts i)) N`).
В `src/stdlib/ProcessIntegration.v:7` объявлено `riemann_sum_01` — другое имя. Все — определения, `Print Assumptions`
к ним — `Closed under the global context`.

В чём расхождение: число «три» верно (и на стр. 769–770 стоит верно), но в перечне третьим названо определение с
другим именем, а файл `ProcessMCT.v` не назван.

**(а)** Формализацию менять не нужно: расхождение в перечне.

**(б)** Было:

> В репозитории есть *три разных*
> определения с именем `riemann_sum`: это, основное, из
> `RiemannIntegration.v` (левая сумма по `walk_point`);
> отдельное `riemann_sum_01` на отрезке $[0,1]$ в
> `ProcessIntegration.v`; и ещё одно, демонстрационное, в
> `ProcessAnalysis.v`. Имена совпадают, определения различны;
> ниже под `riemann_sum` мы всегда понимаем первое, а к
> остальным двум обратимся отдельно в § 5.7, всякий раз называя файл.

Стало:

> В репозитории есть *три разных*
> определения с именем `riemann_sum`: это, основное, из
> `RiemannIntegration.v` (левая сумма по `walk_point`);
> демонстрационное в `ProcessAnalysis.v`; и ещё одно в
> `ProcessMCT.v` (сумма по произвольной последовательности узлов с
> общим весом). Кроме них есть сумма с близким именем
> `riemann_sum_01` на отрезке $[0,1]$ в `ProcessIntegration.v`.
> Определения различны; ниже под `riemann_sum` мы всегда понимаем
> первое, а к суммам из `ProcessAnalysis.v` и `ProcessIntegration.v`
> обратимся отдельно в § 5.7, всякий раз называя файл.

## Расхождение 3. «Имена совпадают» у определений `ProcessAnalysis.v` (стр. 664–668)

Проверка. `process_derivative` (`src/process/ProcessAnalysis.v:26`) и `process_integral` (`:116`) объявлены в `src`
по одному разу. Основные определения носят другие имена: `deriv_process` (`src/process/ProcessDerivative.v:62`) и
`integral_process` (`src/process/ProcessIntegral.v:56`). Совпадает только имя `riemann_sum`
(`ProcessAnalysis.v:110` и `RiemannIntegration.v:39`). При этом значения `process_derivative` и `deriv_process` на
каждом уровне равны (`Check1.v`, без допущений):

```coq
Lemma two_derivative_processes_agree : forall f x K,
  ProcessAnalysis.process_derivative f x K == deriv_process f x K.
Proof.
  intros f x K. rewrite deriv_process_unfold.
  unfold ProcessAnalysis.process_derivative, deriv_step. reflexivity.
Qed.
```

В чём расхождение: совпадает одно имя из трёх; два других лишь похожи на основные.

**(а)** Формализацию менять не обязательно; лемму выше можно добавить как мост между двумя записями
производной-процесса.

**(б)** Было:

> Файл `ProcessAnalysis.v`
> содержит *свои* `process_derivative`,
> `riemann_sum` и `process_integral` — определения,
> *отличные* от тех, что в `ProcessDerivative.v` и
> `RiemannIntegration.v`, хотя имена совпадают.

Стало:

> Файл `ProcessAnalysis.v`
> содержит *свои* определения: `process_derivative`,
> `riemann_sum` и `process_integral`. Имя `riemann_sum`
> совпадает с основным из `RiemannIntegration.v`, а определение
> другое; `process_derivative` и `process_integral` носят имена,
> похожие на основные `deriv_process` (`ProcessDerivative.v`) и
> `integral_process` (`ProcessIntegral.v`), и записаны иначе.

## Расхождение 4. «Интеграл $\int_0^1 1$ равен $1$ на каждом уровне» (стр. 660)

Проверка. В `src/process/ProcessAnalysis.v` доказаны три уровня: `integral_one_K0` (`:122`), `integral_one_K1`
(`:125`), `integral_one_K2` (`:128`) — `process_integral (fun _ => 1) K == 1` при `K = 0, 1, 2`. Леммы для всех `K` в
файле нет (в комментарии на строке 119 она обещана). `Print Assumptions`: `Closed under the global context`.

В чём расхождение: «на каждом уровне» сказано о трёх проверенных уровнях.

**(а) Довести возможно, набросок проверен** (`Check1.v`, без допущений):

```coq
Lemma PA_riemann_sum_one : forall n K,
  ProcessAnalysis.riemann_sum (fun _ => 1) n K == inject_Z (Z.of_nat (S n)).
Proof.
  intros n K. induction n as [| n IH].
  - simpl. reflexivity.
  - change (ProcessAnalysis.riemann_sum (fun _ : Q => 1) (S n) K)
      with (ProcessAnalysis.riemann_sum (fun _ : Q => 1) n K + 1).
    rewrite IH.
    replace (Z.of_nat (S (S n))) with (Z.of_nat (S n) + 1)%Z by lia.
    rewrite inject_Z_plus. reflexivity.
Qed.

Theorem PA_integral_one_all_levels : forall K,
  ProcessAnalysis.process_integral (fun _ => 1) K == 1.
Proof.
  intro K. unfold ProcessAnalysis.process_integral.
  rewrite PA_riemann_sum_one.
  field. intro H. assert (Hp := inject_Z_Sn_pos K). lra.
Qed.
```

(В самом файле `ProcessAnalysis.v` имена пишутся без приставки модуля; `inject_Z_Sn_pos` — из
`ProcessDerivative.v`, в `ProcessAnalysis.v` её нужно повторить или заменить на `unfold Qlt; simpl; lia`.)

**(б)** Стало: «Интеграл $\int_0^1 1$ равен $1$ на уровнях $K=0,1,2$.»

## Расхождение 5. Свёртка телескопа названа «лейбницево-точной» (стр. 484–487)

Проверка. `telescope_collapse` (`src/RiemannIntegration.v:207`):
`tele_sum f a step n == f (walk_point a step n) - f a` — равенство рациональных `==` (`Qeq`).
`Print Assumptions`: `Closed under the global context`. Лейбницево равенство (`=`) для суммы и приращения неверно:
дроби над ℚ не приводятся к несократимому виду. Проверено компилятором (`Check1.v`, `Check5.v`): для $f = \mathrm{id}$,
$a = 0$, шага $1/2$, $n = 2$ сумма вычисляется в `16#16`, приращение — в `4#4`:

```coq
Example telescope_not_leibniz :
  tele_sum (fun x => x) 0 (1#2) 2 <> (fun x => x) (walk_point 0 (1#2) 2) - (fun x : Q => x) 0.
Proof. vm_compute. discriminate. Qed.
```

Лейбницево совпадают узлы: `walk_point a s (S k) = walk_point a s k + s` доказывается `reflexivity`. Именно это
названо в шапке `MeanValueTheorem.v` («Leibniz-exact chaining … for intermediate f-values») и верно изложено в
§ 5.4 (глава «Производная», стр. 741–752).

В чём расхождение: «лейбницево-точным» названо равенство суммы и приращения, а лейбницево-точно только совпадение
соседних узлов; само равенство — `==`.

**(а)** Довести нельзя: утверждение с `=` ложно (пример выше).

**(б)** Было:

> Сумма приращений по узлам равна полному приращению от $a$ до конца
> сетки — и это совпадение *лейбницево-точное*, потому что узлы
> заданы рекурсивной `walk_point` из § 5.4, а не формулой
> $a+ks$ (та же honest-деталь, что разбиралась в главе о производной).

Стало:

> Сумма приращений по узлам равна полному приращению от $a$ до конца
> сетки — без погрешности и без условий на $f$. *Лейбницево-точно*
> здесь совпадение узлов: конец одного шага и начало следующего — один
> и тот же терм, потому что узлы заданы рекурсивной `walk_point` из
> § 5.4, а не формулой $a+ks$ (та же honest-деталь, что разбиралась в
> главе о производной). Поэтому соседние слагаемые сокращаются, и от $f$
> не требуется уважать `Qeq`. Само равенство суммы и приращения в лемме —
> равенство рациональных чисел `==`.

## Расхождение 6. В оценках сумм опущено условие «шаг неотрицателен» (стр. 441–447)

Проверка. `riemann_sum_abs_bound` (`src/RiemannIntegration.v:133`):

```coq
Lemma riemann_sum_abs_bound : forall (f : Q -> Q) (a step : Q) (n : nat) (M : Q),
  (forall k : nat, (k < n)%nat -> Qabs (f (walk_point a step k)) <= M) ->
  0 <= step -> 0 <= M ->
  Qabs (riemann_sum f a step n) <= M * inject_Z (Z.of_nat n) * step.
```

`riemann_sum_global_bound` (`:177`) — с условием `0 <= step`. Обе — `Closed under the global context`. Без условия на
шаг оценки неверны: при `step = -1`, `f = 1`, `n = 1` слева стоит `1`, справа `-1` (`Check1.v`,
`abs_bound_needs_nonneg_step`). У соседних лемм глава условие называет (стр. 397, 411).

В чём расхождение: у двух лемм не названо условие, без которого их утверждения неверны.

**(а)** Снять условие нельзя — без него оценки ложны. Можно дописать леммы уровня процесса, которым соответствуют
формулы стр. 453–457 (сейчас это вывод главы без леммы); набросок проверен (`Check1.v`, без допущений):

```coq
Lemma integral_process_abs_bound : forall f a b n M,
  a < b -> 0 <= M ->
  (forall k, (k < S n)%nat -> Qabs (f (walk_point a (integral_step a b n) k)) <= M) ->
  Qabs (integral_process f a b n) <= M * (b - a).
Proof.
  intros f a b n M Hab HM Hf. unfold integral_process.
  assert (Hstep : 0 <= integral_step a b n).
  { apply Qlt_le_weak. apply integral_step_pos. exact Hab. }
  assert (H := riemann_sum_abs_bound f a (integral_step a b n) (S n) M Hf Hstep HM).
  assert (Hw := grid_width_eq a b n).
  assert (Heq : M * inject_Z (Z.of_nat (S n)) * integral_step a b n == M * (b - a)).
  { rewrite <- Hw. ring. }
  lra.
Qed.

Lemma integral_process_global_bound : forall f a b n lo hi,
  a < b ->
  (forall k, (k < S n)%nat ->
     lo <= f (walk_point a (integral_step a b n) k) /\
     f (walk_point a (integral_step a b n) k) <= hi) ->
  lo * (b - a) <= integral_process f a b n /\ integral_process f a b n <= hi * (b - a).
```

(Доказательство второй — тем же способом; полный текст в `Check1.v`.)

**(б)** Стр. 441–447, стало:

> Лемма
> `riemann_sum_abs_bound`: если $|f|\le M$ в узлах и шаг
> неотрицателен, то
> $|\texttt{riemann\_sum} f a \texttt{step} n|\le M\cdot
> n\cdot\texttt{step}$. Лемма `riemann_sum_global_bound`: при
> $\mathrm{lo}\le f\le \mathrm{hi}$ в узлах и неотрицательном шаге сумма
> из $n$ слагаемых зажата
> между $\mathrm{lo}\cdot n\cdot\texttt{step}$ и $\mathrm{hi}\cdot
> n\cdot\texttt{step}$.

Стр. 464–465, было: «оценки на конечной сумме точны и безусловны». Стало: «оценки на конечной сумме точны и не
требуют сходимости процесса (нужен только неотрицательный шаг; в процессе он положителен при $a<b$)».

## Расхождение 7. `integral_constant`: не назван отрезок (стр. 287–288)

Проверка. `integral_constant` (`src/analysis/StepIntegral.v:59`): `forall c : Q, step_integral (mkStep c 0 1 le_0_1) == c` —
ступень на отрезке $[0,1]$. На общем отрезке значение равно $c\cdot(b-a)$ (по определению `step_integral`;
ср. `integral_from_zero`, `:202`: на $[0,b]$ — `c * b`). `Closed under the global context`.

В чём расхождение: фраза «интеграл константы $c$ на отрезке есть $c$» верна только для отрезка единичной длины.

**(а)** Формализацию менять не нужно.

**(б)** Стало: «интеграл константы $c$ на отрезке $[0,1]$ есть $c$ (`integral_constant`)».

## Расхождение 8. `udiff_product` и `product_decomp` в § 5.6.3 (стр. 607–610)

Проверка. `udiff_product` (`src/IntegralApplications.v:210`) — правило произведения для равномерной
дифференцируемости: при `udiff_on f f' a b`, `udiff_on g g' a b` и ограничениях `|f| <= Mf`, `|g| <= Mg`,
`|f'| <= Mf'`, `|g'| <= Mg'` на $[a,b]$ — `udiff_on (fun x => f x * g x) (fun x => f' x * g x + f x * g' x) a b`.
Интегральная форма — `ftc_product` (`:422`). Лемма `product_decomp` (`:60`) — тождество

`a1 * b1 - a2 * b2 - (c1 * b2 + a2 * c2) * h == (a1 - a2 - c1 * h) * b2 + a2 * (b1 - b2 - c2 * h) + (a1 - a2) * (b1 - b2)`.

В доказательстве `udiff_product` это тождество выведено на месте тактикой `ring` (строки 277–281); сама лемма
`product_decomp` в `src` нигде не применяется (поиск; на строке 269 она названа в комментарии). У правила
произведения производной `deriv_product` (`src/Differentiation.v:284`) разложение другое (строки 355–359):
`(f (x + h) - f x - Lf * h) * g (x + h) + Lf * h * (g (x + h) - g x) + f x * (g (x + h) - g x - Lg * h)`.
Общее у двух доказательств — дробление $\varepsilon$ на три части. Все названные леммы —
`Closed under the global context`.

В чём расхождение: (1) `udiff_product` названа правилом «для интеграла», а это правило для равномерной
дифференцируемости; (2) разложение `product_decomp` названо тем же, что у производной, а тождества разные, и лемма в
доказательстве не вызывается.

**(а)** Малая правка формализации: в доказательстве `udiff_product` заменить вывод тождества на месте вызовом леммы.
Что тождество доказательства есть частный случай леммы, проверено (`Check5.v`):

```coq
Lemma udiff_product_decomposition_is_product_decomp :
  forall (f g f' g' : Q -> Q) (x h : Q),
  f (x + h) * g (x + h) - f x * g x - (f' x * g x + f x * g' x) * h ==
  (f (x + h) - f x - f' x * h) * g x + f x * (g (x + h) - g x - g' x * h) +
  (f (x + h) - f x) * (g (x + h) - g x).
Proof. intros. apply product_decomp. Qed.
```

Слова «то же разложение, что у производной» формализацией не доводятся: у `deriv_product` своё тождество.

**(б)** Было:

> Файл `IntegralApplications.v` содержит правило
> произведения для интеграла (`udiff_product`, с тем же
> $\varepsilon/3$-разложением `product_decomp`, что и правило
> произведения производной в § 5.4), интегрирование по частям

Стало:

> Файл `IntegralApplications.v` содержит правило
> произведения для равномерной дифференцируемости (`udiff_product`:
> приращение произведения раскладывается на три слагаемых — тождество
> `product_decomp`, — и $\varepsilon$ дробится на три части, как в
> правиле произведения производной § 5.4), его интегральную форму
> (`ftc_product`), интегрирование по частям

## Расхождение 9. `antiderivative_unique`: «равные приращения» (стр. 612–615)

Проверка. `antiderivative_unique` (`src/IntegralApplications.v:641`):

```coq
Lemma antiderivative_unique : forall (f g h : Q -> Q) (a b eps : Q),
  udiff_on f h a b -> udiff_on g h a b -> 0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs ((f (walk_point a step (S N)) - f a) - (g (walk_point a step (S N)) - g a)) <= eps * (b - a).
```

`Closed under the global context`. Это $\varepsilon$-форма с выбором уровня: приращения по сетке близки, а не равны.

В чём расхождение: приближённое утверждение пересказано как точное.

**(а) Довести возможно, набросок проверен** (`Check2.v`, без допущений). Для функций, уважающих равенство
рациональных, приращения равны точно:

```coq
Theorem antiderivative_unique_exact : forall (f g h : Q -> Q) (a b : Q),
  Proper (Qeq ==> Qeq) f -> Proper (Qeq ==> Qeq) g ->
  udiff_on f h a b -> udiff_on g h a b ->
  f b - f a == g b - g a.
```

Ход доказательства: по `antiderivative_unique` и `walk_endpoint_qeq` величина
$|(f(b)-f(a)) - (g(b)-g(a))|$ не превосходит $\varepsilon\cdot(b-a)$ при всяком $\varepsilon>0$; число, модуль которого
меньше любого положительного, равно нулю (вспомогательная лемма `Qabs_le_all_eps_zero`). Полный текст — в `Check2.v`.

**(б)** Было:

> единственность первообразной
> (`antiderivative_unique`: две функции с одной производной имеют
> равные приращения — сеточная параллель тому, что нулевая производная
> означает почти-постоянство, § 5.4).

Стало:

> единственность первообразной
> (`antiderivative_unique`: у двух функций с одной производной
> приращения по сетке сколь угодно близки — для всякого $\varepsilon$
> найдётся уровень, на котором они различаются не больше чем на
> $\varepsilon\cdot(b-a)$; сеточная параллель тому, что нулевая
> производная означает почти-постоянство, § 5.4).

## Расхождение 10. Сокращённые имена `abs_bound`, `global_bound` (стр. 699)

Проверка. Объявлений `abs_bound` и `global_bound` в `src` нет (`Locate`: `No object of basename …`). Полные имена —
`riemann_sum_abs_bound` (`src/RiemannIntegration.v:133`) и `riemann_sum_global_bound` (`:177`).

**(а)** Не требуется.

**(б)** Стало: «оценки сумм (`riemann_sum_abs_bound`, `riemann_sum_global_bound`); телескоп (`telescope_collapse`);
сеточный мост grid-FTC (`ftc_grid`);».

## Расхождение 11. «20 Qed» в `StepIntegral.v` (стр. 767–768)

Проверка. Шапка `src/analysis/StepIntegral.v` (строка 5): `STATUS: 20 Qed, 0 Admitted, 0 axioms`. Действительный счёт
(`grep -c 'Qed\.'`) — 17. `Admitted` — 0, аксиом — 0; все 17 лемм — `Closed under the global context`.

В чём расхождение: страница повторяет число из шапки, а оно устарело.

**(а)** Поправить шапку файла: `STATUS: 17 Qed, 0 Admitted, 0 axioms` (правка комментария).

**(б)** Было: «`StepIntegral.v` к тому же короток и заявляет « 20 Qed, 0 Admitted, 0 axioms ».»
Стало: «`StepIntegral.v` к тому же короток: 17 Qed, 0 Admitted, 0 аксиом.»

## Сомнительные места (расхождением не являются)

- **`integral_is_process_construction`** (стр. 120–123, 695). Утверждение верно по определению: свидетель —
  `integral_process`, доказательство — `reflexivity`, посылка `a < b` не используется (`Check1.v`: доказана без
  посылки). Глава говорит о ней честно («не теорема интегрируемости»); в перечне «Построено и проверено» она нового
  содержания не добавляет.
- **Посылка `a < b`.** У `integral_monotone` (`ProcessIntegral.v:207`) она есть и нужна (знак шага); на стр. 398–401
  не названа — подразумевается отрезком. У `integral_process_const` (`:64`) она есть, но в доказательстве не
  используется (`Check1.v`: доказана без неё).
- **$L^1$-норма step-функции** (стр. 428–431). `step_fun_norm f := step_fun_integral (step_fun_abs f)`, где
  `step_fun_abs` берёт модуль значения **каждой ступени**. Тип `StepFun := list Step` не требует, чтобы ступени не
  перекрывались, и функции значения в точке в файле нет. Для списка из ступеней `1` и `-1` на одном отрезке $[0,1]$
  норма равна `2`, а интеграл — `0` (`Check3.v`). Слова «интеграл её модуля» точны для ступеней без перекрытий
  (в шапке файла: «partition»). Возможная оговорка: «норма — сумма $\sum_i |c_i|(b_i-a_i)$; для ступеней без
  перекрытий это интеграл модуля».
- **Мост между двумя линиями** (стр. 310–328). Глава честно говорит, что леммы нет. Она доказуема без аксиом
  (`Check3.v`):

  ```coq
  Fixpoint rs_steps (f : Q -> Q) (a s : Q) (Hs : 0 <= s) (n : nat) : StepFun :=
    match n with
    | O => nil
    | S n' => mkStep (f (walk_point a s n')) (walk_point a s n') (walk_point a s (S n'))
                     (walk_le_next a s n' Hs) :: rs_steps f a s Hs n'
    end.

  Theorem riemann_sum_is_step_integral : forall (f : Q -> Q) (a s : Q) (Hs : 0 <= s) (n : nat),
    step_fun_integral (rs_steps f a s Hs n) == riemann_sum f a s n.
  Proof.
    intros f a s Hs n. induction n as [| n IH].
    - simpl. reflexivity.
    - simpl rs_steps. simpl step_fun_integral. rewrite IH.
      unfold step_integral. simpl. ring.
  Qed.
  ```

  где `walk_le_next : 0 <= s -> walk_point a s k <= walk_point a s (S k)`. С ней фраза «на каждом уровне процесс
  *есть* точный step-интеграл» (стр. 315–316) получает теорему (`integral_process_is_step_integral` там же).
- **Оценки уровня процесса** (стр. 448–457). Формулы $|\texttt{RS}_n(f)|\le M\cdot(b-a)$ и двусторонняя получены в
  главе подстановкой; отдельных лемм в `ProcessIntegral.v` нет. Вывод верен (см. расхождение 6, пункт «а»).
- **«Разность … на процессе»** (стр. 697). Лемм о разности на уровне процесса в `ProcessIntegral.v` нет; есть
  `riemann_sum_sub` на сумме. Вывод однострочный (`Check4.v`, `integral_process_sub`).
- **Оговорка об аксиомах** (стр. 731–758). Осторожная формула («многие могут не зависеть») верна. По компилятору
  она может быть заменена фактом: ни одна из 90 лемм и теорем шести интегральных файлов главы (`RiemannIntegration.v`,
  `ProcessIntegral.v`, `IntegralApplications.v`, `StepIntegral.v`, `ProcessIntegration.v`, `ProcessAnalysis.v`) и
  ни одна из 28 лемм `analysis/FTC.v` (четыре из них названы в главе) от `classic` не зависит. Кроме того, импорт
  `ProcessArithmetic` в `ProcessIntegral.v` (строка 32) не используется: копия файла без этой строки компилируется
  (`ProcessIntegralNoArith.v`). Если импорт убрать, фразу «главный якорь `ProcessIntegral.v` импортирует
  `ProcessArithmetic.v`» (стр. 749–750) придётся переписать.
- **Фраза о `ProcessArithmetic.v`** (стр. 551–553). Теоремы о сохранении свойства Коши под операциями
  (`add_`, `neg_`, `sub_`, `scale_preserves_Cauchy`) — `Closed under the global context`; `classic` стоит только под
  `monotone_bounded_Cauchy` и `decreasing_bounded_Cauchy`. Фраза этого не различает.
- **Примеры `ProcessIntegration.v`** (стр. 641–645). Интеграл нуля и интеграл двойки доказаны только при $K=0$
  (`integral_zero_0`, `integral_two`); уровни для них на странице не названы.
- **`$f_square$`** (стр. 657). Имя `f_square` стоит внутри формулы; подчёркивание в формуле даёт нижний индекс.
  Предложение: «процесс `process_derivative` для `f_square`».
- **`ibp_self` как «частный случай»** (стр. 611–612). По содержанию — случай $g=f$; в доказательстве выведена из
  `ftc_product`, а не из `integration_by_parts`.
- **Аффинная замена** (стр. 623–629). `udiff_chain_affine` и `ftc_u_substitution_affine` требуют `c > 0` и
  `Proper (Qeq ==> Qeq) f`; для `c < 0` есть `udiff_chain_affine_neg` (`analysis/FTC.v:434`), интегральной формы для
  неё нет. Условия на странице не названы.
- **`integral_step_vanishes` и `walk_step_small`** (стр. 558–569). Это одно и то же утверждение о шаге
  $(b-a)/(N+1)$, доказанное дважды разными архимедовыми леммами (`nat_above_Q` и `Archimedean_nat`).
- **Шапка `ProcessIntegral.v`.** «Roles: Cauchy process converging to integral value», «Rules: ftc_grid
  convergence», раздел «Part IV: Convergence via FTC» — в файле сходимость доказана только для константы, а раздел
  содержит лемму о шаге и повтор неотрицательности. Глава цитирует шапку как шапку (стр. 152–153); см. расхождение 1.

## Вне главы (для соседних ведомостей)

- `ftc_comparison` (`RiemannIntegration.v:550`): свидетель в доказательстве — `N = 0` (один узел `a`); посылка
  `udiff_on g g' a b` и `eps` по существу не используются. В главе V.5 лемма только названа в перечне
  `Print Assumptions` (стр. 760–762); содержание — предмет главы V.6. Так же устроена `ftc_constant` (`:347`).
- `ProcessIntegral.v`: `integral_convergence_rate : Q := 1 # 2` и лемма `integral_rate_valid` — число вписано руками
  и ни с одной оценкой не связано; `riemann_sum_nonneg_step` и `integral_process_width` повторяют леммы
  `RiemannIntegration.v`. В главе эти имена не названы.
- Устаревшие числа в шапках и счётчиках, на странице не приведённые: `ProcessIntegral.v` — 11 (действительно 12);
  `ProcessDerivative.v` — 16 (17); `ProcessCore.v` — 25 (19); `analysis_count := 22` в `ProcessAnalysis.v` (18 Qed);
  `integration_count := 5` в `ProcessIntegration.v` (6 Qed).
