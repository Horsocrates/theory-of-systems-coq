# Глава VI.1 «Мера как процесс приписывания» — заметки к ведомости (14.11.2026)

Ведомость: `part06-ch01.json` — 46 ручных записей + 3 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты ручных записей: ok — 38, mismatch-statement — 7, wrong-number — 1.
Расхождений цены и имён без объявления нет.

Семь записей с расхождением формулировки относятся к четырём местам: одна — к расхождению 1 («мера как
sup-процесс»), одна — к расхождению 2 (`measurable_at`), две — к расхождению 3 (мажорированная сходимость),
три — к расхождению 4 (множества меры нуль: рациональные и канторово). Запись с неверным числом — расхождение 5.

Глава называет шесть файлов; все прочитаны целиком:

| файл | строк `Qed.` | шапка говорит | `Admitted` / `Axiom` / `Parameter` |
|---|---|---|---|
| `src/analysis/LebesgueMeasure.v` | 22 | 20 | 0 / 0 / 0 |
| `src/process/ProcessMeasureTheory.v` | 22 | 17 | 0 / 0 / 0 |
| `src/process/ProcessSigmaAdditive.v` | 5 | 5 | 0 / 0 / 0 |
| `src/process/ProcessRationalsNull.v` | 7 | 7 | 0 / 0 / 0 |
| `src/process/ProcessCantorMeasure.v` | 7 | 7 | 0 / 0 / 0 |
| `src/process/ProcessDCT.v` | 7 | 7 | 0 / 0 / 0 |

Седьмой файл глава не называет, но берёт из него имя: `dominated` — `src/process/ProcessFatou.v:41`; восьмой —
`src/process/ProcessArithmetic.v` («процессная арифметика», `monotone_bounded_Cauchy`, `:311`).

`Print Assumptions` снят для всех объявлений шести файлов, для лемм о `dominated` и для
`monotone_bounded_Cauchy` (78 имён): 76 — «Closed under the global context»; два —
`sigma_additive_converges` и `monotone_bounded_Cauchy` — стоят на `Classical_Prop.classic`, и только на ней.
Третьего имени в выводе компилятора нет. Исходники в репозитории и в собранной копии совпадают (`diff`).

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part06/ch01/`:

- `status.txt` — вывод `tom-status.cjs chapter 06/01`;
- `PA.v`, `PA.out` — `Print Assumptions` 78 объявлений;
- `Check.v` — раздел 1 (сходимость процесса меры интервала к $d-c$; пример немонотонности) и раздел 2
  (`measurable_at` не зависит от трёх своих аргументов; набросок содержательного предиката различимости);
- `Check2.v` — раздел 3 (покрытие счётного множества и рациональных чисел), раздел 4 (покрытие канторова
  множества), раздел 5 (конечная сумма: сходимость без мажоранты), раздел 6 (ограниченность частичных сумм для
  примыкающих интервалов).

Оба файла собираются. Новые утверждения разделов 1–5 — «Closed under the global context»;
`adjacent_intervals_sigma` (раздел 6) стоит на `Classical_Prop.classic` (через `sigma_additive_converges`).
В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Отсылки к другим главам по содержанию не сверялись — это предмет их ведомостей. Сверены адреса: Глава 3.3 —
  «Счётность рациональных чисел»; Глава 4.3 — «Точка как класс эквивалентности процессов»; Глава 4.4 —
  «Несчётность процессов»; Глава 6.2 — «Мера Лебега на процессном континууме»; Глава 6.4 — «Теоремы сходимости:
  монотонная и мажорированная»; последняя глава Части V — «Теорема Фубини на процессах». Номера частей
  (II, IV, V, VI) верны.
- Слова сноски 14 «полную формализацию этого перехода для обоих множеств разворачивает следующая глава»
  проверены только по именам: Глава 6.2 называет те же две теоремы (`rationals_cover_to_zero`,
  `cantor_measure_zero`) и те же файлы; других файлов о покрытиях в `src` поиском не найдено. Содержание
  Главы 6.2 — предмет её ведомости.
- Контрпример к мажорированной сходимости для процессного интеграла над ℚ (расхождение 3, пункт «а») изложен
  словами и в Rocq не проверялся: он относится к Главе 6.4.
- Сведения классической математики (неизмеримость $ℚ\cap[c,d]$ по Жордану, стр. 260–265; множества Витали,
  Банах–Тарский; линия Бишопа–Чена) вне предмета аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Мера как sup-процесс … доказаны именно эти процессные утверждения» (стр. 48–50)

**Было:**

> (48–50) *Второй* — процессные *чтения* меры и $\sigma$-аддитивности (мера как sup-процесс, сходимость
> частичных сумм): доказаны именно эти процессные утверждения, при явно названной цене (L3).

**Проверка.** Процесс меры — `src/process/ProcessMeasureTheory.v:39`:

```coq
Definition measure_process (a b c d : Q) : RealProcess :=
  indicator_process a b c d.
```

то есть (`ProcessSimple.v:218`, `ProcessIntegral.v:56`) на стадии `n` — сумма Римана индикатора отрезка
$[c,d]$ по сетке из $n+1$ клеток на $[a,b]$. О нём в файле доказано три утверждения:

```coq
Lemma measure_process_nonneg  : forall a b c d n, a < b -> 0 <= measure_process a b c d n.
Lemma measure_process_bounded : forall a b c d n, a < b -> measure_process a b c d n <= b - a.
Lemma measure_monotone : forall a b c1 d1 c2 d2 n,
  a < b -> c2 <= c1 -> d1 <= d2 ->
  measure_process a b c1 d1 n <= measure_process a b c2 d2 n.
```

Все — «Closed under the global context». Утверждений о точной верхней грани, о росте по `n` и о сходимости
процесса к $d-c$ нет ни в этом файле, ни в остальном `src` (поиск по `measure_process`, `indicator_process`:
ещё `ProcessLebesgue.v`, `ProcessMeasureUnified.v` — там оценки и равенства по определению). Теорема
`measure_is_process` (`:278`) утверждает существование неотрицательного процесса, ограниченного числом $b-a$.

Процесс меры по `n` не монотонен, и его значения бывают больше $d-c$. Для $[c,d]=[1/3,\,2/3]$ в $[0,1]$
(`Check.v`, `measure_process_not_sup`, вычислено `vm_compute`):

| стадия `n` | 1 | 2 | 3 |
|---|---|---|---|
| значение | $1/2$ | $2/3$ | $1/4$ |

при $d-c=1/3$. Точная верхняя грань значений процесса мерой не является; мера — его предел.

Вторая половина фразы верна: сходимость частичных сумм доказана (`sigma_additive_converges`, на `classic`).

**В чём расхождение.** О процессе меры доказаны неотрицательность, ограниченность и монотонность по включению;
утверждения «мера есть верхняя грань (или предел) этого процесса» в формализации нет, а в виде «верхняя грань»
оно для построенного процесса и неверно.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом, новым файлом (например
`src/process/ProcessMeasureLimit.v`); существующие объявления не меняются. Доказывается более сильное, чем
«sup»: процесс меры сходится к $d-c$, и отклонение на стадии `n` не больше шага сетки. Довод: вдоль сетки
сумма $S(k)$ индикатора по первым $k$ узлам удерживает два инварианта — $S(k)\le\max(0,\min(x_k,\,d+h)-c)$ и
$S(k)\ge\min(x_k,\,d)-c-h$; на последнем узле $x_{n+1}=b\ge d$ они дают $|S-(d-c)|\le h$. Набросок проверен
(`Check.v`, раздел 1; три главных утверждения — «Closed under the global context»):

```coq
Lemma ind_cases : forall c d y,
  (c <= y /\ y <= d /\ indicator c d y == 1) \/
  (y < c /\ indicator c d y == 0) \/
  (d < y /\ indicator c d y == 0).
Proof.
  intros c d y.
  destruct (Qlt_le_dec y c) as [Hyc | Hcy].
  - right. left. split; [ exact Hyc | apply indicator_outside_left; exact Hyc ].
  - destruct (Qlt_le_dec d y) as [Hdy | Hyd].
    + right. right. split; [ exact Hdy | apply indicator_outside_right; exact Hdy ].
    + left. split; [ exact Hcy | split; [ exact Hyd | apply indicator_inside; assumption ] ].
Qed.

Lemma ind_sum_nonneg : forall c d a h k,
  0 <= h -> 0 <= riemann_sum (indicator c d) a h k.
Proof.
  intros c d a h k Hh. induction k as [|k IH]; cbn [riemann_sum].
  - apply Qle_refl.
  - assert (H0 := proj1 (indicator_bounded c d (walk_point a h k))).
    assert (Hm : 0 <= indicator c d (walk_point a h k) * h)
      by (apply Qmult_le_0_compat; assumption).
    lra.
Qed.

Lemma ind_sum_upper : forall c d a h k,
  c <= d -> 0 < h ->
  riemann_sum (indicator c d) a h k <= 0 \/
  (riemann_sum (indicator c d) a h k <= walk_point a h k - c /\
   riemann_sum (indicator c d) a h k <= d + h - c).
Proof.
  intros c d a h k Hcd Hh. induction k as [|k IH].
  - left. cbn [riemann_sum]. apply Qle_refl.
  - cbn [riemann_sum walk_point].
    set (y := walk_point a h k) in *.
    set (s := riemann_sum (indicator c d) a h k) in *.
    destruct (ind_cases c d y) as [[H1 [H2 E]] | [[H1 E] | [H1 E]]].
    + assert (Et : indicator c d y * h == h) by (rewrite E; ring).
      right. destruct IH as [IH | [IH1 IH2]]; split; lra.
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      left. destruct IH as [IH | [IH1 IH2]]; lra.
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      destruct IH as [IH | [IH1 IH2]]; [ left; lra | right; split; lra ].
Qed.

Lemma ind_sum_lower : forall c d a h k,
  a <= c -> c <= d -> 0 < h ->
  walk_point a h k - c - h <= riemann_sum (indicator c d) a h k \/
  d - c - h <= riemann_sum (indicator c d) a h k.
Proof.
  intros c d a h k Hac Hcd Hh. induction k as [|k IH].
  - left. cbn [riemann_sum walk_point]. lra.
  - assert (Hnn : 0 <= riemann_sum (indicator c d) a h k)
      by (apply ind_sum_nonneg; lra).
    cbn [riemann_sum walk_point].
    set (y := walk_point a h k) in *.
    set (s := riemann_sum (indicator c d) a h k) in *.
    destruct (ind_cases c d y) as [[H1 [H2 E]] | [[H1 E] | [H1 E]]].
    + assert (Et : indicator c d y * h == h) by (rewrite E; ring).
      destruct IH as [IH | IH]; [ left; lra | right; lra ].
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      left. lra.
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      right. destruct IH as [IH | IH]; lra.
Qed.

(* На стадии n процесс меры отстоит от d - c не дальше шага сетки. *)
Theorem measure_process_rate : forall a b c d n,
  a < b -> a <= c -> c <= d -> d <= b ->
  Qabs (measure_process a b c d n - (d - c)) <= integral_step a b n.
Proof.
  intros a b c d n Hab Hac Hcd Hdb.
  unfold measure_process, indicator_process, riemann_process, integral_process.
  set (h := integral_step a b n).
  assert (Hh : 0 < h) by (unfold h; apply integral_step_pos; exact Hab).
  assert (Hend : walk_point a h (S n) == b).
  { rewrite walk_point_qeq. unfold h.
    assert (G := grid_width_eq a b n). lra. }
  destruct (ind_sum_upper c d a h (S n) Hcd Hh) as [U | [U1 U2]];
  destruct (ind_sum_lower c d a h (S n) Hac Hcd Hh) as [L | L];
  apply Qabs_Qle_condition; split; lra.
Qed.

Theorem measure_process_converges : forall a b c d,
  a < b -> a <= c -> c <= d -> d <= b ->
  measure_process a b c d ~~ const_process (d - c).
Proof.
  intros a b c d Hab Hac Hcd Hdb eps Heps.
  destruct (integral_step_eventually_small a b eps Hab Heps) as [N HN].
  exists N. intros n Hn. unfold const_process.
  eapply Qle_lt_trans; [ apply measure_process_rate; assumption | apply HN; exact Hn ].
Qed.

Corollary measure_process_Cauchy : forall a b c d,
  a < b -> a <= c -> c <= d -> d <= b ->
  is_Cauchy (measure_process a b c d).
Proof.
  intros a b c d Hab Hac Hcd Hdb.
  apply (equiv_cauchy_l (const_process (d - c))).
  - apply process_equiv_sym. apply measure_process_converges; assumption.
  - apply const_is_Cauchy.
Qed.
```

(В пробном файле `measure_process` пишется с именем модуля — `ProcessMeasureTheory.measure_process`; подключения —
`ProcessCore`, `ProcessArithmetic`, `ProcessIntegral`, `ProcessSimple`, `MeanValueTheorem`,
`RiemannIntegration`.) Теорема связывает две линии главы: значение `measure_interval c d H` аналитической линии
($d-c$, `measure_interval_eq`) есть предел процесса `measure_process a b c d` процессной линии. Сходимость здесь
получена с явной оценкой, без `classic`. Слово «sup» на странице после этого лучше заменить: доказан предел, а
не верхняя грань.

**(б) Поправить слова.** Если формализацию не дополнять:

> *Второй* — процессные *чтения* меры и $\sigma$-аддитивности (процесс меры интервала, сходимость частичных
> сумм): о процессе меры доказаны неотрицательность, ограниченность длиной объемлющего отрезка и монотонность по
> включению, о частичных суммах — сходимость, при явно названной цене (L3).

Если дополнить по пункту «а»:

> *Второй* — процессные *чтения* меры и $\sigma$-аддитивности (мера как процесс, сходящийся к длине; сходимость
> частичных сумм): доказаны именно эти процессные утверждения — первое без аксиом, второе при явно названной
> цене (L3).

## Расхождение 2. `measurable_at` назван предикатом различимости (сноска 8, стр. 369)

**Было:**

> (369) В `ProcessMeasureTheory.v`: `measure_process` (процесс индикатора), `q_measure_additive`,
> `q_measure_monotone`, предикат различимости на стадии $n$ `measurable_at`, а также внешние оценки и предикаты
> множества меры нуль.

**Проверка.** `src/process/ProcessMeasureTheory.v:139`:

```coq
Definition measurable_at (a b : Q) (n : nat) (chi : nat -> bool) (x : Q) : Q :=
  if chi n then 1 else 0.
```

Значение — рациональное число $0$ или $1$, а не высказывание; аргументы `a`, `b`, `x` в правой части не
участвуют (`Check.v`, `measurable_at_ignores`: при любых `a b a' b' x x'` значения совпадают по
`reflexivity`). О нём доказана одна лемма — `measurable_at_bounded` (`:143`): значение лежит в $[0,1]$. Вне
файла имя не используется. `Print Assumptions`: Closed under the global context.

Остальное в сноске верно по именам: `measure_process` (`:39`), `q_measure_additive` (`:119`),
`q_measure_monotone` (`:125`), внешние оценки — `outer_approx`, `outer_sum` (`:172`, `:186`), предикат меры
нуль — `is_null_set` (`:211`; он один).

**В чём расхождение.** За словами «предикат различимости на стадии $n$» стоит определение, которое не является
предикатом и не зависит от множества, отрезка и точки.

**(а) Довести формализацию до слов главы.** Возможно, новым файлом, без аксиом: дать содержательный предикат
различимости и доказать его для интервала. Простейший вид — множество зажато между двумя конечными наборами
упорядоченных неперекрывающихся интервалов, и разность суммарных длин не больше $\varepsilon$ (набросок
проверен, `Check.v`, раздел 2; Closed under the global context):

```coq
Definition total_len (l : list (Q * Q)) : Q :=
  fold_right (fun p acc => (snd p - fst p) + acc) 0 l.

Definition in_union (l : list (Q * Q)) (x : Q) : Prop :=
  exists p, In p l /\ fst p <= x /\ x <= snd p.

Fixpoint chain (lo : Q) (l : list (Q * Q)) : Prop :=
  match l with
  | [] => True
  | p :: r => lo <= fst p /\ fst p <= snd p /\ chain (snd p) r
  end.

Definition distinguishable_within (A : Q -> Prop) (a b eps : Q) : Prop :=
  exists inner outer : list (Q * Q),
    chain a inner /\ chain a outer /\
    (forall x, in_union inner x -> A x) /\
    (forall x, a <= x -> x <= b -> A x -> in_union outer x) /\
    total_len outer - total_len inner <= eps.

Definition distinguishable (A : Q -> Prop) (a b : Q) : Prop :=
  forall eps, 0 < eps -> distinguishable_within A a b eps.

Lemma interval_distinguishable : forall a b c d,
  a <= c -> c <= d -> d <= b ->
  distinguishable (fun x => c <= x /\ x <= d) a b.
Proof.
  intros a b c d Hac Hcd Hdb eps Heps.
  exists [(c, d)], [(c, d)]. cbn [chain total_len fold_right fst snd].
  split; [ tauto | split; [ tauto | split; [ | split ] ] ].
  - intros x [p [[Hp | []] Hx]]. subst p. exact Hx.
  - intros x _ _ Hx. exists (c, d). split; [ left; reflexivity | exact Hx ].
  - lra.
Qed.
```

Условие `chain` (каждый следующий интервал начинается не раньше конца предыдущего) нужно, чтобы суммарная длина
внутреннего набора не завышалась повторами. Это предикат уровня объёма Жордана (конечные наборы изнутри и
снаружи); следующим шагом доказывается замкнутость относительно конечного объединения примыкающих интервалов.
Общего предиката «индикатор приближается ступенчатыми функциями» (стр. 127–132) он не заменяет — статус,
названный страницей в сноске 5, остаётся в силе. Определение `measurable_at` в существующем файле при этом не
трогается.

**(б) Поправить слова.**

> В `ProcessMeasureTheory.v`: `measure_process` (процесс индикатора), `q_measure_additive`,
> `q_measure_monotone`, заготовка индикатора на стадии $n$ `measurable_at` (значение $0$ или $1$ по признаку
> стадии; предиката различимости за ней пока нет), а также внешние оценки и предикат множества меры нуль.

## Расхождение 3. «Приём несёт всю теорему о мажорированной сходимости» (стр. 245–249, сноска 13)

**Было:**

> (245–249) Этот приём — не оговорка ради чистоты, а то, что делает теоремы сходимости конструктивными без
> Аксиомы Выбора. В Главе 6.4 он несёт всю теорему о мажорированной сходимости: имея $g$ как параметр, остаётся
> чисто конструктивная оценка $| I(f_n)-I(f) |\le I(|f_n-f|)$ и сжатие невязки — и тогда сходимость интегралов
> следует *без единой аксиомы*.[^13]
>
> (374) Редукция мажорированной сходимости — `process_dct` (`ProcessDCT.v`), 0 аксиом: движок и
> «конверт»-мажоранта доказаны конструктивно, а единственный неконструктивный шаг (сходимость невязок к нулю)
> вынесен в явную гипотезу-вход.

**Проверка.** `src/process/ProcessDCT.v:123`:

```coq
Theorem process_dct : forall (fs : nat -> Q -> Q) (f : Q -> Q)
                             (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  (fun n => riemann_sum (fun x => Qabs (fs n x - f x)) pts w N) ~~ const_process 0 ->
  (fun n => riemann_sum (fs n) pts w N) ~~ const_process (riemann_sum f pts w N).
```

где (`ProcessMCT.v:111`) `riemann_sum f pts w N := w * q_sum (fun i => f (pts i)) N` — сумма по `N`
фиксированным узлам с общим весом `w`. `Print Assumptions process_dct`: Closed under the global context — цена
на странице названа верно.

Три наблюдения.

1. Мажоранты `g` в `process_dct` нет. Она появляется в `process_dct_dominated` (`:148`), и там посылка
   `forall n x, Qabs (fs n x - f x) <= 2 * g x` используется только для первого члена заключения (невязка не
   больше суммы для $2g$); второй член — сходимость — доказывается строкой
   `apply process_dct; [ exact Hw | exact Hres ]`, то есть из посылки о невязках, без мажоранты.
2. «Интеграл» теоремы — конечная сумма при фиксированном `N`; предела по измельчению сетки в утверждении нет.
3. Для такой суммы посылка о невязках не есть неконструктивный шаг: она следует из сходимости в `N` узлах —
   без мажоранты и без аксиом (`Check2.v`, раздел 5, Closed under the global context):

```coq
Theorem finite_sum_dct_no_majorant :
  forall (fs : nat -> Q -> Q) (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  (forall i, (i < N)%nat ->
     (fun n => fs n (pts i)) ~~ const_process (f (pts i))) ->
  (fun n => ProcessMCT.riemann_sum (fs n) pts w N)
    ~~ const_process (ProcessMCT.riemann_sum f pts w N).
```

(доказательство: конечная сумма процессов, сходящихся к нулю, сходится к нулю — леммы `null_plus`,
`q_sum_null`, `scale_null` — и затем `process_dct`).

Слово «редукция» и оговорка о гипотезе-входе в сноске стоят честно; движок (`dct_diff_bound`, `:73`) и конверт
(`dct_dom_bound`, `:99`) доказаны.

**В чём расхождение.** В формализации сходимость сумм выведена из посылки о невязках одним неравенством
треугольника; мажоранта в этом выводе не участвует, а «интеграл» есть конечная сумма по фиксированным узлам, —
слова «приём несёт всю теорему» и «единственный неконструктивный шаг» сильнее и иные, чем доказанное.

**(а) Довести формализацию до слов главы.** В полном виде — нельзя, и причина содержательная.

- На уровне теоремы (конечная сумма) посылку о невязках можно снять (`finite_sum_dct_no_majorant`), но при этом
  мажоранта не нужна вовсе: утверждение перестаёт быть теоремой о мажорированной сходимости.
- На уровне предельного интеграла (процесс `integral_process` по измельчающейся сетке) утверждение «поточечная
  сходимость на ℚ и мажоранта дают сходимость интегралов» неверно. Контрпример (в Rocq не проверялся): $f_m$ —
  индикатор первых $m$ точек перечисления $ℚ\cap[0,1]$, $g=1$. Тогда $|f_m|\le g$, в каждой рациональной точке
  $f_m(x)\to 1$; при каждом $m$ суммы Римана $f_m$ не больше $m\cdot h$ и уходят к нулю при измельчении сетки, а
  суммы для предельной функции $f=1$ равны $1$. Интегралы $f_m$ сходятся к $0$, интеграл предела равен $1$.
- Более слабая содержательная теорема, в которой мажоранта работает (к Главе 6.4): пусть $|f_n|\le g\le M$,
  $|f|\le M$, и для всякого $\delta>0$ найдётся конечный набор интервалов суммарной длины меньше $\delta$, вне
  которого $f_n\to f$ равномерно; тогда процессы интегралов $f_n$ сходятся к процессу интеграла $f$ равномерно
  по стадии сетки. Здесь вклад исключённых интервалов оценивается через $2M\delta$ — это и есть работа
  мажоранты. Набросок не проверялся.

**(б) Поправить слова.**

> (245–249) Этот приём — не оговорка ради чистоты, а то, что делает теоремы сходимости конструктивными без
> Аксиомы Выбора. В Главе 6.4 на нём стоит редукция теоремы о мажорированной сходимости: имея $g$ как параметр,
> доказываются чисто конструктивная оценка $| I(f_n)-I(f) |\le I(|f_n-f|)$ и оценка невязки через $I(2g)$;
> сжатие невязки берётся посылкой — и тогда сходимость интегралов следует *без единой аксиомы*.[^13]
>
> (374) Редукция мажорированной сходимости — `process_dct` (`ProcessDCT.v`), 0 аксиом; интеграл здесь — сумма
> Римана по $N$ фиксированным узлам. Движок и «конверт»-мажоранта доказаны конструктивно, а сходимость невязок
> к нулю вынесена в явную гипотезу-вход; сходимость сумм выводится из неё одним движком, мажоранта даёт
> отдельную оценку невязки (`process_dct_dominated`).

## Расхождение 4. Множества меры нуль: рациональные и канторово (стр. 267–270, сноска 14)

**Было:**

> (267–270) Мера же Лебега, в процессном прочтении, даёт $ℚ\cap[c,d]$ *нуль*. Причина — именно счётность:
> рациональные можно занумеровать (Глава 3.3), а тогда $k$-ю точку можно накрыть интервалом длины, убывающей
> геометрически, так что суммарная длина покрытия есть процесс, сходящийся к нулю.[^14]
>
> (375) Это доказано как процессное утверждение: суммарная длина покрытия на стадии $n$ ведёт себя как
> $(1/2)^n$ и сходится к нулю — `rationals_cover_to_zero` (`ProcessRationalsNull.v`, 0 аксиом). Тот же приём
> даёт меру нуль и для канторова множества — `cantor_measure_zero` (`ProcessCantorMeasure.v`). Полную
> формализацию этого перехода для обоих множеств разворачивает следующая глава.

**Проверка.** `src/process/ProcessRationalsNull.v:46, :90`:

```coq
Fixpoint half_pow (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (1 # 2) * half_pow k
  end.

Theorem rationals_cover_to_zero : half_pow ~~ const_process 0.
```

`src/process/ProcessCantorMeasure.v:43, :88`:

```coq
Fixpoint cantor_cover_measure (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (2 # 3) * cantor_cover_measure k
  end.

Theorem cantor_measure_zero : cantor_cover_measure ~~ const_process 0.
```

Обе теоремы — «Closed under the global context»; цена названа верно. Обе утверждают сходимость к нулю числовой
последовательности: $(1/2)^n$ и $(2/3)^n$. В первом файле нет нумерации рациональных (`Countability_Q` не
подключается), нет интервалов вокруг точек, нет суммы их длин; во втором нет отрезков стадии $n$, их числа и
канторовых точек. Всё это описано в комментариях шапок («the WHOLE countable set Q ∩ [0,1] is covered, at
stage n, by intervals of total length <= (1/2)^n»; «Stage n then consists of 2^n closed intervals, each of
length 3^{-n}»), но объявлениями не построено и не доказано. Остальные утверждения файлов — о тех же
последовательностях (неотрицательность, оценка единицей, вспомогательная оценка $(1/2)^n(n+1)\le 2$ и
$(2/3)^n(n+2)\le 2$, три вычисления).

К словам «тот же приём»: для рациональных приём — нумерация точек и убывающие интервалы вокруг каждой; для
канторова множества — $2^n$ отрезков длины $3^{-n}$ на стадии $n$ (множество несчётно, нумерации нет). Общее у
двух доказательств — геометрическая оценка длины покрытия.

**В чём расхождение.** Доказано, что две геометрические последовательности сходятся к нулю; что эти
последовательности суть длины покрытий рациональных точек и канторова множества, в формализации не построено и
не доказано.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом, новыми файлами (например
`src/process/ProcessCountableNull.v` и `src/process/ProcessCantorCover.v`); существующие теоремы используются
как есть. Наброски проверены (`Check2.v`, разделы 3 и 4; все утверждения — «Closed under the global context»).

*Счётное множество и рациональные числа.* Вокруг $k$-й точки перечисления `e` на стадии $n$ ставится интервал
длины $(1/2)^{k+1}(1/2)^n$; сумма длин первых $K$ интервалов равна $(1/2)^n(1-(1/2)^K)$, то есть меньше
$(1/2)^n$ при любом $K$. Мера нуль читается так: для всякого $\varepsilon>0$ есть последовательность интервалов,
накрывающая каждую точку, у которой любая конечная сумма длин меньше $\varepsilon$ — завершённая сумма ряда не
берётся.

```coq
Lemma half_pow_pos : forall n, 0 < half_pow n.
Proof. induction n as [|n IH]; cbn [half_pow]; lra. Qed.

Definition cov_radius (n k : nat) : Q := half_pow (S (S k)) * half_pow n.
Definition cov_lo (e : nat -> Q) (n k : nat) : Q := e k - cov_radius n k.
Definition cov_hi (e : nat -> Q) (n k : nat) : Q := e k + cov_radius n k.
Definition cov_len (e : nat -> Q) (n k : nat) : Q := cov_hi e n k - cov_lo e n k.

Lemma cov_radius_pos : forall n k, 0 < cov_radius n k.
Proof.
  intros n k. unfold cov_radius.
  apply Qmult_lt_0_compat; apply half_pow_pos.
Qed.

Lemma cov_contains : forall e n k, cov_lo e n k < e k /\ e k < cov_hi e n k.
Proof.
  intros e n k. unfold cov_lo, cov_hi.
  assert (H := cov_radius_pos n k). split; lra.
Qed.

Lemma cov_len_eq : forall e n k, cov_len e n k == half_pow (S k) * half_pow n.
Proof.
  intros e n k. unfold cov_len, cov_hi, cov_lo, cov_radius.
  cbn [half_pow]. ring.
Qed.

Lemma cov_sum : forall e n K,
  q_sum (cov_len e n) K == half_pow n * (1 - half_pow K).
Proof.
  intros e n K. induction K as [|K IH]; cbn [q_sum].
  - cbn [half_pow]. ring.
  - rewrite IH, cov_len_eq. cbn [half_pow]. ring.
Qed.

Lemma cov_sum_lt : forall e n K, q_sum (cov_len e n) K < half_pow n.
Proof.
  intros e n K. rewrite cov_sum.
  assert (Hn := half_pow_pos n). assert (HK := half_pow_pos K).
  assert (Hm : 0 < half_pow n * half_pow K) by (apply Qmult_lt_0_compat; assumption).
  assert (E : half_pow n * (1 - half_pow K) == half_pow n - half_pow n * half_pow K) by ring.
  lra.
Qed.

Theorem countable_set_null : forall (e : nat -> Q) (eps : Q), 0 < eps ->
  exists n : nat,
    (forall k, cov_lo e n k < e k /\ e k < cov_hi e n k) /\
    (forall K, q_sum (cov_len e n) K < eps).
Proof.
  intros e eps Heps.
  destruct (rationals_cover_to_zero eps Heps) as [N HN].
  exists N. split.
  - intro k. apply cov_contains.
  - intro K. apply Qlt_trans with (half_pow N); [ apply cov_sum_lt | ].
    specialize (HN N (Nat.le_refl N)). unfold const_process in HN.
    assert (E : half_pow N - 0 == half_pow N) by ring.
    rewrite E in HN. rewrite Qabs_pos in HN; [ exact HN | apply half_pow_nonneg ].
Qed.

Theorem rationals_null : forall eps : Q, 0 < eps ->
  exists n : nat,
    (forall q : Q, exists k : nat,
        cov_lo enum_Q n k < q /\ q < cov_hi enum_Q n k) /\
    (forall K, q_sum (cov_len enum_Q n) K < eps).
Proof.
  intros eps Heps.
  destruct (countable_set_null enum_Q eps Heps) as [n [Hin Hsum]].
  exists n. split; [ | exact Hsum ].
  intro q. exists (index_of_Q q).
  destruct (Hin (index_of_Q q)) as [H1 H2].
  pose proof (enum_Q_index_id q) as E.
  unfold cov_lo, cov_hi in *. split; lra.
Qed.
```

(`q_sum` — `ProcessMCT.q_sum`; `enum_Q`, `index_of_Q`, `enum_Q_index_id` — `Countability_Q`; в пробном файле они
записаны с именами модулей.) `rationals_null` накрывает все рациональные числа, тем самым и
$ℚ\cap[c,d]$. Существующая теорема `rationals_cover_to_zero` входит в доказательство как оценка длины
покрытия — в том качестве, в каком её описывает страница.

*Канторово множество.* Покрытие стадии $n$ — список левых концов $2^n$ отрезков длины $(1/3)^n$, построенный
самоподобием $C_{n+1}=C_n/3\,\cup\,(C_n/3+2/3)$; канторова точка задаётся последовательностью троичных цифр
$0$ и $2$ (`dg : nat -> bool`), её приближение — первые $m$ цифр.

```coq
Fixpoint third_pow (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (1 # 3) * third_pow k
  end.

Fixpoint cantor_lefts (n : nat) : list Q :=
  match n with
  | O => [0]
  | S k => map (fun a => (1 # 3) * a) (cantor_lefts k)
           ++ map (fun a => (1 # 3) * a + (2 # 3)) (cantor_lefts k)
  end.

Lemma cantor_lefts_length : forall n, length (cantor_lefts n) = Nat.pow 2 n.
Proof.
  induction n as [|n IH]; cbn [cantor_lefts Nat.pow].
  - reflexivity.
  - rewrite length_app, !length_map, IH. lia.
Qed.

(* Суммарная длина покрытия стадии n есть в точности cantor_cover_measure n. *)
Lemma cantor_cover_total : forall n,
  inject_Z (Z.of_nat (length (cantor_lefts n))) * third_pow n
  == cantor_cover_measure n.
Proof.
  induction n as [|n IH]; cbn [cantor_lefts third_pow cantor_cover_measure].
  - cbn. reflexivity.
  - rewrite length_app, !length_map, Nat2Z.inj_add, inject_Z_plus, <- IH. ring.
Qed.

Fixpoint cantor_approx (dg : nat -> bool) (m : nat) : Q :=
  match m with
  | O => 0
  | S k => (if dg O then 2 # 3 else 0)
           + (1 # 3) * cantor_approx (fun i => dg (S i)) k
  end.

Lemma cantor_approx_range : forall m dg,
  0 <= cantor_approx dg m /\ cantor_approx dg m <= 1.
Proof.
  induction m as [|m IH]; intro dg; cbn [cantor_approx].
  - split; lra.
  - destruct (IH (fun i => dg (S i))) as [H1 H2].
    destruct (dg O); split; lra.
Qed.

(* Приближения канторовой точки с номера n лежат в одном отрезке стадии n. *)
Theorem cantor_point_in_cover : forall n dg,
  exists a : Q, In a (cantor_lefts n) /\
    forall m, (n <= m)%nat ->
      a <= cantor_approx dg m /\ cantor_approx dg m <= a + third_pow n.
Proof.
  induction n as [|n IH]; intro dg.
  - exists 0. split; [ left; reflexivity | ].
    intros m _. cbn [third_pow].
    destruct (cantor_approx_range m dg) as [H1 H2]. split; lra.
  - destruct (IH (fun i => dg (S i))) as [a [Ha Hb]].
    cbn [cantor_lefts third_pow].
    destruct (dg O) eqn:E0.
    + exists ((1 # 3) * a + (2 # 3)). split.
      * apply in_or_app. right.
        apply (in_map (fun a => (1 # 3) * a + (2 # 3))). exact Ha.
      * intros m Hm. destruct m as [|m]; [ lia | ].
        cbn [cantor_approx]. rewrite E0.
        destruct (Hb m ltac:(lia)) as [H1 H2]. split; lra.
    + exists ((1 # 3) * a). split.
      * apply in_or_app. left.
        apply (in_map (fun a => (1 # 3) * a)). exact Ha.
      * intros m Hm. destruct m as [|m]; [ lia | ].
        cbn [cantor_approx]. rewrite E0.
        destruct (Hb m ltac:(lia)) as [H1 H2]. split; lra.
Qed.

Theorem cantor_set_null : forall eps : Q, 0 < eps ->
  exists n : nat,
    inject_Z (Z.of_nat (length (cantor_lefts n))) * third_pow n < eps /\
    forall dg, exists a : Q, In a (cantor_lefts n) /\
      forall m, (n <= m)%nat ->
        a <= cantor_approx dg m /\ cantor_approx dg m <= a + third_pow n.
Proof.
  intros eps Heps.
  destruct (cantor_measure_zero eps Heps) as [N HN].
  exists N. split.
  - rewrite cantor_cover_total.
    specialize (HN N (Nat.le_refl N)). unfold const_process in HN.
    assert (E : cantor_cover_measure N - 0 == cantor_cover_measure N) by ring.
    rewrite E in HN. rewrite Qabs_pos in HN; [ exact HN | apply cantor_nonneg ].
  - intro dg. apply cantor_point_in_cover.
Qed.
```

`cantor_cover_total` делает определение `cantor_cover_measure` теоремой о покрытии: сумма длин $2^n$ отрезков
стадии равна $(2/3)^n$. Существующая `cantor_measure_zero` входит в доказательство `cantor_set_null`. Что в
набросок не вошло: попарное непересечение отрезков одной стадии и вложенность стадий как отдельные леммы (для
оценки меры сверху они не нужны).

**(б) Поправить слова.** Текст стр. 267–270 — рассуждение; при неизменной формализации меняется сноска:

> (375) В формализации доказана числовая часть этого рассуждения: оценка суммарной длины покрытия на стадии
> $n$ — процесс $(1/2)^n$ — сходится к нулю, `rationals_cover_to_zero` (`ProcessRationalsNull.v`, 0 аксиом);
> само покрытие (нумерация точек, интервалы, сумма их длин) описано в шапке файла и объявлениями пока не
> построено. Так же для канторова множества: доказано, что длина покрытия стадии $n$, равная $(2/3)^n$, сходится
> к нулю, — `cantor_measure_zero` (`ProcessCantorMeasure.v`); отрезки стадии объявлениями пока не построены. На
> эти оценки опирается следующая глава.

Если дополнить по пункту «а»:

> (375) Это доказано как процессное утверждение: для всякого $\varepsilon$ строится последовательность
> интервалов, накрывающая каждое рациональное число, любая конечная сумма длин которых меньше $\varepsilon$, —
> `rationals_null`; суммарная длина покрытия на стадии $n$ оценивается процессом $(1/2)^n$, сходящимся к нулю
> (`rationals_cover_to_zero`, `ProcessRationalsNull.v`, 0 аксиом). Для канторова множества покрытие стадии $n$ —
> $2^n$ отрезков суммарной длины $(2/3)^n$, и оно содержит приближения всякой канторовой точки, —
> `cantor_set_null`, `cantor_measure_zero` (`ProcessCantorMeasure.v`). Этот переход для обоих множеств
> разворачивает следующая глава.

## Расхождение 5. Число доказанных утверждений в `LebesgueMeasure.v` (сноска 1, стр. 362)

**Было:**

> (362) Опорные файлы — `LebesgueMeasure.v` (каталог `src/analysis/` Rocq-репозитория ToS, 20 доказанных
> утверждений, 0 `Admitted`, 0 аксиом) и `ProcessSigmaAdditive.v` (каталог `src/process/`, 5 утверждений).

**Проверка.** `grep -c 'Qed\.' src/analysis/LebesgueMeasure.v` — 22. Число 20 стоит в шапке файла (`:5`,
«STATUS: 20 Qed»). Из 22 утверждений шесть — вспомогательные неравенства между числами (`le_0_1`, `le_0_half`,
`le_half_1`, `le_0_2`, `le_1_3`, `le_0_0`), одно — сводка четырёх уже доказанных фактов
(`measure_from_integral_works`). «0 `Admitted`» и «0 аксиом» верны; «5 утверждений» для
`ProcessSigmaAdditive.v` верно (четыре леммы и теоремы и один пример).

**В чём расхождение.** На странице число из устаревшей шапки; действительный счёт — 22.

**(а)** Формализации не касается (шапку файла стоит обновить — см. «вне главы»).

**(б) Поправить слова.**

> Опорные файлы — `LebesgueMeasure.v` (каталог `src/analysis/` Rocq-репозитория ToS, 22 доказанных утверждения,
> 0 `Admitted`, 0 аксиом) и `ProcessSigmaAdditive.v` (каталог `src/process/`, 5 утверждений).

## Сомнительные места, не записанные расхождением

1. **Стр. 34–36, 197–207, сноски 9–10: счётная аддитивность.** В `sigma_additive_converges` аргумент
   `mu : nat -> Q` — произвольная последовательность неотрицательных рациональных чисел; множеств $A_k$, их
   непересечения и слов «мера объединения первых $n$ кусков» в утверждении нет, а ограниченность $S_n\le B$ —
   посылка. Страница это оговаривает («в таком прочтении», «при … общей ограниченности частичных сумм»,
   «содержательная роль процесса, а не построенный объект»), поэтому вердикт ok. Довод стр. 199–202 («куски в
   сумме не перекрывают $[c,d]$, и потому $S_n\le d-c$») в файле не формализован. Его можно сделать теоремой для
   примыкающих интервалов $[t_k,t_{k+1}]$: частичная сумма длин равна $t_n-t_0$ (мера объединения первых $n$
   кусков), она не больше $d-t_0$, и процесс — Коши (`Check2.v`, раздел 6, `partial_measure_telescope`,
   `adjacent_intervals_sigma`; первые два члена без аксиом, третий — на `classic`). Для произвольных
   непересекающихся интервалов в $[c,d]$ нужна ещё лемма об упорядочении конечного набора; она не проверялась.
2. **Сноска 9: «`partial_measure_le` даёт монотонность меры по включению».** Утверждение — о номерах частичных
   сумм: `(n <= m)%nat -> partial_measure mu n <= partial_measure mu m`. Пояснение «больше кусков — не меньше
   меры» ему соответствует; слова «по включению» — прочтение. Возможная замена: «даёт монотонность накопления:
   больше кусков — не меньше меры».
3. **Стр. 146–150 и 162–164: неотрицательность и монотонность.** Текст ведёт довод для произвольного $A$
   («индикатор неотрицателен, интеграл неотрицательной ступенчатой функции неотрицателен»; «$\chi_A\le\chi_B$
   поточечно, а интеграл сохраняет порядок»), леммы — для интервалов; уровень оговорён на стр. 149–150 и
   127–132. В `LebesgueMeasure.v` обе леммы доказаны арифметикой длин (переписывание в $d-c$ и `lra`), без
   обращения к поточечному сравнению индикаторов. Довод страницы о монотонности формализован в процессной
   линии: `measure_monotone` из `ProcessMeasureTheory.v:81` (через `indicator_monotone_subset`). Сноска 7
   называет лемму из `LebesgueMeasure.v`; при желании к ней можно добавить вторую.
4. **Стр. 86–94 и сноска 3: «интеграл уже построен в Части V как процесс накопления».** Мера интервала
   `measure_interval` определена через ступенчатый интеграл — конечную сумму «значение × ширина» по списку
   ступеней (определения в `LebesgueMeasure.v:32–48` повторяют `analysis/StepIntegral.v`), а не через процессный
   интеграл Части V. Через процессный интеграл определён `measure_process` процессной линии. Теоремы,
   связывающей две линии, в `src` нет; её даёт пункт «а» расхождения 1.
5. **Сноска 1: «Имена лемм, приводимые в сносках ниже, — из них».** Сноски 8, 12, 13, 14 называют имена из
   `ProcessMeasureTheory.v`, `ProcessFatou.v`, `ProcessDCT.v`, `ProcessRationalsNull.v`,
   `ProcessCantorMeasure.v`; сноски 10–11 — `monotone_bounded_Cauchy` из `ProcessArithmetic.v`.
6. **Сноска 12: `dominated`.** Файл не назван. Формуле страницы отвечает `ProcessFatou.v:41` (с ограничением
   $a\le x\le b$); одноимённое определение `analysis/DominatedConvergence.v:80` берёт постоянную `M`. Предикат
   применяется в двух леммах своего файла; в `ProcessDCT.v` (сноска 13) условие мажорирования записано прямо,
   без него. Возможное уточнение сноски: «предикат `dominated` (`ProcessFatou.v`)».
7. **Стр. 167–169 и сноска 8: «внешние покрытия и предикаты множества меры нуль».** Предикат один —
   `is_null_set` (`:211`), и он о процессе: «`mu n < eps` с некоторого номера», без модуля, так что ему
   удовлетворяет и постоянный отрицательный процесс (`Check.v`, `is_null_set_one_sided`). `outer_approx` и
   `outer_sum` считают длины и накопленную длину последовательности пар чисел; условия «пары накрывают
   множество» в определениях нет. Страница называет всё это инфраструктурой, поэтому вердикт ok; точнее было бы
   «предикат множества меры нуль» в единственном числе.
8. **Сноска 14, последняя фраза: «полную формализацию … разворачивает следующая глава».** Глава 6.2 называет те
   же две теоремы; предмет её ведомости.
9. **Стр. 237–239: «применение P4 в форме „существование $\to$ свидетель“ (L4)».** Аксиомы `L4_witness` в
   выводе компилятора у теорем главы нет: мажоранта стоит аргументом под квантором всеобщности, извлечения
   свидетеля не требуется. Фраза — прочтение, о цене она не говорит.
10. **Сноска 3: «одним тактическим шагом `ring`».** Тактикой `ring` закрывается `characteristic_integral`
    (`:64`) после развёртывания определений; `measure_interval_eq` сводится к ней командой `apply`.

## Вне главы (замечено в исходниках)

- `analysis/LebesgueMeasure.v:5` — шапка «STATUS: 20 Qed»; действительно 22.
- `process/ProcessMeasureTheory.v:6, :16` — шапка «STATUS: 17 Qed»; действительно 22. Заголовок «Measure as
  Supremum Process» и строки шапки «Roles: increasing (more pieces = better)», «Rules: … monotone convergence»
  утверждениями файла не подкреплены: лемм о росте по `n`, о верхней грани и о сходимости в файле нет, а
  процесс `measure_process` по `n` не монотонен (расхождение 1).
- `process/ProcessMeasureTheory.v:278`, `measure_is_process` — под `exists` годится любой неотрицательный
  ограниченный процесс, например постоянный нуль (`Check.v`, `measure_is_process_any_witness`); от `c`, `d` и
  посылки `c <= d` заключение не зависит. То же устройство у `measure_pattern_exists`
  (`ProcessMeasureUnified.v:96`).
- `process/ProcessMeasureTheory.v:139, :150` — `measurable_at` и `measurable_measure` не зависят от части своих
  аргументов (у второго значение — `b - a` или `0` по признаку `chi n`); вне файла не используются.
- `process/ProcessMeasureTheory.v:119` — в `q_measure_additive` посылки `a <= c`, `c <= b` не используются.
- `process/ProcessRationalsNull.v` — заголовок «Q ∩ [0,1] has measure zero» и описание покрытия в шапке
  (`:7–20`) объявлениями не подкреплены; `Countability_Q` не подключён.
- `process/ProcessCantorMeasure.v` — заголовок «The Cantor set has measure zero»; отрезки стадии описаны в
  шапке (`:7–17`), `cantor_cover_measure` определён сразу как $(2/3)^n$.
- `process/ProcessSigmaAdditive.v:38` — «σ-add ⇔ monotone limit»: равносильность в файле не доказывается,
  используется одна сторона (`monotone_bounded_Cauchy`). Комментарий к примеру `:109` («three disjoint sets
  each of measure 2») — о сумме трёх чисел `q_sum (fun _ => 2) 3 = 6`.
- `process/ProcessDCT.v:148`, `process_dct_dominated` — посылка о мажоранте не используется во втором члене
  заключения (расхождение 3).
- `process/ProcessFatou.v:6, :19` — шапка «15 Qed»; действительно 16. Строка шапки «Process: dominated process
  of integrals is Cauchy» (`:17`) теоремой не подкреплена: в файле доказаны оценки, утверждения с `is_Cauchy`
  нет.
