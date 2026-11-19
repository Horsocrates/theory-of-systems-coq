# Глава VIII.5 «Экспонента, линейные уравнения, применения» — заметки к ведомости (18.11.2026)

Ведомость: `part08-ch05.json` — 38 ручных записей + 1 автоматическая (упоминание файла); `merge --dry` проходит
без замечаний, список «без сверки» пуст. Вердикты ручных записей: ok — 34, mismatch-price — 2,
mismatch-statement — 2. Имён без объявления и неверных чисел нет.

Четыре записи с расхождением относятся к трём местам: две — к расхождению 1 (цена ε-сходимости, стр. 35–36 и
171–173), одна — к расхождению 2 (затухание, стр. 66–67), одна — к расхождению 3 («проверка устойчивости» в
динамике цены, стр. 121–124).

Глава называет четыре файла: `src/process/ProcessODEExamples.v` (294 строки, 20 `Qed`),
`src/process/ProcessExpProcess.v` (167, 12), `src/process/ProcessODESystem.v` (110, 8),
`src/stdlib/trading/PriceDynamicsODE.v` (185, 23). Все четыре прочитаны целиком. Для итоговых слов о Части
(стр. 9–13, 141–146, 166–173) прочитаны целиком `ProcessPicardOperator.v` (11 `Qed`) и `ProcessODEStability.v`
(5), а из `ProcessGronwall.v`, `ProcessODE.v`, `ProcessPicard.v`, `FixedPoint.v`, `SeriesConvergence.v` —
определения и названные леммы. Строк `Axiom`, `Parameter`, `Admitted` в четырёх файлах главы нет, библиотека
`Reals` не подключается. `Print Assumptions` снят для всех объявлений двенадцати файлов, на которые опираются
главы Части VIII (`PA.v`: 293 объявления, из них 87 — в четырёх файлах главы): каждое — «Closed under the
global context». Исходники в репозитории и в собранной копии совпадают (`diff` по 14 файлам). Цена на странице
в сносках 1, 4, 7, 8 («0 аксиом») и в итоге Части («без аксиом», стр. 166) названа верно.

Блоков кода в главе нет (инструмент: «БЛОКИ КОДА: объявлений 0»). Пять «прочих фрагментов кода», которые
считает инструмент, — строчные фрагменты в обратных кавычках; сверены все:

| фрагмент | где | сверка |
|---|---|---|
| `exp_euler y0 h n == gronwall_iterate 1 0 h y0 n` | сноска 3 | совпадает с утверждением `exp_euler_is_gronwall` (`ProcessODEExamples.v:89–90`) дословно |
| `price_trajectory p0_ex forces_ex == 203#2` | сноска 11 | совпадает с утверждением `traj_final` (`PriceDynamicsODE.v:79`) дословно |
| `stdlib/trading/` | сноски 1 и 10 (два фрагмента) | каталог `src/stdlib/trading/` есть, файл в нём |
| `Print Assumptions` | сноска 1 | команда стоит в двух новых файлах (`ProcessExpProcess.v:166–167`, `ProcessODESystem.v:109–110`); в двух других её нет, цена проверена в `PA.v` |

Формулы сносок (не в обратных кавычках) тоже сверены: $y_{n+1}=(1+h)y_n$ — `exp_euler_succ`; стадия
$(1+t/(N{+}1))^{N+1}$, значения $1$ и $2$ — `expt_process`, `expt_0_0`, `expt_1_0`; $E_2 = 10201/10000$ и
$1 < E_2$ — `sho_energy2`, `sho_energy_drifts`.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part08/ch05/`:

- `status.txt` — вывод `tom-status.cjs chapter 08/05`; `pa1.txt`, `pa2.txt` — вывод `tom-pa.cjs` для лемм
  Глав 8.3–8.4 и для экспоненты-ряда;
- `PA.v`, `PA.out` — `Print Assumptions` всех объявлений двенадцати файлов; `PA2.v`, `PA2.out` — то же для
  `SeriesConvergence.v` (к расхождению 1);
- `Check.v`, `Check.out` — пробные доказательства, разделы 0–7 по местам главы. Собирается: 75 `Qed`; все 51
  утверждение, для которых снят `Print Assumptions`, — «Closed under the global context»;
- `Stmt.out` — формулировки главных пробных теорем после сборки и несколько вычислений.

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Главы 8.1–8.4 по содержанию не сверялись — это предмет их ведомостей. Проверены только те их утверждения,
  которые повторены в тексте настоящей главы (стр. 9–13, 141–146, 166–173): по исходникам и по
  `Print Assumptions`.
- Свойство Коши для $e^t$-процесса `expt_process t` при общем $t$ и сходимость векторного процесса осциллятора
  при $h \to 0$ не пробовались. Для $e$-процесса доказаны граница $\le 4$ и модуль $4/(N_0+1)$; граница $<3$
  для всех $N$, о которой говорит шапка `ProcessExpProcess.v`, не доказывалась.
- Предложенные добавления проверены как пробный файл поверх собранных модулей (`Check.v`); как файлы `src` с
  записью в `_CoqProject` они не собирались.
- Слова о Части IX (стр. 177–187) — анонс; по файлам Части IX не сверялись. Проверено только, что Часть IX
  тома — «Уравнения в частных производных».
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Что стоит за разделами главы (сводка)

| раздел главы | общие утверждения в `.v` | вычисления на числах | чего в `.v` нет |
|---|---|---|---|
| экспонента как процесс | `euler_yeqy_closed` (рекурсия Эйлера для $y'=y$ даёт $y_0(1+h)^M$), `exp1_is_euler`, `exp1_lower` ($\ge 2$ для всех $N$), `bernoulli_nonneg`, `exp_euler_succ`, `exp_euler_is_gronwall` | стадии `exp1_0`–`exp1_2`; рост и граница $<3$ на трёх стадиях (`exp1_climb`, `exp1_below3`); `expt_0_0`, `expt_1_0` | монотонности и верхней границы для всех $N$; свойства Коши; частичных сумм ряда $\sum x^k/k!$; функционального уравнения; для $e^t$ при общем $t$ — чего-либо, кроме определения и двух значений |
| линейные уравнения | `linear_euler_step` (один шаг, любое $L$), `linear_rhs_lipschitz` ($L>0$), `decay_rhs_lipschitz` ($\alpha>0$), `decay_solution_bounded`, `decay_converges`, `cluster_linear_euler_gronwall` | — | траектории Эйлера за $n$ шагов (`linear_euler_is_gronwall` имеет вид `x = x`); роста при $L>0$; систем линейных уравнений |
| системы и осциллятор | `sys_euler_0`, `sys_euler_fst_S`, `sys_euler_snd_S`, `order2_position_step` — развёртывания определения | `sho_y2`, `sho_v2`, `sho_energy2`, `sho_energy_drifts` ($h=1/10$, два шага) | липшицевости, сжатия, оценки расхождения для пар; закона энергии; второго разностного уравнения |
| динамика цены | `price_step_additive`, `traj_nil`, `traj_single`, `history_length`, `history_head`, `mr_force_at_target` | `traj_step1`–`traj_step4`, `traj_final`; семь примеров порогов; пять примеров возврата к среднему | теоремы об устойчивости какой-либо траектории |

Экспонента как ряд с теоремой сложения в репозитории есть, но в других файлах, которых глава не называет:
`exp_limit` (`src/PowerSeries.v:419`), `exp_add` (`src/ExpFunctionalEquation.v:272`); оба берут
`Classical_Prop.classic`. Связи между `exp1_process` и `exp_limit 1` в формализации нет (имя `exp1_process`
встречается только в `ProcessExpProcess.v`).

## Расхождение 1. ε-сходимость отнесена к слою L3, а по компилятору аксиом не берёт (стр. 35–36, 171–173)

**Было:**

> (35–36) Эти объекты — роль-пределы, и $\varepsilon$-сходимость к ним наследует L3 (как в Главах 8.3–8.4).
>
> (171–173) *Граница* (L3 / роль-предел): $\varepsilon$-сходимость итераций и множителей к завершённому пределу;
> завершённые функции-решения, $e^t$, $\sin$, $\cos$ как объекты; глобальное во времени продолжение, blow-up,
> максимальный интервал.

**Проверка.** Главы 8.3–8.4, на которые ссылается стр. 36, относят к L3 леммы `iterate_is_cauchy` и
`Qpow_vanish` (Глава 8.3, сноска 3: «наследующие `classic`»). Вывод `tom-pa.cjs` (`pa1.txt`, `pa2.txt`):

```
Qpow_vanish — Lemma, src/SeriesConvergence.v:164
  forall (r : Q) (eps : Q), 0 < r -> r < 1 -> 0 < eps -> exists N : nat, Qpow r N < eps.
  допущения:   Closed under the global context
Qpow_limit_zero — Lemma, src/SeriesConvergence.v:261
  forall r, 0 <= r -> r < 1 -> forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qpow r n < eps.
  допущения:   Closed under the global context
iterate_is_cauchy — Lemma, src/FixedPoint.v:263
  forall f a b c x, is_contraction f a b c -> a <= x -> x <= b -> is_cauchy (fun n => iterate f x n).
  допущения:   Closed under the global context
euler_picard_cauchy — Theorem, src/process/ProcessPicard.v:206
  forall g y0 h L M, 0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M -> L * h < 1 ->
  is_cauchy (euler_picard_process g y0 h).
  допущения:   Closed under the global context
decay_converges — Lemma, src/process/ProcessODEExamples.v:139
  forall alpha h y0, 0 < alpha -> 0 < h -> alpha * h < 1 -> 0 < y0 ->
  forall eps, 0 < eps -> exists N, y0 * Qpow (1 - alpha * h) N < eps.
  допущения:   Closed under the global context
```

`decay_converges` стоит в опорном файле самой главы: это ε-сходимость множителей $y_0(1-\alpha h)^N$ к нулю.
Строка шапки `FixedPoint.v` («AXIOMS: classic (inherited from MonotoneConvergence via Qpow_vanish)», стр. 12)
устарела: ни одно из 23 объявлений этого файла `classic` не берёт (`PA.v`). В `SeriesConvergence.v` `classic`
берут пять объявлений из 26 проверенных — `Qpow_cauchy`, `partial_sum_nonneg_bound`, `geometric_series_cauchy`,
`comparison_test`, `geometric_limit` (`PA2.v`); `Qpow_vanish` и `Qpow_limit_zero` к ним не относятся, и
перечисленные выше леммы на эти пять не опираются. Во всех двенадцати файлах, на которые опираются главы
Части VIII, ни одно из 293 объявлений `classic` не берёт (`PA.v`).

О сходимости самих объектов стр. 33–36 в файлах главы утверждений нет: для $e$-процесса доказаны три стадии,
тождество с траекторией Эйлера и нижняя граница $2$; монотонность и граница $<3$ проверены на трёх стадиях;
`sin` и `cos` не объявлены. Шапка `ProcessExpProcess.v` (стр. 21–25) относит свойство Коши к недоказанному и
называет его «classic-based». Пробный файл (`Check.v`, раздел 1) показывает, что оно доказывается без аксиом:

```
exp1_is_Cauchy : is_Cauchy exp1_process                      (* ProcessCore.is_Cauchy *)
exp1_modulus   : forall N0 m n : nat, (N0 <= m)%nat -> (N0 <= n)%nat ->
                 Qabs (exp1_process m - exp1_process n) <= 4 / Qn (S N0)
Print Assumptions: Closed under the global context
```

Для итераций Пикара на сетке «завершённый предел» есть рациональная грид-функция — ломаная Эйлера, и итераты
достигают её точно за $N$ шагов (`Check.v`, раздел 7, `picard_iter_reaches_euler`; Closed under the global
context).

**В чём расхождение.** Страница относит ε-сходимость итераций и множителей к слою L3; по компилятору
соответствующие утверждения доказаны без аксиом, а для $e$, $\sin$ и $\cos$ утверждение о сходимости в
названных файлах не записано вовсе — слова «наследует L3» сказаны о незаписанном.

**(а) Довести формализацию до слов главы.** По цене доводить нечего: формализация сильнее слов страницы.
Содержательно недостаёт самого утверждения о сходимости $e$-процесса; оно доводится без аксиом. Предлагается
новый файл, например `src/process/ProcessExpCauchy.v` (существующие файлы не трогаются). Набросок проверен:
`Check.v`, раздел 1 (стр. 85–345 файла), все утверждения — Closed under the global context. Ход: неравенство
Бернулли при $x \ge -1$; нижний процесс $(1+1/n)^n$ не убывает, верхний $(1+1/n)^{n+1}$ не возрастает; их
разность равна $(1+1/n)^n/n \le 4/n$.

```coq
Definition Qn (n : nat) : Q := inject_Z (Z.of_nat n).

(** Неравенство Бернулли при x >= -1 (в ProcessExpProcess.v — только при x >= 0). *)
Lemma bernoulli_ge_m1 : forall (x : Q) (n : nat),
  -1 <= x -> 1 + Qn n * x <= qpow (1 + x) n.

(** Стадии e-процесса не убывают: множитель (1 - 1/(d+1)^2)^(n+2) >= d/(d+1) по Бернулли. *)
Lemma exp1_mono_step : forall N, exp1_process N <= exp1_process (S N).
Lemma exp1_mono : forall n m, (n <= m)%nat -> exp1_process n <= exp1_process m.

(** Верхний процесс (1+1/n)^(n+1) не возрастает: (1 + 1/(d(d+2)))^(n+3) >= 1 + 1/d по Бернулли. *)
Definition exp1_upper (N : nat) : Q := qpow (1 + 1 / Qn (S N)) (S (S N)).
Lemma exp1_upper_0 : exp1_upper 0 == 4.
Lemma exp1_upper_anti_step : forall N, exp1_upper (S N) <= exp1_upper N.
Lemma exp1_upper_anti : forall n m, (n <= m)%nat -> exp1_upper m <= exp1_upper n.

Lemma exp1_upper_gap : forall N,
  exp1_upper N - exp1_process N == exp1_process N / Qn (S N).
Lemma exp1_le_upper : forall N, exp1_process N <= exp1_upper N.

Theorem exp1_le_4 : forall N, exp1_process N <= 4.
Proof.
  intro N.
  eapply Qle_trans; [ apply exp1_le_upper | ].
  eapply Qle_trans; [ apply (exp1_upper_anti 0 N); lia | ].
  rewrite exp1_upper_0. apply Qle_refl.
Qed.

Theorem exp1_modulus : forall N0 m n, (N0 <= m)%nat -> (N0 <= n)%nat ->
  Qabs (exp1_process m - exp1_process n) <= 4 / Qn (S N0).
Proof.
  intros N0 m n Hm Hn.
  pose proof (exp1_mono N0 m Hm) as Lm.
  pose proof (exp1_mono N0 n Hn) as Ln.
  pose proof (Qle_trans _ _ _ (exp1_le_upper m) (exp1_upper_anti N0 m Hm)) as Um.
  pose proof (Qle_trans _ _ _ (exp1_le_upper n) (exp1_upper_anti N0 n Hn)) as Un.
  pose proof (exp1_upper_gap N0) as Hg.
  pose proof (Qn_pos N0) as Hd.
  assert (Hq : exp1_process N0 / Qn (S N0) <= 4 / Qn (S N0)).
  { unfold Qdiv. apply Qmult_le_compat_r; [ apply exp1_le_4 | ].
    apply Qlt_le_weak, Qinv_lt_0_compat. exact Hd. }
  set (g := exp1_process N0 / Qn (S N0)) in *.
  set (b := 4 / Qn (S N0)) in *.
  apply Qabs_Qle_condition. split; lra.
Qed.

Theorem exp1_is_Cauchy : is_Cauchy exp1_process.
Proof.
  intros eps Heps.
  destruct (nat_archimedean 4 eps Heps) as [K HK].
  exists K. intros m n Hm Hn.
  eapply Qle_lt_trans; [ apply (exp1_modulus K m n Hm Hn) | ].
  apply Qlt_shift_div_r; [ apply Qn_pos | ].
  pose proof (Qn_S K) as HS. fold (Qn K) in HK.
  assert (Hle : Qn K * eps <= Qn (S K) * eps).
  { apply Qmult_le_compat_r; [ rewrite HS; lra | lra ]. }
  rewrite (Qmult_comm eps (Qn (S K))). lra.
Qed.
```

Полные доказательства двух шагов монотонности (`exp1_mono_step`, `exp1_upper_anti_step`) и вспомогательных
лемм — в `Check.v`, стр. 89–275. `nat_archimedean` — `src/MonotoneConvergence.v:74`. Для $e^t$ при общем $t$ в
том же разделе доказаны `expt_is_euler` (стадия есть траектория Эйлера с шагом $t/(N+1)$), `expt_lower`
($1+t \le$ стадии при $t \ge 0$) и `expt_zero`; свойство Коши при общем $t$ не доказывалось. Для $\sin$ и
$\cos$ утверждение о сходимости не доводилось: они остаются роль-пределами без записанной оценки.

**(б) Поправить слова.**

Стр. 35–36, если формализация не дополняется:

> Эти объекты — роль-пределы: завершённым объектом ни один из них здесь не предъявлен, а утверждение о
> сходимости к ним в опорных файлах главы не записано. Сами $\varepsilon$-оценки L3 не требуют: Коши-свойство
> итераций и затухание множителей (Главы 8.3–8.4) доказаны без аксиом.

Стр. 35–36, если добавлен файл из пункта (а):

> Эти объекты — роль-пределы: завершённым объектом ни один из них здесь не предъявлен. $\varepsilon$-оценки L3
> не требуют: $e$-процесс есть процесс Коши с явным модулем $4/(N+1)$, а Коши-свойство итераций и затухание
> множителей (Главы 8.3–8.4) доказаны без аксиом; для $e^t$ при общем $t$, $\sin$ и $\cos$ утверждение о
> сходимости не записано.

Стр. 171–173:

> *Граница* (роль-предел): завершённые функции-решения, $e^t$, $\sin$, $\cos$ как объекты; глобальное во времени
> продолжение, blow-up, максимальный интервал. $\varepsilon$-оценки — Коши-свойство итераций и затухание
> множителей — к границе не относятся: они доказаны без аксиом.

Следующая фраза страницы («Эта граница — не пробел, а честная демаркация…») остаётся без изменений. Слова
стр. 145–146 («L3 входит лишь там, где роль-предел читается как завершённый объект») с компилятором согласуются
и правки не требуют. Формулировку стоит согласовать с тем, как будут поправлены Главы 8.3–8.4: там стоит та же
отсылка к L3.

## Расхождение 2. Затухание: в теореме стоит условие $u_0 \ge 0$, на странице его нет (стр. 66–67)

**Было:**

> Здесь множитель шага есть $1 - \alpha h$, и при $0 \le 1 - \alpha h \le 1$ процесс не растёт, а убывает — ровно
> случай затухающего Гронуолла из Главы 8.4: $u_n \le u_0$.

**Проверка.** `src/process/ProcessGronwall.v:112` и `src/process/ProcessODEExamples.v:131`:

```coq
Lemma gronwall_decay_factor : forall r u0 n,
  0 <= r -> r <= 1 ->
  0 <= u0 ->
  u0 * Qpow r n <= u0.

Lemma decay_solution_bounded : forall alpha h y0 n,
  0 < alpha -> 0 < h -> alpha * h < 1 -> 0 <= y0 ->
  gronwall_iterate (- alpha) 0 h y0 n <= y0.
```

`Print Assumptions` обеих: Closed under the global context. Посылка `0 <= u0` нужна: при $u_0=-1$, $r=1/2$,
$n=1$ имеем $u_1=-1/2>u_0$ (`Check.v`, раздел 3, `decay_bound_needs_nonneg`). Кроме того, обе леммы дают
сравнение с начальным значением ($u_n \le u_0$), а не убывание от шага к шагу. Вторая лемма говорит об итерации
Гронуолла `gronwall_iterate (- alpha) 0 h y0 n`; что метод Эйлера с правой частью `decay_rhs alpha` даёт
$y_0(1-\alpha h)^n$, в файле не записано.

**В чём расхождение.** На странице оценка $u_n \le u_0$ дана при одном условии на множитель; в теореме есть
ещё условие неотрицательности начального значения, без которого оценка неверна.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. Оценка по модулю верна при любом знаке
начального значения и при любом множителе с $\lvert r\rvert \le 1$; при $u_0 \ge 0$, $0 \le r \le 1$ верно и
убывание от шага к шагу. Набросок проверен: `Check.v`, разделы 2 и 3, Closed under the global context.

```coq
Lemma Qabs_Qpow_le_1 : forall r n, Qabs r <= 1 -> Qabs (Qpow r n) <= 1.
Proof.
  intros r n Hr. induction n as [|k IH].
  - cbn [Qpow]. rewrite Qabs_pos; [ apply Qle_refl | unfold Qle; simpl; lia ].
  - cbn [Qpow]. rewrite Qabs_Qmult.
    pose proof (Qabs_nonneg (Qpow r k)) as H1.
    apply Qle_trans with (1 * Qabs (Qpow r k)).
    + apply Qmult_le_compat_r; assumption.
    + lra.
Qed.

Lemma decay_abs_bound : forall r u0 n,
  Qabs r <= 1 -> Qabs (u0 * Qpow r n) <= Qabs u0.
Proof.
  intros r u0 n Hr. rewrite Qabs_Qmult.
  pose proof (Qabs_Qpow_le_1 r n Hr) as Hp.
  pose proof (Qabs_nonneg u0) as Hu.
  apply Qle_trans with (Qabs u0 * 1); [ | lra ].
  rewrite (Qmult_comm (Qabs u0) (Qabs (Qpow r n))), (Qmult_comm (Qabs u0) 1).
  apply Qmult_le_compat_r; assumption.
Qed.

Lemma decay_monotone : forall r u0 n, 0 <= r -> r <= 1 -> 0 <= u0 ->
  u0 * Qpow r (S n) <= u0 * Qpow r n.
Proof.
  intros r u0 n Hr0 Hr1 Hu.
  assert (Hp : 0 <= u0 * Qpow r n).
  { apply Qmult_le_0_compat; [ exact Hu | apply Qpow_nonneg; exact Hr0 ]. }
  cbn [Qpow].
  setoid_replace (u0 * (r * Qpow r n)) with (r * (u0 * Qpow r n)) by ring.
  apply Qle_trans with (1 * (u0 * Qpow r n)); [ | lra ].
  apply Qmult_le_compat_r; assumption.
Qed.

(** Метод Эйлера с правой частью decay_rhs даёт именно этот процесс множителей. *)
Lemma decay_euler_closed : forall alpha t0 y0 h n,
  euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n
  == y0 * Qpow (1 - alpha * h) n.
Proof.
  intros alpha t0 y0 h n. induction n as [|k IH].
  - simpl. ring.
  - rewrite euler_method_succ. unfold euler_step, decay_rhs.
    rewrite IH. cbn [Qpow]. ring.
Qed.
```

**(б) Поправить слова.** Если формализация не дополняется:

> Здесь множитель шага есть $1 - \alpha h$, и при $0 \le 1 - \alpha h \le 1$ и $u_0 \ge 0$ процесс не превосходит
> начального значения — ровно случай затухающего Гронуолла из Главы 8.4: $u_n \le u_0$.

Если добавлены леммы из пункта (а):

> Здесь множитель шага есть $1 - \alpha h$, и при $0 \le 1 - \alpha h \le 1$ процесс по модулю не растёт, а
> убывает — ровно случай затухающего Гронуолла из Главы 8.4: $\lvert u_n\rvert \le \lvert u_0\rvert$ (при
> $u_0 \ge 0$ — $u_{n+1} \le u_n \le u_0$).

## Расхождение 3. «Проверка устойчивости» — сравнение числа с порогом; с траекторией цены она не связана (стр. 121–124; вывод курсивом на стр. 126–129)

**Было:**

> Файл вводит и проверку устойчивости через липшицев коэффициент — аналогичное липшицево условие (коэффициент
> сжатия меньше единицы), родственное условию $LT<1$ сжатия Пикара (Глава 8.3), прочитанное как признак
> устойчивой динамики.

**Проверка.** `src/stdlib/trading/PriceDynamicsODE.v:35–51`:

```coq
Definition lipschitz_ratio (x1 y1 x2 y2 : Q) : Q :=
  Qabs (y2 - y1) / Qabs (x2 - x1).

Definition lipschitz_check (L : Q) : bool :=
  Qle_bool L 1.

Definition stability_signal (L : Q) : Z :=
  match Qlt_le_dec L (1#2) with
  | left _ => 1%Z      (* strongly stable *)
  | right _ =>
    match Qlt_le_dec L 1 with
    | left _ => 0%Z     (* marginally stable *)
    | right _ => (-1)%Z (* unstable *)
    end
  end.
```

1. `lipschitz_check` есть условие «не больше единицы», а не «меньше единицы»: `lipschitz_check L = true <-> L <= 1`
   (`Check.v`, раздел 5, `lipschitz_check_spec`), в частности `lipschitz_check 1 = true`. Второе определение
   даёт на том же числе противоположный ответ: `stability_signal 1 = (-1)%Z` (`Stmt.out`).
2. Все три определения — функции числа. О них в файле семь лемм, и все — вычисления на числах
   (`lipschitz_small`, `lipschitz_large`, `check_small_lip`, `check_large_lip`, `signal_strong`,
   `signal_marginal`, `signal_unstable`). Ни одна теорема файла не связывает их с `price_trajectory`, с
   `mr_trajectory` или с иной траекторией. Строка шапки «Rules: Lipschitz < 1 implies stable dynamics» теоремой
   не подкреплена.
3. При совпадающих абсциссах `lipschitz_ratio` равно нулю (деление на нуль в `Q` даёт нуль), и сигнал —
   «сильно устойчиво»: `lipschitz_ratio x y1 x y2 == 0`, `stability_signal (lipschitz_ratio 1 0 1 100) = 1%Z`
   (`Check.v`, `lipschitz_ratio_degenerate`, `stability_signal_degenerate`).
4. У динамики примера главы $p_{n+1}=p_n+f_n$ воздействие от цены не зависит, и коэффициент шага по начальной
   цене равен единице: две траектории под одними воздействиями сохраняют расстояние
   (`Check.v`, `price_traj_shift`: `price_trajectory p forces - price_trajectory q forces == p - q`). Сжатия у
   неё нет.

**В чём расхождение.** Страница называет условие «коэффициент сжатия меньше единицы» и говорит о проверке
устойчивости; в файле стоит сравнение числа с порогом (в `lipschitz_check` — нестрогое), и ни с какой
траекторией оно теоремой не связано.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. В том же файле есть динамика, у которой
липшицев коэффициент шага действительно управляет устойчивостью, — возврат к среднему `mr_trajectory`
(`:170`); о самой траектории в файле три вычисления (`mr_traj_0`–`mr_traj_2`) и ни одной общей теоремы.
Предлагается новый файл, например
`src/stdlib/trading/PriceDynamicsStability.v`. Набросок проверен: `Check.v`, раздел 5, Closed under the global
context.

```coq
(** Две траектории под одними воздействиями сохраняют расстояние (коэффициент 1). *)
Lemma price_trajectory_sum : forall forces p,
  price_trajectory p forces == p + fold_right Qplus 0 forces.
Proof.
  induction forces as [|f rest IH]; intro p.
  - simpl. ring.
  - simpl. rewrite IH. unfold price_step. ring.
Qed.

Lemma price_traj_shift : forall forces p q,
  price_trajectory p forces - price_trajectory q forces == p - q.
Proof. intros forces p q. rewrite !price_trajectory_sum. ring. Qed.

(** Возврат к среднему: отклонение от цели умножается на 1 - alpha на каждом шаге. *)
Lemma mr_step : forall p0 target alpha n,
  mr_trajectory p0 target alpha (S n) - target
  == (1 - alpha) * (mr_trajectory p0 target alpha n - target).
Proof.
  intros. cbn [mr_trajectory]. cbv zeta. unfold mean_reverting_force. ring.
Qed.

Theorem mr_deviation : forall p0 target alpha n,
  mr_trajectory p0 target alpha n - target
  == (p0 - target) * Qpow (1 - alpha) n.
Proof.
  intros p0 target alpha n. induction n as [|k IH].
  - cbn [mr_trajectory Qpow]. ring.
  - rewrite mr_step, IH. cbn [Qpow]. ring.
Qed.

(** Шаг возврата к среднему — липшицево отображение с коэффициентом |1 - alpha|. *)
Lemma mr_step_lipschitz : forall p q target alpha,
  Qabs ((p + mean_reverting_force p target alpha)
        - (q + mean_reverting_force q target alpha))
  == Qabs (1 - alpha) * Qabs (p - q).
Proof.
  intros. unfold mean_reverting_force. rewrite <- Qabs_Qmult.
  apply Qabs_wd. ring.
Qed.

(** При |1 - alpha| <= 1 отклонение не растёт (decay_abs_bound — из расхождения 2). *)
Theorem mr_stable : forall p0 target alpha n,
  Qabs (1 - alpha) <= 1 ->
  Qabs (mr_trajectory p0 target alpha n - target) <= Qabs (p0 - target).
Proof.
  intros p0 target alpha n Ha. rewrite mr_deviation.
  apply decay_abs_bound. exact Ha.
Qed.

(** При 0 < alpha < 1 траектория сходится к цели. *)
Theorem mr_converges : forall p0 target alpha,
  0 < alpha -> alpha < 1 ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (mr_trajectory p0 target alpha n - target) < eps.
Proof.
  intros p0 target alpha Ha0 Ha1 eps Heps.
  set (C := Qabs (p0 - target) + 1).
  assert (HC : 0 < C) by (unfold C; pose proof (Qabs_nonneg (p0 - target)); lra).
  assert (Hec : 0 < eps / C).
  { apply Qlt_shift_div_l; [ exact HC | lra ]. }
  destruct (Qpow_limit_zero (1 - alpha) ltac:(lra) ltac:(lra) (eps / C) Hec) as [N HN].
  exists N. intros n Hn.
  rewrite mr_deviation, Qabs_Qmult.
  assert (Hp0 : 0 <= Qpow (1 - alpha) n) by (apply Qpow_nonneg; lra).
  rewrite (Qabs_pos (Qpow (1 - alpha) n) Hp0).
  pose proof (HN n Hn) as Hlt.
  assert (H1 : Qabs (p0 - target) * Qpow (1 - alpha) n <= C * Qpow (1 - alpha) n).
  { apply Qmult_le_compat_r; [ unfold C; lra | exact Hp0 ]. }
  assert (H2 : C * Qpow (1 - alpha) n < C * (eps / C)).
  { apply Qmult_lt_l; assumption. }
  assert (H3 : C * (eps / C) == eps) by (field; lra).
  lra.
Qed.
```

Определение `lipschitz_check` в существующем файле лучше не менять; если нужна строгая проверка, её можно
добавить в новом файле отдельным определением.

**(б) Поправить слова.** Если формализация не дополняется:

> Файл вводит и пороговую проверку липшицева коэффициента (`lipschitz_check` — коэффициент не больше единицы;
> `stability_signal` — пороги $1/2$ и $1$) — условие того же рода, что $LT<1$ сжатия Пикара (Глава 8.3),
> прочитанное как признак устойчивой динамики; с траекторией цены эта проверка в файле теоремой не связана.

Если добавлен файл из пункта (а), к этому предложению добавляется:

> Для динамики возврата к среднему связь доказана: отклонение от цели на каждом шаге умножается на
> $1-\alpha$, и при $0<\alpha<1$ оно становится меньше любого $\varepsilon$.

Вывод курсивом на стр. 126–129 («Устойчивость управляется липшицевым условием того же типа, что и сходимость
Пикара…») — слово автора; после доводки (а) у него появляется опора в формализации, без неё опоры нет.

## Сомнительные места (расхождением не являются)

1. **Сноска 2: `exp_euler` задан замкнутой формулой.** `exp_euler y0 h n := y0 * Qpow (1 + h) n`
   (`ProcessODEExamples.v:76`) не ссылается ни на `exp_rhs`, ни на метод Эйлера; `exp_euler_succ` есть свойство
   этой формулы. Слова стр. 41–42 («за $n$ шагов получается $(1+h)^n$») при этом доказаны — в другом файле:
   `euler_yeqy_closed` (`ProcessExpProcess.v:71`). Между двумя файлами связки нет: степени разные (`Qpow` и
   локальная `qpow`), `exp1_process` и `exp_euler` не сопоставлены, с общим `euler_method` (`ProcessODE.v:48`)
   ни тот, ни другой не связан. Связки доказаны в `Check.v`, раздел 0: `qpow_is_Qpow`,
   `exp_euler_is_euler_method`, `euler_yeqy_is_exp_euler`, `exp1_is_exp_euler`.
2. **Стр. 50–51: «Для произвольного времени аналогично».** О `expt_process` в файле есть определение и два
   значения (сноска 5 так и говорит). Тождество с траекторией Эйлера и нижняя граница, доказанные для $t=1$,
   для общего $t$ не записаны; они верны (`Check.v`, `expt_is_euler`, `expt_lower` при $t \ge 0$,
   `expt_zero`).
3. **Стр. 60–62: линейное уравнение.** Доказан один шаг (`linear_euler_step`). Лемма с названием
   `linear_euler_is_gronwall` (`:210`) имеет вид `x = x` и доказана `reflexivity`; содержательное утверждение
   (траектория Эйлера за $n$ шагов есть $y_0(1+Lh)^n$ и совпадает с однородной итерацией Гронуолла) доказано в
   `Check.v`, раздел 2: `linear_euler_closed`, `linear_euler_gronwall`; рост при $L>0$ — `linear_growth`.
   Страница эту лемму не называет.
4. **Стр. 79: «переносит всё сказанное на пары».** О парах в файле доказаны только законы шага (развёртывание
   определения) и первое уравнение редукции порядка; липшицевость, сжатие и оценка расхождения для систем не
   записаны. Сноска 7 называет ровно доказанное.
5. **Стр. 83–85, сноска 8: редукция порядка.** `order2_position_step` говорит о первом уравнении ($y'=v$),
   которое выполнено по построению. Что позиция удовлетворяет разностному уравнению второго порядка, в файле не
   записано; доказано в `Check.v`, раздел 4: `order2_second_difference`:
   $y_{k+2}-2y_{k+1}+y_k = h^2 g(t_k,y_k,v_k)$. В формализации только второй порядок и только пары.
6. **Стр. 91–98: дрейф энергии.** Доказано одно вычисление (два шага, $h=1/10$) — страница так и говорит.
   Слова «систематический рациональный дрейф» (стр. 98) общего утверждения в файле не имеют; оно верно и
   доказано в `Check.v`, раздел 4: `sho_energy_step` ($E_{k+1} = (1+h^2)E_k$ при любых $h$, $y_0$, $v_0$),
   `sho_energy_closed` ($E_n=(1+h^2)^nE_0$), `sho_energy_strict` (строгий рост при $h \ne 0$, $E_0>0$). Число
   главы $1{,}0201$ есть $(1+1/100)^2$.
7. **Стр. 87: «Его точное решение — $(\cos t, \sin t)$».** Для пары $y'=v$, $v'=-y$ с $y(0)=1$, $v(0)=0$ вторая
   координата есть $y' = -\sin t$; пара $(\cos t, \sin t)$ первому уравнению не удовлетворяет. Формализация
   это показывает: `sho_v2` даёт $v_2=-1/5$, а первый шаг даёт $v_1=-h$ (`Check.v`, `sho_v1`). Точнее было бы
   «$(\cos t, -\sin t)$». Это замечание о математике страницы, а не о формализации; та же запись стоит в шапке
   `ProcessODESystem.v`.
8. **Стр. 11–13, 143, 166–168: «сжатие» без условия.** `picard_op_contraction` даёт оценку с коэффициентом
   $L\cdot T$ при любом его значении; сжатием она становится при $L\cdot T<1$. В этих трёх местах условие не
   повторено; оно названо на стр. 123.
9. **Стр. 168–169: единственность на сетке.** `picard_unique` доказана под посылкой $L\cdot T<1$ через конечный
   максимум — как и сказано. Сама единственность от этой посылки не зависит: неподвижная точка сеточного
   оператора есть ломаная Эйлера, она существует при любой правой части и единственна при одной липшицевости
   (`Check.v`, раздел 7: `picard_fixed_is_euler`, `egrid_is_fixed`, `picard_unique_without_rate`); итераты
   Пикара достигают её точно за $N$ шагов (`picard_iter_reaches_euler`). Это относится к Главе 8.3; здесь — к
   сведению.
10. **Сноска 11: «промежуточные шаги — `traj_step1`–`traj_step4`».** Это четыре вычисления `price_step` на
    числах, а не утверждения о траектории; все шесть стадий подтверждены одним вычислением `price_history`
    (`Check.v`, `price_history_ex`). `traj_step1` записана с равенством Лейбница, остальные — с `Qeq`.

## Вне главы (исходники)

- `ProcessODEExamples.v`: внутренний комментарий «STATUS: 25 Qed» (стр. 26) при действительных 20 (шапка — 20,
  верно). В шапке «logistic growth» — такого примера в файле нет. Комментарий к `linear_rhs_lipschitz` —
  «constant |L|», утверждение — при `0 < L` с постоянной `L`.
- Там же: `linear_euler_is_gronwall` (`:210`) — равенство терма самому себе. `cluster_linear_euler_gronwall`
  (`:227`) — посылки `0 < L`, `0 < h` в доказательстве не используются (это `gronwall_beta_zero`).
  `cluster_picard_euler_rate` (`:235`) — равенство по определению: обе скорости суть `L * h`.
  `cluster_convergence` (`:242`) — заключение после развёртывания определений есть трижды повторённое
  `0 < L * h < 1` (`Check.v`, раздел 6: `cluster_rate_by_definition`, `cluster_convergence_unfolded`).
- Там же: итоговая теорема `ode_examples_summary` (`:266`, «every ODE with Lipschitz RHS yields a process
  triple») берёт посылку `is_bounded_auto g M` — ограниченность правой части на всём `Q`. Правые части
  примеров 1, 2 и 4 этого файла ей не удовлетворяют ни при каком `M` (`Check.v`, раздел 6:
  `exp_rhs_not_bounded`, `decay_rhs_not_bounded`, `linear_rhs_not_bounded`); удовлетворяет только постоянная
  (`const_rhs_bounded`). Заключительные комментарии файла («All share the same framework: Picard contraction →
  process») для экспоненты, затухания и линейного уравнения этой теоремой не подкреплены. Страница теорему не
  называет.
- `PriceDynamicsODE.v`: шапка «STATUS: 25 Qed» при действительных 23; строка шапки «Rules: Lipschitz < 1
  implies stable dynamics» теоремы не имеет (расхождение 3).
- `ProcessExpProcess.v`, шапка (стр. 21–25): монотонность, равномерная граница и свойство Коши названы
  недоказанными, последнее — «classic-based»; все три доказуемы без аксиом (расхождение 1; граница в пробном
  файле — $4$, не $3$).
- `ProcessODESystem.v`, шапка: «(dynamical systems proper are Part IX)» — Часть IX тома есть «Уравнения в
  частных производных»; «joint VECTOR process on ℚⁿ» — в файле только пары; «(cos, sin)» — см. сомнительное
  место 7.
- `FixedPoint.v` (стр. 12), `SeriesConvergence.v` (стр. 12): «AXIOMS: classic…» — для `iterate_is_cauchy`,
  `banach_fixed_point`, `Qpow_vanish`, `Qpow_limit_zero` компилятор даёт «Closed under the global context»; в
  `FixedPoint.v` `classic` не берёт ни одно объявление, в `SeriesConvergence.v` — пять (перечислены в
  расхождении 1). Шапки `ProcessPicardOperator.v` (стр. 20–22) и `ProcessODEStability.v` (стр. 26–27) повторяют
  ту же отсылку к «L3/classic-based» слою.
