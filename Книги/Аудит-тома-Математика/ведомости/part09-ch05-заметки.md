# Глава IX.5 «Навье–Стокс и синтез» — заметки к ведомости (23.11.2026)

Ведомость: `part09-ch05.json` — 51 ручная запись + 2 автоматические (упоминания файлов); `merge --dry` проходит
без замечаний, список «без сверки» пуст. Вердикты ручных записей: ok — 22, mismatch-statement — 25,
mismatch-price — 4. Имён без объявления и неверных чисел нет.

29 записей с расхождением относятся к девяти местам: расхождение 1 (нелинейный член) — 2 записи; 2 (система
уравнений не объявлена) — 2; 3 (тождество для скорости энергии) — 2; 4 (оценка энергии «безусловно») — 5;
5 (два измерения) — 4; 6 (три измерения «условно») — 6; 7 (на чём держится условность) — 1; 8 (формулировка
зазора) — 3; 9 (цена: «доменные аксиомы») — 4.

Глава называет шесть файлов каталога `src/navier_stokes/`: `GalerkinSystem.v` (533 строки, 31 `Qed`),
`EnergyEstimate.v` (399, 25), `AttackSynthesis.v` (367, 33), `ConcentrationBound.v` (300, 20),
`TriadicInteraction.v` (599, 37), `HonestAssessment.v` (390, 26). Все шесть прочитаны целиком; целиком прочитаны
также `InvariantRegion.v` (576, 28), `GalerkinFiniteRegularity.v` (137, 4) и `README.md` каталога; по определениям
и названным теоремам — `Vorticity.v`, `PerModeBound.v`, `GronwallAnalysis.v`, `EnstrophyProduction.v`,
`ResolutionRegularity.v`, `ProcessNS.v`, `TransientClosure.v`, `LowModeControl.v`, `MillenniumComplete.v`,
`AdvectionEnergyConservation.v`. Для итоговых слов о Части IX прочитаны утверждения пяти файлов триптиха
(`process/ProcessHeatEquation.v`, `process/ProcessPDEGreen.v`, `process/ProcessWaveEnergy.v`,
`acoustics/WavePropagation.v`, `process/ProcessTransport.v`).

Что снято с компилятора:

- `Print Assumptions` всех 881 объявлений `Lemma`/`Theorem` 36 файлов каталога `navier_stokes` (`PA.v`): 880 —
  «Closed under the global context», одно — `galerkin_finite_regularity_capstone` — `Classical_Prop.classic`.
  Строк `Axiom`, `Parameter`, `Admitted` в каталоге нет; библиотека `Reals` не подключается;
- `Print Assumptions` всех 43 объявлений пяти файлов триптиха (`PA2.v`): все — «Closed under the global context»;
- типы всех 881 теоремы (`Types.v`): запись `NSCoupling` аргументом получают 318, не получают 563;
- `Print All Dependencies` семи теорем (`Deps.v`): от поля-оценки `B_raw_antisym_bounded` зависит `forcing_bound`;
  `conditional_regularity_theorem`, `region_invariant`, `millennium_reading2_capstone`, `ns_galerkin_bound_chain`,
  `honest_assessment_main` зависят только от `C_B_positive`; `energy_rate_formula` — от `B_raw`, `B_coeff`,
  `B_antisym`, а от `C_B_positive` и от оценки не зависит;
- исходники каталога в репозитории и в собранной копии совпадают (`diff`; в копии нет только `README.md`).

Блоков кода в главе нет (инструмент: «БЛОКИ КОДА: объявлений 0»). Три «прочих фрагмента кода» — строчные
фрагменты в обратных кавычках; сверены все: `B_coeff k l m := B_raw k l m - B_raw k m l` (сноска 2) совпадает с
определением `GalerkinSystem.v:245`; `stretching_2d == 0` (сноска 4) совпадает с утверждением `unconditional_2d`;
`navier_stokes/` (сноска 1) — каталог есть. Итоговых теорем `MillenniumComplete.v` страница не называет: ни
прежних имён (`millennium_complete_final`, `navier_stokes_millennium`), ни новых на ней нет.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part09/ch05/`:

- `status.txt` — вывод `tom-status.cjs chapter 09/05`; `status-ch01.txt` … `status-ch04.txt` — то же для Глав 9.1–9.4
  (взяты списки файлов);
- `PA.v`, `PA.out`; `PA2.v`, `PA2.out`; `Types.v`, `Types.out`; `Deps.v`, `Deps.out` — см. выше;
- `Check.v`, `Check.out` — пробные доказательства, разделы 0–6 по местам главы. Собирается: 38 `Qed`, одно
  `Defined`; все 29 утверждений, для которых снят `Print Assumptions`, — «Closed under the global context».

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Главы 9.1–9.4 по содержанию не сверялись — это предмет их ведомостей. По строкам таблицы «Карта границ»
  проверены только существование названных утверждений и цена («0 аксиом») по компилятору.
- Из 36 файлов каталога целиком прочитаны девять; остальные — по списку определений, по названным теоремам и по
  выводу компилятора. Утверждать что-либо о каждой из 881 теоремы эти заметки не берутся.
- Зависимость от поля `B_raw_antisym_bounded` проверена компилятором для семи теорем, для остальных — поиском
  имён по исходникам (поле и опирающиеся на него леммы встречаются только в `TriadicInteraction.v`).
- В пункте (а) расхождения 6 не доведена посылка об оценке нелинейного члена в области: её вывод из оценки
  связи требует правила отбора триад, которого в записи `NSCoupling` нет; сказано, что нужно дописать.
- В пункте (а) расхождения 8 доказана только неограниченность постоянной по $K$; сопоставление показателей
  $\alpha=2$ и $\alpha=1$ не доказывалось.
- В пункте (а) расхождения 5 «двумерный тип» коэффициента показан на одной триаде; семейство таких
  коэффициентов при всяком $K$ и вывод из двумерной геометрии не строились.
- Предложенные добавления проверены как пробный файл поверх собранных модулей (`Check.v`); как файлы `src` с
  записью в `_CoqProject` они не собирались.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Что стоит за разделами главы (сводка)

| раздел главы | что в `.v` есть общего | что стоит посылкой или определением | чего в `.v` нет |
|---|---|---|---|
| соединение триптиха | состояние `modal_state := nat -> Q`; энергия, энстрофия; кубическая сумма `triple_sum`; `B_antisym` | коэффициент — антисимметризация `B_raw` по двум последним индексам | правой части системы как объекта; шага схемы с нелинейным членом; давления и несжимаемости; правила отбора триад |
| энергетический метод | `nonlinear_energy_zero`; `enstrophy_ge_energy`; `viscous_dissipation` | вязкая скорость энергии равна $-2\nu\Omega$ по определению; убывание энергии по шагам — посылка `energy_decreasing` | связи «скорости» с какой-либо траекторией; траектории, для которой посылка доказана |
| два измерения | `enstrophy_bounded_2d` (индукция по посылке) | `stretching_2d := 0`; убывание энстрофии — посылка `enstrophy_decreasing` | размерности; вытяжения как величины, зависящей от состояния |
| три измерения | `harmonic_linear_bound` ($2H_n\le n+1$); `smooth_in_region` (гладкие начальные данные лежат в области) | `conditionally_regular` — пошаговая форма заключения; оценка нелинейного члена в области — формула `forcing_in_region` | сохранения области шагом схемы; связи области с энстрофией; связи `forcing_in_region` с коэффициентом записи |
| «стена» | $\Omega^2\le E\cdot P$ (`ep_interpolation`); монотонность постоянной по $K$ | показатель 2 — в определении `stretching_enstrophy_bound` | утверждения о показателях; утверждения о приёмах |

В каталоге есть и содержательный результат, которого глава не называет: `burgers_conserves_energy`
(`AdvectionEnergyConservation.v:118`) — для периодической сеточной функции сумма
$(u_i^2+u_iu_{i+1}+u_{i+1}^2)(u_{i+1}-u_i)$ по периоду равна нулю (телескопирование кубов); это сеточный аналог
$\int (u\cdot\nabla u)\cdot u=0$ для одномерной адвекции, без посылок и без аксиом.

## Расхождение 1. Антисимметрия по $(l,m)$ обнуляет нелинейный член каждой моды: перераспределения в формализации нет (стр. 60–62; сноска 2, стр. 179)

**Было:**

> (60–62) Антисимметрия означает: нелинейность энергию только *перераспределяет*, как линейный перенос
> перераспределял массу (Глава 9.4). Тогда единственный сток энергии — вязкая диффузия.
>
> (сноска 2) Она формализует, что конвекция *сохраняет* энергию (лишь перебрасывает её между модами), не создавая
> и не уничтожая — дискретный аналог того, что $\int (u\cdot\nabla u)\cdot u = 0$.

**Проверка.** `src/navier_stokes/GalerkinSystem.v`:

```coq
Definition B_coeff (k l m : nat) : Q := B_raw k l m - B_raw k m l.                 (* :245 *)
Lemma B_antisym : forall k l m, B_coeff k l m == -(B_coeff k m l).                 (* :249 *)
Definition inner_double_sum (K : nat) (k : nat) (a : modal_state) : Q :=           (* :288 *)
  sum_Q_ns (fun l => sum_Q_ns (fun m => B_coeff k l m * a l * a m) K) K.
Lemma inner_double_sum_self_neg : forall K k (a : modal_state),                    (* :300 *)
  inner_double_sum K k a == - inner_double_sum K k a.
Theorem nonlinear_energy_zero : forall K (a : modal_state), triple_sum K a == 0.   (* :326 *)
```

`inner_double_sum K k a` есть нелинейный член уравнения моды $k$ из шапки файла
(«da_k/dt = -nu*k^2*a_k + sum_{l,m} B_{klm} a_l a_m», стр. 5). Из `inner_double_sum_self_neg` следует, что он
равен нулю при всяком $k$, всяком состоянии и всякой записи посылок (`Check.v`, раздел 1):

```coq
Lemma nl_mode_zero : forall (nsc : NSCoupling) K k (a : modal_state),
  inner_double_sum K k a == 0.
Proof. intros nsc K k a. pose proof (inner_double_sum_self_neg K k a) as H. lra. Qed.

Lemma formal_rhs_is_viscous : forall (nsc : NSCoupling) nu K (a : modal_state) k,
  formal_rhs nu K a k == - nu * inject_Z (Z.of_nat ((k+1)*(k+1))) * a k.
(* Print Assumptions: Closed under the global context *)
```

Причина: множитель $a_la_m$ симметричен по $(l,m)$, поэтому коэффициент, антисимметричный по $(l,m)$, даёт
нулевую квадратичную форму. Это верно без записи посылок и без всякой оценки (`antisym_quadratic_form_zero`).
Теорема `nonlinear_energy_zero` верна, но утверждает нуль суммы нулей. Комментарий исходника (`:189–192`:
«работу совершает только антисимметричная часть сопряжения; симметричная часть аннулируется») говорит обратное
доказанному.

**В чём расхождение.** Страница говорит, что нелинейность перераспределяет энергию между модами; в
формализации при заявленной антисимметрии нелинейный член каждой моды тождественно равен нулю — перераспределять
нечему.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом и без посылок. Энергию при ненулевом переносе
сохраняет антисимметрия по первому и третьему индексу (проверяемая мода $k$ и переносимая мода $m$): так
устроена форма $((u\cdot\nabla)v, w) = -((u\cdot\nabla)w, v)$. Предлагается новый файл, например
`src/navier_stokes/GalerkinAdvection.v` (существующие файлы не трогаются). Набросок проверен: `Check.v`,
раздел 3, все утверждения — Closed under the global context.

```coq
Definition nl (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) (k : nat) : Q :=
  sum_Q_ns (fun l => sum_Q_ns (fun m => B k l m * a l * a m) K) K.

Definition adv (T : nat -> nat -> nat -> Q) (k l m : nat) : Q := T k l m - T m l k.

Lemma adv_antisym : forall T k l m, adv T k l m == - adv T m l k.

(** Перестановка крайних индексов тройной суммы (три применения sum_ns_swap). *)
Lemma sum3_rev : forall K (h : nat -> nat -> nat -> Q),
  sum_Q_ns (fun k => sum_Q_ns (fun l => sum_Q_ns (fun m => h k l m) K) K) K ==
  sum_Q_ns (fun m => sum_Q_ns (fun l => sum_Q_ns (fun k => h k l m) K) K) K.

(** Сохранение энергии: для всякого сырого коэффициента T и всякого состояния. *)
Theorem adv_energy_zero : forall T K (a : nat -> Q),
  sum_Q_ns (fun k => a k * nl (adv T) K a k) K == 0.

(** Перенос между модами ненулевой: T0 0 0 1 = 1, прочие нули; состояние (1, 1). *)
Lemma adv_nl_nonzero :
  nl (adv T0) 2 a11 0%nat == 1 /\ nl (adv T0) 2 a11 1%nat == -(1).

(** Тот же сырой коэффициент, антисимметризованный по (l,m), как в B_coeff: нуль. *)
Lemma lm_antisym_nl_zero : forall (T : nat -> nat -> nat -> Q) K (a : nat -> Q) k,
  nl (fun k l m => T k l m - T k m l) K a k == 0.
```

Доказательство `adv_energy_zero`: множитель $a_k$ вносится под суммы, слагаемое принимает вид
$g(k,l,m)-g(m,l,k)$ с $g(k,l,m)=T(k,l,m)\,a_ka_la_m$, а сумма второго слагаемого после перестановки крайних
индексов (`sum3_rev`) совпадает с суммой первого. Полный текст — `Check.v`, стр. 205–260. Посылки теоремы пусты:
оценка связи для сохранения энергии не нужна.

**(б) Поправить слова.** Если формализация дополнена по пункту (а), меняется и формула антисимметрии (стр. 59):

> Ключевое свойство нелинейности — антисимметрия коэффициента по проверяемой и переносимой модам,
> $B(k,l,m) = -B(m,l,k)$; в формализации это лемма: коэффициент задан как антисимметризация абстрактной
> связи.[^2] Антисимметрия означает: нелинейность энергию только *перераспределяет*, как линейный перенос
> перераспределял массу (Глава 9.4). Тогда единственный сток энергии — вязкая диффузия.

> [^2]: `adv_antisym` в `GalerkinAdvection.v` — лемма: `adv T k l m := T k l m - T m l k`, `T` — произвольный
> сырой коэффициент; аксиом и посылок нет. Теорема `adv_energy_zero` формализует, что конвекция *сохраняет*
> энергию (лишь перебрасывает её между модами: `adv_nl_nonzero`), не создавая и не уничтожая — дискретный аналог
> того, что $\int (u\cdot\nabla u)\cdot u = 0$; сеточная форма того же — `burgers_conserves_energy`
> (`AdvectionEnergyConservation.v`).

Если формализация не дополняется:

> Антисимметрия означает: кубическая сумма нелинейного члена в балансе энергии равна нулю
> (`nonlinear_energy_zero`). В формализации это выполнено в вырожденном виде: при антисимметрии по $(l,m)$
> нелинейный член каждой моды равен нулю, и перераспределение энергии между модами в формальном слое не
> представлено. Единственный сток энергии — вязкая диффузия.

> [^2]: `B_antisym` в `GalerkinSystem.v` — лемма: `B_coeff k l m := B_raw k l m - B_raw k m l`, `B_raw` —
> поле записи посылок; аксиом в файле нет. Из неё следует `nonlinear_energy_zero` — нуль кубической суммы; сумма
> по $(l,m)$ при этом равна нулю для каждой моды в отдельности. Сеточный аналог того, что
> $\int (u\cdot\nabla u)\cdot u = 0$, доказан отдельно: `burgers_conserves_energy` (`AdvectionEnergyConservation.v`).

## Расхождение 2. Система уравнений для амплитуд в формализации не объявлена; шаг схемы есть только вязкий (стр. 56–58, 126–128)

**Было:**

> (56–58) ToS ведёт это как процесс — галёркинский (модальный): поле раскладывается по конечному числу мод, и
> эволюция каждой амплитуды задаётся системой обыкновенных уравнений с *триадным* взаимодействием $B(k,l,m)$
> между модами.
>
> (126–128) *Rules*: на всех уровнях — сетка, конечно-разностная схема
> $u^{n+1}=u^n+\Delta t \mathcal L_h u^n$ и конечные законы (энергия, масса, причинность, максимум).

**Проверка.** Система стоит в комментарии шапки `GalerkinSystem.v` (стр. 4–5). Объявлений, задающих её правую
часть, в каталоге нет: `B_coeff`, `inner_double_sum`, `triple_sum` используются только в `GalerkinSystem.v` и
`TriadicInteraction.v` (поиск по `src`); `mode_forcing` (`TriadicInteraction.v:191`) — сумма модулей, а не
нелинейный член. Шагов по времени два, оба без нелинейного члена:

```coq
(* ResolutionRegularity.v:44 *)
Definition euler_step (nu : Q) (K N : nat) (a : modal_state) : modal_state :=
  fun k => if Nat.ltb k K
           then a k + (1 / inject_Z (Z.of_nat N)) * (- nu * inject_Z (Z.of_nat (k * k)) * a k)
           else a k.
(* InvariantRegion.v:463 *)
Definition euler_step (nu : Q) (K : nat) (a : modal_state) (dt : Q) : modal_state :=
  fun k => a k + dt * (-(nu * inject_Z (Z.of_nat (k * k)) * a k)).
```

О траектории `euler_evolve` доказано: значение есть рациональное число, нулевое начальное состояние остаётся
нулевым, моды с номером $\ge K$ не меняются. С теоремами об энергии она не связана; второй шаг в теоремах не
участвует. Все оценки «по времени» кластера сформулированы для произвольной последовательности состояний
`u : time_series` под посылкой (расхождения 4–6). Правила отбора у коэффициента нет: `is_triad`
(`TriadicInteraction.v:65`) объявлено, но с `B_coeff` не связано; `triad_count k K := (2 * K)%nat` — определение,
а не подсчёт. Давления и условия несжимаемости в формализации нет.

**В чём расхождение.** Страница говорит, что эволюция амплитуд задана системой уравнений и что на всех уровнях
Части стоит схема шага; в формализации уровня Навье–Стокса система записана в комментарии, а схема шага объявлена
только для вязкой части.

**(а) Довести формализацию до слов главы.** Возможно. В том же новом файле объявляются правая часть, шаг и
траектория (проверено: `Check.v`, раздел 3):

```coq
Definition wgt (k : nat) : Q := inject_Z (Z.of_nat ((k+1)*(k+1))).
Definition grhs (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) (k : nat) : Q :=
  - nu * wgt k * a k + nl B K a k.
Definition gstep (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (dt : Q) (a : nat -> Q)
  : nat -> Q := fun k => a k + dt * grhs nu B K a k.
Fixpoint gtraj (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (dt : Q)
  (a : modal_state) (n : nat) : modal_state :=
  match n with O => a | S m => gstep nu B K dt (gtraj nu B K dt a m) end.
```

Это схема вида $a^{n+1}=a^n+\Delta t\,F(a^n)$ на конечном числе мод — тот же род, что схемы Глав 9.2 и 9.4.
Законы для неё — в расхождениях 3 и 4. Правило отбора триад и давление при этом по-прежнему не формализованы.

**(б) Поправить слова.** Если формализация не дополняется:

> (56–58) ToS ведёт это как процесс — галёркинский (модальный): поле раскладывается по конечному числу мод, и
> эволюция каждой амплитуды задаётся системой обыкновенных уравнений с *триадным* взаимодействием $B(k,l,m)$
> между модами. В формализации объявлены состояние (набор амплитуд), его энергия и энстрофия и кубическая сумма
> нелинейного члена; сама система записана в комментарии файла, а шаг по времени объявлен только для вязкой
> части.
>
> (126–128) *Rules*: на уровнях тепла, волны и переноса — сетка, конечно-разностная схема
> $u^{n+1}=u^n+\Delta t \mathcal L_h u^n$ (для волны — двухслойная) и конечные законы (энергия, масса,
> причинность, максимум); на уровне Навье–Стокса — модальные состояния и алгебраическое тождество баланса энергии.

Если добавлен файл из пункта (а), первое предложение (56–58) остаётся как есть, а во втором достаточно оговорки о
волне: «…конечно-разностная схема $u^{n+1}=u^n+\Delta t \mathcal L_h u^n$ (для волны — двухслойная)…».

## Расхождение 3. «Эволюционное тождество»: вязкая половина скорости энергии задана определением (стр. 78–80; сноска 3, стр. 180)

**Было:**

> (78–80) В модальном (галёркинском) слое это записано как эволюционное тождество для скорости энергии
> (`energy_rate_formula`, над рациональными процессами); классическая запись $dE/dt$ — его непрерывное чтение.
>
> (сноска 3) `energy_rate_formula` (`GalerkinSystem.v`: $dE/dt=-2\nu\Omega$; нелинейный вклад нулевой —
> `nonlinear_energy_zero`)

**Проверка.** `GalerkinSystem.v` (вывод `Print`, `Check.out`):

```coq
Definition viscous_energy_rate (nu : Q) (K : nat) (a : modal_state) : Q :=      (* :149 *)
  -(2) * nu * modal_enstrophy K a.
Definition nonlinear_energy_rate (K : nat) (a : modal_state) : Q := triple_sum K a.   (* :350 *)
Definition total_energy_rate (nu : Q) (K : nat) (a : modal_state) : Q :=        (* :364 *)
  viscous_energy_rate nu K a + nonlinear_energy_rate K a.
Theorem energy_rate_formula : forall nu K (a : modal_state),                     (* :393 *)
  total_energy_rate nu K a == -(2) * nu * modal_enstrophy K a.
```

После развёртывания определений теорема есть $-2\nu\Omega + \texttt{triple\_sum} = -2\nu\Omega$, то есть
`nonlinear_energy_zero`. Вязкое слагаемое из уравнений не вычислено — оно положено равным $-2\nu\Omega$.
`total_energy_rate` — функция одного состояния `a : nat -> Q` (номер — номер моды, а не шаг времени); ни с правой
частью системы, ни с разностью `energy_at K u (S n) - energy_at K u n` какой-либо последовательности она теоремой
не связана. `Print Assumptions`: Closed under the global context.

**В чём расхождение.** Тождество названо эволюционным и подано записью $dE/dt=-2\nu\Omega$; в формализации одна
его половина — определение, а связи с эволюцией нет.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. Скорость энергии вдоль правой части есть
$\sum_k a_kF_k(a)$; для правой части из расхождения 2 она выводится, и для шага схемы получается точное
тождество (проверено: `Check.v`, раздел 3, Closed under the global context):

```coq
Theorem galerkin_energy_rate : forall nu T K (a : nat -> Q),
  sum_Q_ns (fun k => a k * grhs nu (adv T) K a k) K == -(2) * nu * modal_enstrophy K a.
Proof.
  intros nu T K a. unfold grhs.
  transitivity (sum_Q_ns (fun k => (- nu) * (wgt k * a k * a k)
                                   + a k * nl (adv T) K a k) K).
  { apply sum_ns_ext. intros k _. ring. }
  rewrite (sum_ns_add (fun k => (- nu) * (wgt k * a k * a k))
                      (fun k => a k * nl (adv T) K a k) K).
  rewrite (sum_ns_scale (- nu) (fun k => wgt k * a k * a k) K).
  rewrite (adv_energy_zero T K a).
  unfold modal_enstrophy, wgt. ring.
Qed.

Lemma energy_step_identity : forall K (a F : nat -> Q) dt,
  modal_energy K (fun k => a k + dt * F k) ==
  modal_energy K a + dt * sum_Q_ns (fun k => a k * F k) K
  + (1#2) * dt * dt * sum_Q_ns (fun k => F k * F k) K.

Theorem galerkin_step_energy : forall nu T K dt (a : nat -> Q),
  modal_energy K (gstep nu (adv T) K dt a) ==
  modal_energy K a - 2 * nu * dt * modal_enstrophy K a
  + (1#2) * dt * dt
    * sum_Q_ns (fun k => grhs nu (adv T) K a k * grhs nu (adv T) K a k) K.
```

**(б) Поправить слова.** Если формализация не дополняется:

> В модальном (галёркинском) слое это записано как алгебраическое тождество для состояния
> (`energy_rate_formula`, над рациональными амплитудами): вязкий вклад в скорость энергии положен равным
> $-2\nu\Omega$, а нелинейный вклад — кубическая сумма — доказанно равен нулю; классическая запись $dE/dt$ — его
> непрерывное чтение.

Если добавлен файл из пунктов (а):

> В модальном (галёркинском) слое это записано как тождество для скорости энергии вдоль правой части системы,
> $\sum_k a_k F_k(a) = -2\nu\Omega$ (`galerkin_energy_rate`, над рациональными амплитудами), и как точное
> тождество шага схемы, $E(a^{n+1}) = E(a^n) - 2\nu\,\Delta t\,\Omega + \tfrac12 \Delta t^2 \sum_k F_k^2$
> (`galerkin_step_energy`); классическая запись $dE/dt$ — его непрерывное чтение.

Сноска 3, первая половина: «`energy_rate_formula` (`GalerkinSystem.v`: тождество баланса для состояния; вязкий
вклад $-2\nu\Omega$ взят по определению, нелинейный вклад нулевой — `nonlinear_energy_zero`)».

## Расхождение 4. «$E(t)\le E(0)$ безусловно»: в теореме убывание энергии стоит посылкой (стр. 31–32, 81–83; сноски 1 и 3)

**Было:**

> (31–32) Доказанное ядро — энергетическое, на модальном (галёркинском) процессе. *Безусловно*: энергия
> диссипирует и ограничена начальной;
>
> (81–83) Поэтому энергия *монотонно убывает* и ограничена начальной, $E(t)\le E(0)$ — и это *безусловный*
> результат.[^3]
>
> (сноска 1) `energy_bounded_by_initial` (`EnergyEstimate.v`, $E(t)\le E(0)$ безусловно)
>
> (сноска 3) и `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена
> начальной, безусловно. Опираются на `B_antisym`.

**Проверка.** `src/navier_stokes/EnergyEstimate.v`:

```coq
Definition time_series := nat -> modal_state.                                    (* :34 *)
Definition energy_decreasing (K : nat) (u : time_series) : Prop :=              (* :45 *)
  forall n, energy_at K u (S n) <= energy_at K u n.
Theorem energy_bounded_by_initial : forall K u,                                  (* :73 *)
  energy_decreasing K u -> forall n, energy_at K u n <= energy_at K u 0.
Theorem energy_monotone : forall K u,                                            (* :84 *)
  energy_decreasing K u ->
  forall m n, (m <= n)%nat -> energy_at K u n <= energy_at K u m.
```

`u` — произвольная последовательность состояний; с системой уравнений она не связана. Посылка
`energy_decreasing` — то самое убывание, которое страница выводит словом «поэтому». Обе теоремы доказаны
индукцией по посылке (`lra`); `Print Assumptions` — Closed under the global context; записи `NSCoupling` они
аргументом не получают (`About`, `Check.out`), то есть от коэффициента и от `B_antisym` не зависят вовсе. Посылка
`energy_decreasing` в `src` стоит только посылкой (шесть файлов каталога и `process/ProcessNavierStokesConnection.v`;
через определение `process_energy_bounded` — ещё `NSComplete.v` и `ResolutionRegularity.v`); ни для одной
последовательности она не доказана. В пробном файле (`Check.v`, раздел 2):

```coq
Lemma energy_bound_needs_premise :
  ~ (forall K (u : time_series) n, energy_at K u n <= energy_at K u 0).
(* u n := постоянное состояние со значением n; K = 1, n = 1 *)

Lemma galerkin_euler_energy_can_grow :
  modal_energy 2 a11 < modal_energy 2 (gstep (1#100) (adv T0) 2 1 a11).
(* явная схема для системы с сохраняющей энергию нелинейностью: за один шаг энергия выросла *)
```

Второй пример показывает, что и для схемы, у которой скорость энергии вдоль правой части неположительна,
оценка за шаг без условия на $\Delta t$ неверна: в тождестве шага стоит слагаемое $\tfrac12\Delta t^2\sum F_k^2$.

**В чём расхождение.** Страница называет оценку $E(t)\le E(0)$ безусловной и выведенной из тождества для
скорости; в формализации она доказана для последовательности состояний, о которой убывание энергии
предположено, а на `B_antisym` не опирается.

**(а) Довести формализацию до слов главы.** Безусловной оценки для явной схемы нет (контрпример выше). Без
аксиом доводится оценка при условии на шаг — и тогда посылка `energy_decreasing` впервые доказана для траектории.
Набросок проверен: `Check.v`, разделы 2 и 3, Closed under the global context.

```coq
(** Вязкая ломаная Эйлера из ResolutionRegularity.v (она же — вся формальная система,
    раз нелинейный член с B_coeff равен нулю): при nu*K^2 <= N энергия не растёт. *)
Theorem viscous_euler_energy_decreasing : forall nu K N (a0 : modal_state),
  0 <= nu -> (0 < N)%nat ->
  nu * inject_Z (Z.of_nat (K * K)) <= inject_Z (Z.of_nat N) ->
  energy_decreasing K (fun n => ResolutionRegularity.euler_evolve nu K N n a0).

Corollary viscous_euler_energy_bounded : forall nu K N (a0 : modal_state),
  0 <= nu -> (0 < N)%nat ->
  nu * inject_Z (Z.of_nat (K * K)) <= inject_Z (Z.of_nat N) ->
  forall n, modal_energy K (ResolutionRegularity.euler_evolve nu K N n a0)
            <= modal_energy K a0.

(** Схема с нелинейным членом: условие на шаг, при котором энергия за шаг не растёт. *)
Corollary galerkin_step_energy_le : forall nu T K dt (a : nat -> Q),
  0 <= dt ->
  dt * sum_Q_ns (fun k => grhs nu (adv T) K a k * grhs nu (adv T) K a k) K
    <= 4 * nu * modal_enstrophy K a ->
  modal_energy K (gstep nu (adv T) K dt a) <= modal_energy K a.

Theorem galerkin_traj_energy_bounded : forall nu T K dt (a0 : modal_state),
  0 <= dt ->
  (forall n,
     dt * sum_Q_ns (fun k => grhs nu (adv T) K (gtraj nu (adv T) K dt a0 n) k
                             * grhs nu (adv T) K (gtraj nu (adv T) K dt a0 n) k) K
     <= 4 * nu * modal_enstrophy K (gtraj nu (adv T) K dt a0 n)) ->
  energy_decreasing K (gtraj nu (adv T) K dt a0) /\
  (forall n, energy_at K (gtraj nu (adv T) K dt a0) n
             <= energy_at K (gtraj nu (adv T) K dt a0) 0).
```

Доказательство первой теоремы: на моде $i<K$ шаг умножает амплитуду на $1-c$ с $c=\nu i^2/N\in[0,1]$, поэтому
квадрат не растёт (`sq_contract`), и суммы сравниваются почленно. Условие второй пары теорем зависит от состояния
(оно ограничивает шаг через отношение $4\nu\Omega/\sum F_k^2$) и названо в теореме посылкой честно; равномерного
по траектории условия на шаг для системы с нелинейным членом здесь не получено.

**(б) Поправить слова.** Если формализация не дополняется:

> (31–32) Доказанное ядро — энергетическое, на модальном (галёркинском) процессе. *Безусловно*: скорость
> энергии в каждом состоянии неположительна. *При посылке, что энергия от шага к шагу не растёт*: она
> ограничена начальной;
>
> (81–83) Поэтому скорость энергии неположительна; для последовательности состояний, в которой энергия от шага
> к шагу не растёт (посылка `energy_decreasing`), энергия *монотонно убывает* и ограничена начальной,
> $E(n)\le E(0)$.[^3]
>
> (сноска 1) `energy_bounded_by_initial` (`EnergyEstimate.v`, $E(n)\le E(0)$ при посылке `energy_decreasing`)
>
> (сноска 3) и `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена
> начальной при посылке `energy_decreasing` (энергия не растёт от шага к шагу). На `B_antisym` опираются
> `nonlinear_energy_zero` и `energy_rate_formula`.

Если добавлены теоремы из пункта (а), к стр. 81–83 добавляется:

> Для ломаной Эйлера это убывание выведено из шага схемы при условии на шаг (`galerkin_traj_energy_bounded`;
> для вязкой части — `viscous_euler_energy_decreasing` при $\nu K^2\le N$); без условия на шаг явная схема
> энергию может увеличить.

Вывод курсивом на стр. 91–93 («оно безусловно и есть фундамент всего, что доказано о НС») — слово автора; как
тождество для состояния `energy_rate_formula` от оценок-посылок действительно не зависит (запись ведомости к
стр. 92).

## Расхождение 5. Два измерения: вытяжение задано нулём по определению, размерности в формализации нет (стр. 32–33, 97–100; сноски 1 и 4)

**Было:**

> (32–33) двумерное течение регулярно (нет вытяжения вихря).
>
> (99–100) Поэтому энстрофия остаётся под контролем, и в формальном галёркинском (модальном) слое кластера
> двумерное течение *регулярно безусловно*.[^4]
>
> (сноска 1) `unconditional_2d` (`AttackSynthesis.v`, двумерное вытяжение нулевое)
>
> (сноска 4) `unconditional_2d`: `stretching_2d == 0` (`AttackSynthesis.v`). Отсутствие вытяжения — причина
> безусловной двумерной регулярности.

**Проверка.**

```coq
Definition stretching_2d : Q := 0.                                               (* Vorticity.v:189 *)
Theorem stretching_vanishes_2d : stretching_2d == 0.                             (* Vorticity.v:191 *)
Theorem unconditional_2d : stretching_2d == 0.                                   (* AttackSynthesis.v:293 *)
Definition enstrophy_production_rate (nu C_s : Q) (K : nat) (a : modal_state) : Q :=   (* Vorticity.v:272 *)
  -(2) * nu * palinstrophy K a + stretching_enstrophy_bound C_s (modal_enstrophy K a).
Theorem enstrophy_dissipation_2d : forall nu K (a : modal_state),                (* Vorticity.v:289 *)
  0 < nu -> enstrophy_production_rate nu 0 K a <= 0.
Theorem full_regularity_2d : forall K u,                                         (* EnergyEstimate.v:201 *)
  energy_decreasing K u -> enstrophy_decreasing K u ->
  forall n, energy_at K u n <= energy_at K u 0 /\ enstrophy_at K u n <= enstrophy_at K u 0.
```

`stretching_2d` — число нуль; `unconditional_2d` есть `0 == 0` (`Check.v`: `stretching_2d_is_literal_zero`,
`reflexivity`). `enstrophy_dissipation_2d` — формула $-2\nu P + C_s\Omega^2$ при подставленном $C_s=0$.
`full_regularity_2d` берёт посылками убывание энергии и энстрофии. Моды нумерует одно натуральное число;
понятия размерности, завихренности как скаляра или вектора и вытяжения как величины, зависящей от состояния, в
каталоге нет. Все названные теоремы — Closed under the global context; записи `NSCoupling` они не получают.

**В чём расхождение.** Страница говорит, что в формальном слое двумерное течение регулярно безусловно; в
формализации двумерный случай задан тем, что постоянная названа нулём, а оценка энстрофии доказана под посылкой,
что энстрофия не растёт.

**(а) Довести формализацию до слов главы.** Вывести двумерность из геометрии в нынешней формализации не из
чего: мод с двумя индексами и коэффициентов действительной адвекции в ней нет. Честно доводится более слабое, но
содержательное: вытяжение как нелинейное производство энстрофии; коэффициенты, у которых оно равно нулю при
всяком состоянии; для них скорость энстрофии вдоль правой части равна $-2\nu P\le 0$. Набросок проверен
(`Check.v`, раздел 5, Closed under the global context):

```coq
Definition stretch (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) : Q :=
  sum_Q_ns (fun k => wgt k * a k * nl B K a k) K.

(** Триада на модах 0,1,2 (веса 1,4,9): da0 = -5 a1 a2, da1 = 8 a0 a2, da2 = -3 a0 a1. *)
Lemma Btri_energy        : forall a : nat -> Q, sum_Q_ns (fun k => a k * nl Btri 3 a k) 3 == 0.
Lemma Btri_no_stretching : forall a : nat -> Q, stretch Btri 3 a == 0.

(** У коэффициента adv T0 вытяжение ненулевое. *)
Lemma T0_stretching_nonzero : stretch (adv T0) 2 a11 == -(3).

Theorem no_stretching_enstrophy_rate : forall nu B K (a : nat -> Q),
  stretch B K a == 0 ->
  sum_Q_ns (fun k => wgt k * a k * grhs nu B K a k) K
  == -(2) * nu * Vorticity.palinstrophy K a.
```

Коэффициенты триады $(-5, 8, -3)$ суть $(w_1-w_2,\ w_2-w_0,\ w_0-w_1)$ при весах $w=(1,4,9)$: сумма равна нулю
(энергия), взвешенная сумма равна нулю (энстрофия). Не сделано: семейство таких коэффициентов при всяком $K$ и
оценка энстрофии на траектории (она, как и оценка энергии, потребует условия на шаг — расхождение 4).

**(б) Поправить слова.** Если формализация не дополняется:

> (32–33) двумерный случай задан нулевым вытяжением, и при посылке, что энстрофия от шага к шагу не растёт,
> она ограничена начальной.
>
> (99–100) Поэтому энстрофия остаётся под контролем. В формальном галёркинском (модальном) слое кластера
> двумерный случай *задан* нулевым вытяжением (постоянная `stretching_2d` равна нулю по определению), а оценка
> энстрофии начальной доказана при посылке, что энстрофия от шага к шагу не растёт.[^4]
>
> (сноска 1) `unconditional_2d` (`AttackSynthesis.v`: постоянная вытяжения двумерного случая, заданная нулём)
>
> (сноска 4) `unconditional_2d`: `stretching_2d == 0` (`AttackSynthesis.v`); `stretching_2d` — постоянная,
> заданная нулём в `Vorticity.v`. Оценка энстрофии при её убывании по шагам — `full_regularity_2d`
> (`EnergyEstimate.v`). Отсутствие вытяжения — причина двумерной регулярности; вывод этого отсутствия из
> уравнений в формализации не записан.

Если добавлены утверждения пункта (а), сноска 4 дополняется: «Для коэффициентов с нулевым нелинейным
производством энстрофии скорость энстрофии вдоль правой части равна $-2\nu P$ (`no_stretching_enstrophy_rate`);
пример такого коэффициента — триада `Btri`.»

## Расхождение 6. Три измерения «условно»: условием стоит само сохранение; названная теорема говорит о формуле (стр. 25, 33–34, 104–106, 112–113; сноски 1 и 5)

**Было:**

> (25) Во-вторых, трёхмерная регулярность доказана лишь *условно*;
>
> (33–34) *Условно* (в инвариантной области, при докритической энстрофии): трёхмерная регулярность.[^1]
>
> (104–106) В том же модальном слое регулярность доказана *условно* — если поле остаётся в инвариантной области
> (энстрофия докритична относительно $\nu$), оно регулярно; но что система туда попадает и там остаётся
> *безусловно*, не доказано.[^5]
>
> (сноска 1) `conditional_regularity_theorem` (трёхмерная регулярность при условии)
>
> (сноска 5) `conditional_regularity_theorem` и инвариантная область (`ConcentrationBound.v`, `EnergyEstimate.v`):
> при докритической энстрофии регулярность сохраняется. Безусловного перехода в эту область нет — это и есть
> зазор.

**Проверка.** Три разных утверждения стоят за этими словами.

```coq
(* ConcentrationBound.v:232; per_mode_amplitude nu E0 k := 2 * C_B * E0 / (nu * inject_Z (Z.of_nat k)) *)
Theorem conditional_regularity_theorem : forall nu E0,
  0 < nu -> 0 < E0 ->
  (forall k, (1 <= k)%nat -> 0 < per_mode_amplitude nu E0 k) /\
  (forall k, 0 <= enstrophy_contribution nu E0 k) /\
  (forall k1 k2, (1 <= k1)%nat -> (k1 <= k2)%nat ->
    per_mode_amplitude nu E0 k2 <= per_mode_amplitude nu E0 k1).

(* EnergyEstimate.v:248, :255 *)
Definition conditionally_regular (K : nat) (u : time_series) (nu C_stretch : Q) : Prop :=
  forall n, enstrophy_at K u n < critical_enstrophy nu C_stretch ->
            enstrophy_at K u (S n) <= enstrophy_at K u n.
Theorem regularity_3d_small_data : forall K u nu C_stretch,
  conditionally_regular K u nu C_stretch ->
  enstrophy_at K u 0 < critical_enstrophy nu C_stretch ->
  forall n, enstrophy_at K u n < critical_enstrophy nu C_stretch.

(* InvariantRegion.v:65, :448 *)
Definition in_region (nu : Q) (K : nat) (a : modal_state) : Prop :=
  forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (a k) <= A_inv nu / inject_Z (Z.of_nat k).
Theorem region_invariant : forall nu K, 0 < nu -> (1 <= K)%nat ->
  forall k, (1 <= k)%nat -> (k <= K)%nat -> forcing_in_region nu k <= boundary_damping nu k.
```

1. `conditional_regularity_theorem` — три свойства выражения $2C_BE_0/(\nu k)$: положительность, монотонность
   по $k$, неотрицательность взвешенного квадрата. Состояния, последовательности состояний, области и условия в
   ней нет.
2. `regularity_3d_small_data` — индукция по посылке: посылка `conditionally_regular` говорит, что докритическая
   энстрофия на следующем шаге не растёт, заключение — что она остаётся докритической. Последовательность `u`
   произвольна; постоянная `C_stretch` и «трёхмерность» в утверждении участвуют только через число
   `critical_enstrophy`.
3. «Инвариантная область» объявлена в `InvariantRegion.v` — файле, которого сноска 5 не называет (в
   `ConcentrationBound.v` и `EnergyEstimate.v` области нет). Теорема `region_invariant` есть неравенство между
   двумя формулами от $\nu$, $C_B$, $k$ (оно сводится к $2H_{k-1}\le k$); о том, что шаг какой-либо схемы
   оставляет состояние в области, в каталоге утверждения нет (`discrete_invariance_step`, `:476`, возвращает
   собственную посылку). С энстрофией область теоремой не связана: `enstrophy_bounded_in_R`
   (`TransientClosure.v:162`) заключает `0 <= modal_energy K a`.

Все названные теоремы — Closed under the global context. Связи `forcing_in_region` с коэффициентом записи нет, и
без дополнительной посылки её быть не может (`Check.v`, раздел 4б): для экземпляра записи с
$B_{raw}(k,1,2)=1$, $C_B=1$ состояние $(a_1,a_2)=(1,\tfrac12)$ лежит в области при $\nu=1$, а мажоранта
нелинейного члена первой моды `mode_forcing 1 3 a` равна 1 при `forcing_in_region 1 1 == 0`
(`forcing_in_region_not_a_bound`).

**В чём расхождение.** Страница говорит об условной трёхмерной регулярности в инвариантной области; в
формализации названная теорема говорит о формуле, а утверждение о последовательности состояний берёт условием
то, что требуется доказать, по шагам.

**(а) Довести формализацию до слов главы.** Условная теорема о траектории доводится без аксиом — как дискретная
теорема Нагумо: если в области нелинейный член моды не превосходит граничного затухания, а шаг удовлетворяет
$\Delta t\,\nu K^2\le 1$, то шаг схемы область сохраняет. Набросок проверен (`Check.v`, раздел 4, Closed under
the global context):

```coq
Definition gstep_gen (nu dt : Q) (Nl : modal_state -> nat -> Q) (a : modal_state)
  : modal_state :=
  fun k => a k + dt * (- (nu * inject_Z (Z.of_nat (k * k)) * a k) + Nl a k).

Theorem region_invariant_step :
  forall (nsc : NSCoupling) nu dt K (Nl : modal_state -> nat -> Q) (a : modal_state),
  0 < nu -> 0 <= dt ->
  dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  (forall k, (1 <= k)%nat -> (k <= K)%nat ->
     Qabs (Nl a k) <= boundary_damping nu k) ->
  in_region nu K a ->
  in_region nu K (gstep_gen nu dt Nl a).

Theorem region_invariant_iter :
  forall (nsc : NSCoupling) nu dt K (Nl : modal_state -> nat -> Q) (a0 : modal_state),
  0 < nu -> 0 <= dt ->
  dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 ->
  (forall b, in_region nu K b ->
     forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (Nl b k) <= boundary_damping nu k) ->
  in_region nu K a0 ->
  forall n, in_region nu K (giter nu dt Nl a0 n).

(** Вклад каждой моды в энстрофию на всей траектории не превосходит A^2. *)
Corollary region_iter_mode_enstrophy : (* те же посылки *)
  forall n k, (1 <= k)%nat -> (k <= K)%nat ->
    inject_Z (Z.of_nat (k * k)) * (giter nu dt Nl a0 n k * giter nu dt Nl a0 n k)
    <= A_inv nu * A_inv nu.
```

Ход первого доказательства: при $c=\Delta t\,\nu k^2\in[0,1]$ новое значение равно $(1-c)a_k+\Delta t\,N_k$, его
модуль не больше $(1-c)\,A/k+\Delta t\,\nu kA = A/k$. Полный текст — `Check.v`, стр. 417–460. Условие теоремы —
оценка нелинейного члена в области — названо посылкой; для формального нелинейного члена (с `B_coeff`) оно
выполнено тривиально, потому что он равен нулю (`formal_region_invariant`). Чтобы посылка следовала из оценки
связи для ненулевого члена, нужно дописать: (1) правило отбора в записи посылок — $B(k,l,m)=0$ при $l+m\ne k$;
(2) лемму $\lvert N_k(a)\rvert\le C_Bk\sum_{l+m=k}\lvert a_l\rvert\lvert a_m\rvert$; (3) тождество
$\sum_{l=1}^{k-1}\frac{1}{l(k-l)}=\frac{2H_{k-1}}{k}$. Это не проверялось. Замечание о силе результата: сумма
вкладов мод $\sum_{k\le K}k^2a_k^2\le KA^2$ растёт с $K$; оценки энстрофии, равномерной по $K$, область не даёт
(число `enstrophy_bound_in_region nu := nu^4/C_B^4 * 10`, `TransientClosure.v:138`, с энстрофией состояния не
сравнивается ни в одной теореме).

**(б) Поправить слова.** Если формализация не дополняется:

> (25) Во-вторых, трёхмерная регулярность доказана лишь *условно* — при посылке, что докритическая энстрофия
> от шага к шагу не растёт;
>
> (33–34) *Условно* (при посылке, что докритическая энстрофия от шага к шагу не растёт): она остаётся
> докритической на всех шагах.[^1]
>
> (104–106) В том же модальном слое регулярность доказана *условно* — если докритическая (относительно $\nu$)
> энстрофия от шага к шагу не растёт, она остаётся докритической на всех шагах; но что система этому условию
> удовлетворяет, не доказано.[^5]
>
> (сноска 1) `regularity_3d_small_data` (`EnergyEstimate.v`: докритическая энстрофия остаётся докритической при
> посылке `conditionally_regular`)
>
> (сноска 5) `regularity_3d_small_data` (`EnergyEstimate.v`): при посылке `conditionally_regular` докритическая
> энстрофия сохраняется. Область покомпонентных оценок $\lvert a_k\rvert\le A/k$ объявлена в `InvariantRegion.v`
> (`in_region`); доказано неравенство между оценкой нелинейного члена и затуханием на её границе
> (`region_invariant`), сохранение области шагом схемы не записано. Безусловного перехода в эту область нет — это и
> есть зазор.

Если добавлены теоремы пункта (а), стр. 104–106:

> В том же модальном слое регулярность доказана *условно* — если начальное состояние лежит в инвариантной
> области, нелинейный член в ней не превосходит граничного затухания и шаг схемы мал
> ($\Delta t\,\nu K^2\le 1$), то вся траектория остаётся в области (`region_invariant_iter`); но что система
> туда попадает и что оценка нелинейного члена выполнена *безусловно*, не доказано.[^5]

Стр. 112–113 («он формализует, *что именно* доказуемо (диссипация, двумерная регулярность, условная трёхмерная)»)
правится вслед за стр. 31–34; сама мысль — что ToS очерчивает рубеж, а не решает задачу, — с формализацией
согласна.

## Расхождение 7. Оценка связи `B_raw_antisym_bounded` названа опорой условности; теоремы о регулярности на неё не опираются (сноска 1, стр. 178; к стр. 24)

**Было:**

> *Посылки:* теоремы кластера получают аргументом запись `NSCoupling` (`GalerkinSystem.v`) — константу связи с её
> положительностью (`C_B_positive`) и оценку связи `B_raw_antisym_bounded`, на которой держится условность
> трёхмерной регулярности (в `TriadicInteraction.v` она же — лемма `B_coeff_bounded`). Объявлений-аксиом кластер
> не делает; в отличие от триптиха Глав 9.2–9.4, его результаты условны по этим посылкам.

**Проверка.**

1. Запись аргументом получают 318 теорем из 881 (`Types.out`). Не получают её, в частности,
   `energy_bounded_by_initial`, `energy_monotone`, `unconditional_2d`, `millennium_gap_precise`,
   `regularity_3d_small_data`, `galerkin_finite_regularity_capstone` и все 33 теоремы `AttackSynthesis.v`. Из
   названных в сноске 1 четырёх теорем запись получает одна — `conditional_regularity_theorem`.
2. Поле `B_raw_antisym_bounded` используют пять объявлений, все в `TriadicInteraction.v`: `B_coeff_bounded`
   (`:126`), `coupling_for_sum_triad` (`:130`), `nonlinear_term_bounded` (`:167`), `forcing_bound` (`:307`),
   `triadic_interaction_main` (`:583`). Ни одно из них в других файлах не используется (поиск по `src`).
3. По `Print All Dependencies` (`Deps.out`): `conditional_regularity_theorem`, `region_invariant`,
   `honest_assessment_main`, `millennium_reading2_capstone`, `ns_galerkin_bound_chain` зависят от `C_B_positive`
   и не зависят от `B_raw_antisym_bounded`, `B_raw`, `B_coeff`. Константа $C_B$ входит в них как положительное
   число в формулах ($A=\nu/C_B$, $2C_BE_0/(\nu k)$).
4. Экземпляр записи в формализации один — `NSCoupling_inhabited` (`GalerkinSystem.v:228`): нулевая связь,
   $C_B=1$; комментарий к нему оговаривает, что модель с коэффициентами действительной адвекции не строится.

**В чём расхождение.** Страница говорит, что условность трёхмерной регулярности держится на оценке связи; по
компилятору теоремы, названные этой регулярностью, оценку не используют, а большинство названных результатов
записи посылок не получают вовсе — их условность состоит в собственных посылках (`energy_decreasing`,
`conditionally_regular`).

**(а) Довести формализацию до слов главы.** Оценка связи станет опорой теоремы о регулярности, когда будет
дописана цепочка из пункта (а) расхождения 6: оценка нелинейного члена в области выводится из оценки связи (и
правила отбора), и на ней стоит `region_invariant_iter`. До этого доводить нечем.

**(б) Поправить слова.**

> *Посылки:* теоремы кластера, в которые входит константа связи, получают аргументом запись `NSCoupling`
> (`GalerkinSystem.v`) — константу связи с её положительностью (`C_B_positive`) и оценку связи
> `B_raw_antisym_bounded` (в `TriadicInteraction.v` она же — лемма `B_coeff_bounded`; на неё опирается оценка
> суммарного воздействия на моду, `forcing_bound`). Оценки по времени — энергии, энстрофии — от записи не
> зависят и условны по своим посылкам об убывании (`energy_decreasing`, `conditionally_regular`).
> Объявлений-аксиом кластер не делает; в отличие от триптиха Глав 9.2–9.4, его результаты условны.

Стр. 24 достаточно согласовать одним словом: «…и он *условен*: часть его теорем берёт посылками положительность
константы связи и оценку связи нелинейного члена (запись посылок `NSCoupling`: …), оценки по времени — посылки об
убывании энергии и энстрофии; с ноября 2026 года это посылки теорем, а не аксиомы проекта.»

## Расхождение 8. `millennium_gap_precise` — конъюнкция пяти утверждений; показателей в ней нет (стр. 108–111; сноски 1 и 6)

**Было:**

> (108–111) в ToS она помечена точно: между двумя показателями (квадратичной нелинейностью и тем, что было бы
> нужно для безусловного контроля) лежит зазор, который ни один известный приём не закрывает.[^6]
>
> (сноска 1) `millennium_gap_precise` (точная формулировка открытого зазора)
>
> (сноска 6) `millennium_gap_precise` (`AttackSynthesis.v`): точная формулировка зазора $\alpha=2$ против
> $\alpha=1$; сопровождается честной оценкой (`HonestAssessment.v`), что задача остаётся открытой.

**Проверка.** `AttackSynthesis.v:249` (вывод `Check`, `Check.out`):

```coq
Theorem millennium_gap_precise :
  (forall K u, energy_decreasing K u -> forall n, energy_at K u n <= energy_at K u 0) /\
  (forall C_lady K E_0 nu, 0 <= C_lady -> 0 <= E_0 -> 0 < nu ->
     0 <= k_dependent_rate C_lady E_0 nu K) /\
  (stretching_2d == 0) /\
  (forall K a, modal_enstrophy K a * modal_enstrophy K a <= modal_energy K a * palinstrophy K a) /\
  (forall C_lady E_0 nu K1 K2, 0 <= C_lady -> 0 <= E_0 -> 0 < nu -> (K1 <= K2)%nat ->
     k_dependent_rate C_lady E_0 nu K1 <= k_dependent_rate C_lady E_0 nu K2).
```

Первый конъюнкт — оценка энергии под посылкой (расхождение 4); третий — `0 == 0` (расхождение 5); второй и
пятый — неотрицательность и монотонность по $K$ числа `k_dependent_rate C E0 nu K = C*C*E0*K^2/nu`; четвёртый —
неравенство $\Omega^2\le E\cdot P$ (содержательное). Показателей 2 и 1 в утверждении нет. В кластере показатель
2 стоит в определении `stretching_enstrophy_bound C_s omega := C_s * omega * omega` (`Vorticity.v:196`), так что
`upper_bound_quadratic` (`:187`) есть $-2\nu P + C\Omega^2\le C\Omega^2$; показатель 1 — в `discrete_gronwall`
(`GronwallAnalysis.v:148`). О приёмах: `alpha_2_robust` (`:162`) — конъюнкция четырёх соотношений между числами,
`young_preserves_degree` (`HonestAssessment.v:196`) имеет вид `0 < eps -> 0 < eps`. `HonestAssessment.v` — 26
теорем о положительности и сравнении чисел (`not_solved`, `:339`: $(C_0+A)^2>A^2$); что задача открыта, сказано в
комментариях. Closed under the global context.

**В чём расхождение.** Страница называет теорему точной формулировкой зазора между показателями; утверждение
теоремы о показателях не говорит и состоит из пяти несвязанных между собой фактов.

**(а) Довести формализацию до слов главы.** Частично. В терминах самого кластера зазор есть отсутствие оценки,
равномерной по $K$: постоянная линейной оценки при фиксированном $K$ не ограничена. Этого в теореме нет
(есть только монотонность); доказано в пробном файле (`Check.v`, раздел 6, Closed under the global context):

```coq
Theorem k_rate_unbounded : forall C_lady E_0 nu M,
  0 < C_lady -> 0 < E_0 -> 0 < nu ->
  exists K : nat, M < GronwallAnalysis.k_dependent_rate C_lady E_0 nu K.
(* nat_archimedean (MonotoneConvergence.v:74) и K <= K*K *)
```

Сопоставление показателей не проверялось. Его честная форма над ℚ: для разностного неравенства
$y_{n+1}\le(1+hC)y_n$ значение в момент $T=nh$ ограничено равномерно по шагу $h$ (следует из
`discrete_gronwall` и границы лестницы $(1+s/n)^n$, `process/ProcessExpLadder.v`), а для разностного уравнения
$y_{n+1}=y_n+hCy_n^2$ при $T>1/(Cy_0)$ такой равномерной по $h$ границы нет. Утверждение «ни один известный приём
не закрывает» теоремой быть не может; это слово автора.

**(б) Поправить слова.**

> (108–111) в ToS она помечена так: оценка энстрофии при фиксированном числе мод $K$ есть, но её постоянная
> растёт с $K$; между квадратичной нелинейностью и тем, что было бы нужно для безусловного контроля, лежит
> зазор, который ни один известный приём не закрывает.[^6]
>
> (сноска 1) `millennium_gap_precise` (свод доказанного по обе стороны зазора)
>
> (сноска 6) `millennium_gap_precise` (`AttackSynthesis.v`) — свод: оценка энергии при её убывании по шагам,
> неравенство $\Omega^2\le E\cdot P$, монотонный рост по $K$ постоянной оценки при фиксированном $K$. Сами
> показатели $\alpha=2$ и $\alpha=1$ в утверждении не стоят: квадратичная оценка вытяжения введена определением
> (`Vorticity.v`), линейный случай — `discrete_gronwall` (`GronwallAnalysis.v`). `HonestAssessment.v` — числовые
> соотношения для порога $A=\nu/C_B$; что задача остаётся открытой, в файле сказано комментарием.

Если добавлена теорема пункта (а): в сноске 6 «монотонный рост по $K$» заменить на «неограниченный рост по $K$
(`k_rate_unbounded`)».

## Расхождение 9. Цена: «доменные аксиомы», «не претендует на 0-аксиомность» — по компилятору аксиом нет (стр. 37–38, 40, 140, 143–144)

**Было:**

> (37–38) не строит завершённое непрерывное решение и не претендует на 0-аксиомность НС-слоя.
>
> (40) *Первый* — доказанное (с доменными аксиомами): диссипация энергии, двумерная регулярность безусловно,
> трёхмерная — условно.
>
> (140) | 9.5 Навье–Стокс | диссипация, 2D регулярно, 3D условно | доменные аксиомы о константе связи (+ L3) |
>
> (143–144) Навье–Стокс — доказательно богаче, но честно несёт доменные аксиомы о константе связи и упирается в
> открытую трёхмерную стену.

**Проверка.** `PA.v`, `PA.out`: 881 объявление `Lemma`/`Theorem` в 36 файлах каталога; 880 — «Closed under the
global context»; одно —

```
galerkin_finite_regularity_capstone
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

Строк `Axiom` и `Parameter` в каталоге нет: `C_B`, `C_B_positive`, `B_raw` и оценка связи с 13.11.2026 — поля
записи `NSCoupling` (`GalerkinSystem.v:216`). Сама страница на стр. 24 и в сноске 1 говорит это же («посылки
теорем, а не аксиомы проекта», «объявлений-аксиом кластер не делает»); четыре места выше остались от прежнего
положения.

**В чём расхождение.** В четырёх местах страница называет цену слоя доменными аксиомами; по компилятору аксиом у
слоя нет, а условность стоит в посылках теорем.

**(а) Довести формализацию до слов главы.** Доводить нечего: формализация по цене сильнее этих слов.

**(б) Поправить слова.**

> (37–38) не строит завершённое непрерывное решение и не претендует на безусловность НС-слоя: его результаты
> стоят под посылками.
>
> (40) *Первый* — доказанное (под посылками, без аксиом): …
>
> (140) | 9.5 Навье–Стокс | … | 0 аксиом; условно по посылкам (запись константы связи; убывание по шагам); одна
> теорема — на L3 |
>
> (143–144) Навье–Стокс — доказательно богаче, но честно несёт посылки — о константе связи и об убывании
> энергии и энстрофии по шагам — и упирается в открытую трёхмерную стену.

Средняя клетка строки 140 и перечень стр. 40 («диссипация, 2D регулярно, 3D условно») правятся вслед за
расхождениями 4–6, например: «баланс энергии состояния; оценки энергии и энстрофии при их убывании по шагам».

## Сомнительные места (расхождением не являются)

1. **Стр. 24: «его теоремы берут посылками…».** Запись получают 318 теорем из 881; остальные 563 от коэффициента
   и константы связи не зависят (расхождение 7). Запись в ведомости — ok: класс, поля и статус «посылки, а не
   аксиомы» названы верно.
2. **Экземпляр записи посылок.** Он один — нулевая связь (`NSCoupling_inhabited`); для неё все теоремы кластера
   верны, так что о коэффициентах действительной адвекции они ничего не утверждают. Комментарий исходника
   оговаривает это; на странице оговорки нет.
3. **Стр. 58: «триадным взаимодействием».** Правило отбора (`is_triad`) объявлено, но с коэффициентом не
   связано: суммы идут по всем парам $(l,m)$ (расхождения 2 и 6).
4. **Стр. 80–81: «давление — тоже».** Давления и условия несжимаемости в формализации нет; теоремы с этим
   словом в имени (`pressure_smooth`, `ClassicalRegularity.v:270`; `pressure_from_velocity`,
   `GalerkinConvergence.v:326`) утверждают положительность постоянной. Фраза страницы относится к классическому
   уравнению и формализации не приписана.
5. **Стр. 137–139: строки таблицы о Главах 9.2–9.4.** Цена «0 аксиом» верна по компилятору. По содержанию:
   «диссипация энергии» — невозрастание за один шаг на периодической сетке (`heat_step_energy`); «конечная
   скорость» — локальность одного шага и одно вычисление на пяти узлах; «сохранение массы» — за один шаг на
   периодической сетке. Сверка формулировок — в ведомостях этих глав.
6. **Сноска 1: «Точные имена и счётчики — по `README`/`CLAUDE` репозитория».** `README.md` каталога отстал:
   «34 files | 654 Qed | 3 axioms» при 36 файлах, 882 строках `Qed.` и отсутствии аксиом; из пяти его «Key
   Theorems» двух имён в `src` нет (`energy_dissipation_identity`, `invariant_region_stable`). `CLAUDE.md`:
   «34 .v files, 869 Qed». Фразу можно заменить числами: «36 файлов, 882 `Qed`, аксиом нет».
7. **Стр. 143: «доказательно богаче».** По счёту — 882 `Qed` против 43 у триптиха. По содержанию заметная часть
   теорем кластера — положительность постоянных и возврат посылки (см. «Вне главы»); общие теоремы о шаге схемы,
   какие есть у тепла и переноса, в кластере отсутствуют.
8. **Стр. 150–151, 166–167: «Навье–Стокс соединяет все роли».** Тезис автора. К сведению: объекта, в котором
   диффузия стояла бы вместе с ненулевой конвекцией, в формализации нет (расхождения 1 и 2).
9. **Стр. 92–93: «есть фундамент всего, что доказано о НС».** На `energy_rate_formula` опираются сводные
   теоремы `EnergyEstimate.v` (`uniform_energy_structure`, `energy_rate_is_neg_dissipation`,
   `energy_estimate_main`), `ProcessNS.v` и `ProcessVorticity.v` — шесть мест, во всех она повторена конъюнктом
   или переписана; оценки по времени на неё не опираются (расхождение 4).
10. **Сноска 6: «сопровождается честной оценкой».** Оценка статуса задачи в `HonestAssessment.v` дана
    комментариями; теоремы файла — числовые неравенства (расхождение 8).
11. **Сноска 2: «`B_raw` — абстрактный параметр».** С 13.11.2026 это поле записи посылок, а не строка
    `Parameter`; по смыслу («произвольная функция») сказано верно.

## Вне главы (исходники)

- `GalerkinSystem.v`, комментарий `:189–192` (и та же фраза в `CLAUDE.md`, раздел History): «работу совершает
  только антисимметричная часть сопряжения; симметричная часть аннулируется в сумме тождественно» — наоборот:
  множитель $a_la_m$ симметричен, поэтому в сумме аннулируется антисимметричная по $(l,m)$ часть, и `B_coeff`
  выделяет именно её (расхождение 1).
- Шапки файлов. `GalerkinSystem.v`: «~46 Qed» при 31, «abstract Parameter B_raw» (теперь поле записи);
  `EnergyEstimate.v`: «~40 Qed» при 25; `TriadicInteraction.v`: «40 Qed, 2 Axioms (C_B)» при 37 и без аксиом;
  `AttackSynthesis.v`: «~35» при 33; `ConcentrationBound.v`: «~30» при 20. «AXIOMS: classic» в шапках
  `HonestAssessment.v`, `InvariantRegion.v`, `ResolutionRegularity.v` и «classic, L4_witness» в
  `MillenniumComplete.v` — по компилятору ни одна теорема этих файлов аксиом не берёт. Первая строка
  `MillenniumComplete.v` — «Unconditional 3D Regularity» (ниже стоит оговорка от июня 2026).
- `README.md` каталога — см. сомнительное место 6; раздел «Unconditional results» повторяет слова, разобранные в
  расхождениях 4 и 5.
- Теоремы, заключение которых не зависит от названия: `galerkin_smooth`, `galerkin_global`
  (`GalerkinSystem.v:405`, `:412`) — `modal_energy K a0 >= 0` под комментарием о глобальном существовании;
  `p4_global_existence`, `p4_smoothness`, `p4_exact_solution`, `p4_resolution_regularity`, `dns_validation`
  (`ResolutionRegularity.v:176–235`) — `0 < nu -> … -> 0 < nu`; `process_energy_decreasing` (`:215`) — возврат
  посылки; `young_preserves_degree`, `cauchy_schwarz_preserves`, `interpolation_preserves`
  (`HonestAssessment.v:196–219`) — возврат посылки; `enstrophy_bounded_in_R` (`TransientClosure.v:162`) —
  `0 <= modal_energy K a`; `region_invariant`, `invariance_by_induction` (`InvariantRegion.v:448`, `:486`),
  `step2_region_invariant` (`TransientClosure.v:49`) — одно и то же числовое неравенство; `solution_is_rational`
  (`ResolutionRegularity.v:75`) — всякое значение типа `Q` есть дробь.
- Итоговые теоремы `millennium_reading2_capstone` (`MillenniumComplete.v:415`) и `ns_galerkin_bound_chain`
  (`:105`) — положительность постоянных $A=\nu/C_B$, $\nu/(4C_B)$, $10\nu^4/C_B^4$ и неравенство
  $2H_n\le n+1$; состояния и траектории в утверждениях нет. Страница их не называет.
- `forcing_in_region` (`InvariantRegion.v:150`) не является оценкой `mode_forcing` (`TriadicInteraction.v:191`) в
  области — контрпример в `Check.v`, раздел 4б.
- Нумерация мод в файлах разная: энергия и энстрофия суммируют $k<K$ с весом $(k+1)^2$; оба `euler_step` берут
  затухание $\nu k^2$; `in_region` говорит о $k=1,\dots,K$. Два одноимённых `euler_step` имеют разные сигнатуры;
  второй (`InvariantRegion.v:463`) в теоремах не участвует.
- `foundation/HeavyWallAudit.v` (комментарии, стр. 18, 26, 125) называет оценку связи опорой всей регулярности;
  по зависимостям её используют пять объявлений `TriadicInteraction.v` (расхождение 7). Файл целиком не читался.
- `TwoMillennium.v`: строк `Qed.` 20 при 19 объявлениях `Lemma`/`Theorem` (не разбиралось).
