# Глава X.5 «Ординалы как процессы; башня сильных аксиом (ATR₀, Π¹₁) и её снятие» — заметки к ведомости (12.11.2026)

Ведомость: `part10-ch05.json` — 61 ручная запись + 8 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты ручных записей: ok — 43, mismatch-statement — 13, mismatch-price — 1,
wrong-number — 3, missing-name — 1 (с автоматическими: ok — 51).

Тринадцать записей mismatch-statement относятся к девяти местам (расхождения 1–9): четыре записи об одном
утверждении о порядке `ord_lt`, две — об одной сноске про `P4_Eliminates_Pi11.v`.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part10/ch05/`: `Check.v` (порядок на нотациях, индукция,
рекурсия), `CheckATR.v` (оператор `CB_step`), `CheckCB.v` (производная Кантора–Бендиксона вдоль `Ord`),
`CheckPi11.v` (кванторы по кодам и по функциям), `CheckInf.v` (бесконечность, сходимость, условие Рассела).
Все пять собираются; ответы `Print Assumptions` приведены по месту. В `src` и в собранной копии ничего не менялось.

Главы касаются семь файлов `src/foundation/`: `Ordinal.v`, `TransfiniteInduction.v`, `TransfiniteInductionLevel.v`,
`P4_Eliminates_ATR.v`, `P4_Eliminates_Pi11.v`, `P4_Eliminates_Infinity.v`, `P4ProhibitsImpredicative.v`. Для всех
утверждений этих файлов (24 + 12 + 6 + 17 + 15 + 10 + 7) снят `Print Assumptions`.

## Что проверить не удалось

- Отсылки к другим главам (10.1, 10.4, 10.6) не сверялись. Проверено попутно: `completed_inf_contradicts_P4` и
  `potential_compatible_with_P4` (`foundation/P4CompletedInfinity.v:64`, `:93`) существуют и закрыты; полная теорема
  Крускала в `settheory/KruskalFull.v` записана определением `kruskal_full_statement` (`:158`) и не доказана — слову
  «стена» на стр. 158 это соответствует.
- «См. §10.5.1» (стр. 62): нумерованных разделов на странице нет; по смыслу это раздел «Предупреждение о масштабе
  утверждений», но проверить ссылку нечем.
- Замечания о математике вне формализации — что производная Кантора–Бендиксона удаляет изолированные точки
  топологического пространства, что универсальная машина задаёт частичную, а не всюду определённую функцию, —
  компилятором не проверялись. Проверены их формальные следствия: вырожденность итерации `CB_step` и диагональный
  выход за любую таблицу `nat -> nat -> nat`.
- Для порядка Брауэра (расхождение 1, вариант Б) доказаны фундированность, транзитивность и перечисленные ниже
  факты; совпадение с `ord_lt` на конечных нотациях и возрастание башни `omega_tower` по этому порядку не
  доказывались.
- Пример множества, на котором итерация настоящей производной (`CB_ord`, расхождение 5) различает стадии выше
  первой, не строился.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Отношение `ord_lt` сравнивает с нотациями только конечные нотации (стр. 43–45, 122–123, 147–149; сноска 2, стр. 168)

**Было:**

> (43–45) Это даёт трансфинитную индукцию и рекурсию *по нотациям* — без аксиом. Отношение $\mathrm{ord\_lt}$
> фундировано, и из этого следуют принципы индукции вплоть до $\omega$, башни и $\varepsilon_0$.[^2]
>
> (122–123) **Что даёт.** Трансфинитная индукция/рекурсия по нотациям — `wf_ord_lt`, `transfinite_ind` (0 аксиом).
>
> (147–149) …а трансфинитная индукция по конструктивным нотациям структурна и 0-аксиомна (`wf_ord_lt`,
> `transfinite_ind`).

**Проверка.** Определение (`src/foundation/Ordinal.v:64`):

```coq
Inductive ord_lt : Ord -> Ord -> Prop :=
  | lt_zero_succ : forall a, ord_lt OZero (OSucc a)
  | lt_succ_mono : forall a b, ord_lt a b -> ord_lt (OSucc a) (OSucc b)
  | lt_to_lim : forall a f n, ord_lt a (f n) -> ord_lt a (OLim f)
  | lt_succ_to_lim : forall a f, (exists n, ord_lt a (f n)) -> ord_lt (OSucc a) (OLim f).
```

`wf_ord_lt : well_founded ord_lt` (`TransfiniteInduction.v:40`) и
`transfinite_ind : forall P, (forall a, (forall b, ord_lt b a -> P b) -> P a) -> forall a, P a` (`:62`) — оба
Closed under the global context; цена на странице названа верно.

Ни один конструктор не ставит слева предельную нотацию. В пробном файле (`Check.v`) доказано, все — Closed under
the global context:

```coq
Lemma ord_lt_left_numeral : forall b a, ord_lt a b -> exists n, a = nat_to_ord n.
Theorem lim_not_lt : forall f x, ~ ord_lt (OLim f) x.
Corollary omega_not_lt_succ_omega : ~ ord_lt omega (OSucc omega).
Corollary omega_not_lt_epsilon_0 : ~ ord_lt omega epsilon_0.
Corollary tower_stage_not_lt_epsilon_0 : forall n, ~ ord_lt (omega_tower n) epsilon_0.
Theorem below_epsilon_0_iff_below_omega : forall x, ord_lt x epsilon_0 <-> ord_lt x omega.
Lemma one_lt_lim_const_one : ord_lt (OSucc OZero) (OLim (fun _ => OSucc OZero)).
```

То есть: ниже любой нотации по `ord_lt` лежат только конечные нотации `nat_to_ord n`; `omega` не ниже
`OSucc omega` и не ниже `epsilon_0`; ни одна ступень башни не ниже `epsilon_0`; ниже `epsilon_0` лежит ровно то
же, что ниже `omega`. Последняя лемма показывает, что отношение не согласовано и с чтением `OLim` как верхней
грани: единица оказывается ниже предела постоянной последовательности единиц. Это отмечает и сам репозиторий —
`src/foundation/LevelComparison.v:10–11`: «General ord_lt a (OSucc a) for limit ordinals is NOT provable from the
current ord_lt constructors».

«Принципы индукции вплоть до $\omega$ … и $\varepsilon_0$» — леммы `transfinite_ind_omega` (`:125`) и
`transfinite_ind_epsilon_0` (`:133`): частные случаи `transfinite_ind` при `a = omega` и `a = epsilon_0`.

**В чём расхождение.** Теоремы верны, но отношение, по которому идёт индукция, не является порядком на
ординальных нотациях: в предельном шаге предположение индукции охватывает конечные нотации, а не стадии предела,
и индукция «до $\varepsilon_0$» по нему не отличается от индукции «до $\omega$». Через пределы в формализации
ведёт другой принцип — структурная индукция `Ord_ind`, порождаемая определением типа `Ord` (в предельном шаге
предположение дано для всех стадий `f n`); ею и доказана `wf_ord_lt`.

**(а) Довести формализацию.** Возможно, без допущений. Проверены два варианта (`Check.v`); все перечисленные
утверждения — Closed under the global context.

*Вариант А — структурный порядок* (тот, по которому идёт `Fixpoint`):

```coq
Inductive ord_sub : Ord -> Ord -> Prop :=
  | sub_succ : forall a, ord_sub a (OSucc a)
  | sub_lim  : forall f n, ord_sub (f n) (OLim f).

Lemma wf_ord_sub : well_founded ord_sub.
Proof.
  intro a. induction a as [| a IH | f IH]; constructor; intros b Hb; inversion Hb; subst.
  - exact IH.
  - apply IH.
Qed.

Definition ord_below : Ord -> Ord -> Prop := clos_trans Ord ord_sub.

Theorem wf_ord_below : well_founded ord_below.
Proof. unfold ord_below. apply wf_clos_trans. exact wf_ord_sub. Qed.

Theorem structural_transfinite_ind : forall P : Ord -> Prop,
  (forall a, (forall b, ord_below b a -> P b) -> P a) -> forall a, P a.
Proof. intros P H. apply (well_founded_ind wf_ord_below). exact H. Qed.

Lemma below_succ : forall a, ord_below a (OSucc a).
Lemma stage_below_lim : forall f n, ord_below (f n) (OLim f).
Lemma nat_below_omega : forall n, ord_below (nat_to_ord n) omega.
Lemma tower_below_epsilon_0 : forall n, ord_below (omega_tower n) epsilon_0.
Lemma omega_below_epsilon_0 : ord_below omega epsilon_0.

Theorem induction_below_epsilon_0 : forall P : Ord -> Prop,
  (forall a, ord_below a epsilon_0 -> (forall b, ord_below b a -> P b) -> P a) ->
  forall a, ord_below a epsilon_0 -> P a.
```

*Вариант Б — порядок Брауэра* (`OLim f` — верхняя грань стадий):

```coq
Inductive ole : Ord -> Ord -> Prop :=
  | ole_zero  : forall b, ole OZero b
  | ole_succ  : forall a b, ole a b -> ole (OSucc a) (OSucc b)
  | ole_stage : forall a f n, ole a (f n) -> ole a (OLim f)
  | ole_lim   : forall f b, (forall n, ole (f n) b) -> ole (OLim f) b.

Definition olt (a b : Ord) : Prop := ole (OSucc a) b.

Lemma ole_refl : forall a, ole a a.
Theorem ole_trans : forall a b, ole a b -> forall c, ole b c -> ole a c.
Theorem wf_olt : well_founded olt.
Theorem brouwer_transfinite_ind : forall P : Ord -> Prop,
  (forall a, (forall b, olt b a -> P b) -> P a) -> forall a, P a.
Lemma olt_succ : forall a, olt a (OSucc a).
Lemma ole_stage_lim : forall f n, ole (f n) (OLim f).
Lemma olt_trans : forall a b c, olt a b -> olt b c -> olt a c.
Lemma olt_nat_omega : forall n, olt (nat_to_ord n) omega.
Theorem olt_omega_epsilon_0 : olt omega epsilon_0.
```

Доказательство фундированности — индукцией по `b` с леммой «всё, что не больше доступного, доступно»:

```coq
Lemma acc_olt_down : forall b, Acc olt b -> forall a, ole a b -> Acc olt a.
Proof.
  intros b Hb a Hab. constructor. intros c Hc.
  apply (Acc_inv Hb). unfold olt in *. exact (ole_trans _ _ Hc _ Hab).
Qed.

Theorem wf_olt : well_founded olt.
Proof.
  intro b. induction b as [| b IH | f IH]; constructor; intros c Hc; unfold olt in Hc.
  - inversion Hc.
  - inversion Hc; subst. apply (acc_olt_down b IH). assumption.
  - inversion Hc as [| | a0 f0 n0 Hle Heq1 Heq2 |]; subst.
    apply (Acc_inv (IH n0)). exact Hle.
Qed.
```

Полный текст обоих вариантов — в `Check.v`. Порядок Брауэра с `ord_lt` не совпадает: пример
`one_lt_lim_const_one` в нём неверен (`olt_differs_from_ord_lt`, Closed). На `ord_lt` стоит
`src/foundation/LevelComparison.v` (33 вхождения: леммы о конечных нотациях и две общие — `ord_lt_irrefl`,
`ord_lt_add_r`); новый порядок проще добавить рядом, не трогая старого. Какой из двух порядков взять — решает автор: вариант А короче и буквально соответствует слову
«структурна», вариант Б есть порядок ординалов в обычном смысле.

После добавления слова стр. 43–45 верны с заменой имён в сноске 2: `wf_ord_below`,
`structural_transfinite_ind`, `induction_below_epsilon_0` (или `wf_olt`, `brouwer_transfinite_ind`).

**(б) Поправить слова** (если формализацию не трогать):

> (43–47) Это даёт индукцию и рекурсию *по нотациям* — без аксиом. Основной принцип — структурная индукция по
> типу `Ord`: свойство, верное для нуля, сохраняемое успешником и переходящее от всех стадий $f(n)$ к пределу
> $\mathrm{OLim} f$, верно для всякой нотации; рекурсия по нотациям записывается как `Fixpoint`. Отдельно доказаны
> фундированность отношения $\mathrm{ord\_lt}$ и индукция по нему.[^2] Это отношение сравнивает с нотацией только
> конечные нотации (предельная нотация по нему не лежит ниже никакой другой), поэтому через пределы ведёт
> структурная индукция. Подчеркнём область: это индукция/рекурсия по *конструктивным ординальным нотациям* `Ord`,
> а не по произвольному завершённому вполне-порядку.
>
> (122–123) **Что даёт.** Индукция и рекурсия по нотациям — структурные (`Ord_ind`, `Fixpoint`); фундированность
> `ord_lt` и индукция по нему — `wf_ord_lt`, `transfinite_ind` (0 аксиом).
>
> (147–149) …а индукция по конструктивным нотациям структурна и 0-аксиомна (принцип `Ord_ind`; для отношения
> `ord_lt` — `wf_ord_lt`, `transfinite_ind`).
>
> (сноска 2) `TransfiniteInduction.v`: `wf_ord_lt` (`well_founded ord_lt`), `transfinite_ind` — индукция по
> `ord_lt`; её частные случаи — `transfinite_ind_omega`, `transfinite_ind_epsilon_0`. По `ord_lt` ниже любой
> нотации лежат только конечные нотации, поэтому в предельном шаге предположение индукции охватывает их, а не
> стадии предела; индукцию через пределы даёт структурный принцип `Ord_ind`. **0 аксиом** (сверено
> `Print Assumptions`: …

(продолжение сноски — по расхождениям 2 и 3).

## Расхождение 2. `transfinite_rec` не содержит уравнения рекурсии (стр. 43, 122; сноска 2, стр. 168)

**Было:** «`TransfiniteInduction.v`: `wf_ord_lt` (`well_founded ord_lt`), `transfinite_ind`, `transfinite_rec`;
`omega_tower_induction`. **0 аксиом**»

**Проверка.** `src/foundation/TransfiniteInduction.v:74`:

```coq
Theorem transfinite_rec : forall (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_lt b a -> T) -> T),
  forall a : Ord, T.
Proof.
  intros T step a.
  exact (well_founded_induction_type wf_ord_lt (fun _ => T) step a).
Qed.
```

Closed under the global context. Утверждение говорит только, что по `step` получается значение типа `T`;
равенства, связывающего результат с `step`, в нём нет, а доказательство закрыто `Qed` и развернуть его нельзя.
Тот же тип населён без фундированности — достаточно применить `step` к нулю, ниже которого ничего нет
(`Check.v`, Closed under the global context):

```coq
Lemma nothing_below_zero : forall b, ord_lt b OZero -> False.
Proof. intros b H. inversion H. Qed.

Definition transfinite_rec_without_wf : forall (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_lt b a -> T) -> T),
  forall a : Ord, T :=
  fun T step _ => step OZero (fun b H => False_rect T (nothing_below_zero b H)).
```

**В чём расхождение.** Теорема с именем «трансфинитная рекурсия» не утверждает ничего о рекурсии. Рекурсия по
нотациям в формализации есть, но в другом виде — как `Fixpoint` (`ord_add`, `ord_mul`, `ord_exp`, `iterate_pred`).

**(а) Довести формализацию.** Возможно: определить рекурсию через `Fix` и доказать уравнение неподвижной точки.
Набросок проверен (`Check.v`, для порядка `ord_below` расхождения 1; для `ord_lt` и `olt` текст тот же), Closed
under the global context:

```coq
Definition ord_rec (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_below b a -> T) -> T) : Ord -> T :=
  Fix wf_ord_below (fun _ => T) step.

Theorem ord_rec_eq : forall (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_below b a -> T) -> T),
  (forall a (f g : forall b, ord_below b a -> T),
      (forall b p, f b p = g b p) -> step a f = step a g) ->
  forall a, ord_rec T step a = step a (fun b _ => ord_rec T step b).
Proof.
  intros T step Hext a. unfold ord_rec.
  exact (Fix_eq wf_ord_below (fun _ => T) step Hext a).
Qed.
```

**(б) Поправить слова** (в сноске 2): имя `transfinite_rec` из перечня снять и добавить фразу:

> Рекурсия по нотациям записывается как `Fixpoint` (`ord_add`, `ord_mul`, `ord_exp` в `Ordinal.v`); теорема
> `transfinite_rec` утверждает лишь, что по шагу рекурсии получается значение, — уравнения рекурсии в ней нет.

## Расхождение 3. `omega_tower_induction` — индукция по натуральным числам (стр. 44–45; сноска 2, стр. 168)

**Было:** «…принципы индукции вплоть до $\omega$, башни и $\varepsilon_0$.[^2]»; в сноске — «`omega_tower_induction`».

**Проверка.** `src/foundation/TransfiniteInduction.v:96`:

```coq
Lemma omega_tower_induction : forall (P : nat -> Prop),
  P O -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof. intros P H0 HS. exact (nat_ind P H0 HS). Qed.
```

Closed under the global context. Утверждение дословно совпадает с `nat_induction_from_transfinite` (`:87`) и с
`nat_ind`; `omega_tower` в него не входит.

**В чём расхождение.** Индукции «по башне» в формализации нет: под этим именем стоит индукция по ℕ.

**(а) Довести формализацию.** Возможно. Индукция по ступеням башни и индукция ниже `epsilon_0` (`Check.v`, обе —
Closed under the global context):

```coq
Theorem tower_induction : forall P : Ord -> Prop,
  P omega -> (forall n, P (omega_tower n) -> P (omega_tower (S n))) ->
  forall n, P (omega_tower n).
Proof. intros P H0 HS n. induction n as [| n IH]; [exact H0 | exact (HS n IH)]. Qed.
```

и `induction_below_epsilon_0` из расхождения 1. Первая — та же индукция по номеру ступени, но сформулированная о
нотациях башни; вторая требует порядка, по которому ступени лежат ниже `epsilon_0`.

**(б) Поправить слова.** Если абзац стр. 43–47 заменён по расхождению 1, слово «башни» из него уже ушло; иначе:

> (44–45) …и из этого следует индукция по нему; её частные случаи записаны для $\omega$ и $\varepsilon_0$.[^2]

В обоих случаях в сноске 2:

> …`omega_tower_induction` — индукция по номеру ступени башни, то есть по $ℕ$.

## Расхождение 4. «На каждой стадии актуально лишь конечное» верно только для ω (стр. 39–41)

**Было:** «На каждой стадии $n$ актуально лишь конечное ($\mathrm{OSucc}^n(\mathrm{OZero})$); сам ординал — не
завершённый трансфинитный объект, а позиция в фундированном процессе.»

**Проверка.** Фраза идёт сразу за определением $\varepsilon_0$. Для `omega := OLim nat_to_ord` стадия $n$ —
`nat_to_ord n`, то есть $\mathrm{OSucc}^n(\mathrm{OZero})$. Для `epsilon_0 := OLim omega_tower` стадия $n$ —
`omega_tower n`: `omega_tower 0 = omega` (`Ordinal.v:209`), и при каждом $n$ это предельная нотация (`Check.v`,
Closed under the global context):

```coq
Lemma tower_stage_is_limit : forall n, exists g, omega_tower n = OLim g.
```

Для произвольного `OLim f` стадия `f n` — любая нотация.

**В чём расхождение.** Свойство одного примера записано как общее; для второго примера той же фразы оно неверно.

**(а) Довести формализацию.** Не требуется: формализация верна, расходятся слова.

**(б) Поправить слова:**

> На каждой стадии $n$ предъявлена одна нотация: для $\omega$ — конечная, $\mathrm{OSucc}^n(\mathrm{OZero})$; для
> $\varepsilon_0$ — ступень башни, сама заданная как предел процесса. Сам ординал — не завершённый трансфинитный
> объект, а позиция в фундированном процессе.

Та же оговорка относится к строке таблицы на стр. 120 («конечная нотация/код/стадия на каждом шаге»).

## Расхождение 5. `CB_transfinite` итерирует не производную Кантора–Бендиксона (сноска 3, стр. 169)

**Было:** «`P4_Eliminates_ATR.v`: `CB_transfinite` — трансфинитная итерация (производная Кантора–Бендиксона) как
`Fixpoint` на `Ord`;»

**Проверка.** `src/foundation/P4_Eliminates_ATR.v:36`, `:43`:

```coq
Definition CB_step (S : nat -> Prop) : nat -> Prop :=
  fun n => S n /\ exists m, m <> n /\ S m /\ (m < n + 2 /\ n < m + 2)%nat.

Fixpoint CB_transfinite (S : nat -> Prop) (alpha : Ord) : nat -> Prop :=
  match alpha with
  | OZero => S
  | OSucc a => CB_step (CB_transfinite S a)
  | OLim f => fun n => forall k, CB_transfinite S (f k) n
  end.
```

`CB_step` оставляет число $n$, если в множестве есть сосед $n-1$ или $n+1$. Сосед оставленной точки сам имеет
соседа, поэтому оператор идемпотентен, и итерация стабилизируется на первом шаге (`CheckATR.v`, все — Closed under
the global context):

```coq
Lemma CB_step_idempotent : forall (X : nat -> Prop) n, CB_step (CB_step X) n <-> CB_step X n.
Theorem CB_transfinite_succ_stage : forall (X : nat -> Prop) (a : Ord) n,
  CB_transfinite X (OSucc a) n <-> CB_step X n.
Theorem CB_transfinite_omega : forall (X : nat -> Prop) n,
  CB_transfinite X omega n <-> CB_step X n.
```

**В чём расхождение.** Оператор — модельный («есть сосед на расстоянии 1» на подмножествах ℕ), а не производная
Кантора–Бендиксона; его итерация вдоль нотаций на всех стадиях-успешниках и на стадии ω даёт одно и то же
множество. Форма рекурсии (ноль, успешник, предел) показана верно; содержательного трансфинитного процесса в
примере нет.

**(а) Довести формализацию.** Возможно. Настоящая производная — множество точек накопления — определена в
`src/settheory/CantorBendixsonFull.v:37` (`CB_deriv` на подмножествах ℚ), но итерируется там только по натуральным
шагам; `CB_ord_step` (`:393`) рекурсивным не является (на `OSucc _` даёт одну производную независимо от
предшественника). Итерация вдоль `Ord` структурной рекурсией проверена (`CheckCB.v`, Closed under the global
context):

```coq
Fixpoint CB_ord (X : PointSet) (a : Ord) : PointSet :=
  match a with
  | OZero => X
  | OSucc b => CB_deriv (CB_ord X b)
  | OLim f => fun x => forall k, CB_ord X (f k) x
  end.

Lemma CB_ord_subset : forall X a x, CB_ord X a x -> X x.
Lemma CB_ord_nat : forall X n, CB_ord X (nat_to_ord n) = CB_iter X n.
Theorem CB_ord_omega : forall X x, CB_ord X omega x <-> CB_omega X x.
Lemma CB_ord_omega_succ : forall X, CB_ord X (OSucc omega) = CB_deriv (CB_ord X omega).
```

Здесь тип `Ord` — общий с `Ordinal.v`, а не копия. Чтобы пример был содержательным, к нему нужно множество, у
которого стадии выше первой различны; оно не строилось.

**(б) Поправить слова:**

> [^3]: `P4_Eliminates_ATR.v`: `iterate_pred` — итерация произвольного оператора на подмножествах $ℕ$ вдоль
> нотации как `Fixpoint` на `Ord`; `CB_transfinite` — тот же `Fixpoint` для модельного оператора `CB_step` (точка
> остаётся, если у неё есть сосед на расстоянии 1), дискретного подобия производной Кантора–Бендиксона;
> `P4_eliminates_ATR0` фиксирует zero/successor-уравнения рекурсии (limit-стадия задана самим `Fixpoint`). 17 Qed,
> 0 аксиом (сверено `Print Assumptions`: Closed).

## Расхождение 6. `P4_eliminates_Pi11` раскрывает определение; `eval_program` — объявление без свойств (сноска 4, стр. 170)

**Было:** «`P4_Eliminates_Pi11.v`: `Program := nat`, `P4_forall_functions` (квантор по функциям через коды), итог —
`P4_eliminates_Pi11`. По `Print Assumptions` — 0 логических аксиом, но зависит от `eval_program` (`Parameter` —
вычислительный примитив универсальной машины); это и есть P4-кодовая переинтерпретация, а не построение
пространства программ изнутри.»

**Проверка.** `src/foundation/P4_Eliminates_Pi11.v:26–36`, `:157`:

```coq
Definition Program := nat.
Parameter eval_program : Program -> nat -> nat.
Definition P4_forall_functions (phi : (nat -> nat) -> nat -> Prop) (n : nat) : Prop :=
  forall c : Program, phi (eval_program c) n.

Theorem P4_eliminates_Pi11 :
  forall phi n, P4_forall_functions phi n <-> (forall c : nat, phi (eval_program c) n).
Proof. intros. apply pi11_to_arithmetic. Qed.
```

`Print Assumptions P4_eliminates_Pi11`: `Axioms: P4_Eliminates_Pi11.eval_program : P4_Eliminates_Pi11.Program ->
nat -> nat`. Цена на странице названа верно (стр. 125 и 170).

О формулировке. Левая и правая стороны равносильности совпадают после раскрытия определения: их равенство
закрывается `reflexivity` (`CheckPi11.v`). Квантора по функциям `nat -> nat` в теореме нет. О `eval_program`
формализация не утверждает ничего, кроме типа; слова «вычислительный примитив универсальной машины» повторяют
комментарий файла (`:22–25`). Для любой всюду определённой таблицы найдётся функция вне её, и квантор по кодам
строго слабее квантора по функциям (`CheckPi11.v`; первые две — Closed under the global context, третья зависит
только от `eval_program`):

```coq
Theorem diagonal_escapes_codes : forall ev : nat -> nat -> nat,
  exists f : nat -> nat, forall c, exists n, f n <> ev c n.
Proof.
  intro ev. exists (fun n => S (ev n n)). intro c. exists c.
  apply Nat.neq_succ_diag_l.
Qed.

Theorem codes_reading_is_weaker : forall ev : nat -> nat -> nat,
  exists phi : (nat -> nat) -> nat -> Prop,
    (forall n c, phi (ev c) n) /\ ~ (forall n f, phi f n).

Theorem P4_forall_is_not_forall :
  exists phi : (nat -> nat) -> nat -> Prop,
    (forall n, P4_forall_functions phi n) /\ ~ (forall n f, phi f n).
```

**В чём расхождение.** Итоговая теорема не связывает квантор по функциям с квантором по кодам — она
переписывает определение. Само прочтение задано определением `P4_forall_functions`; основной текст главы (стр.
82–89) честно называет его выбором онтологии. Сноска же подаёт теорему как итог и описывает `eval_program`
словами, которых формализация не подтверждает: всюду определённая таблица универсальной быть не может.

**(а) Довести формализацию.** До равносильности «$\forall f \Leftrightarrow \forall c$» — нельзя: она неверна для
любой таблицы (`codes_reading_is_weaker`). Честная форма прочтения «квантор по функциям, *заданным кодами*»
(стр. 86–87) доказывается, причём без `Parameter` — для произвольной таблицы (`CheckPi11.v`; первая — Closed under
the global context):

```coq
Theorem forall_codes_iff_forall_coded : forall (ev : nat -> nat -> nat)
  (phi : (nat -> nat) -> nat -> Prop) (n : nat),
  (forall c : nat, phi (ev c) n) <->
  (forall f : nat -> nat, (exists c : nat, f = ev c) -> phi f n).
Proof.
  intros ev phi n. split.
  - intros H f [c Hc]. subst. apply H.
  - intros H c. apply H. exists c. reflexivity.
Qed.

Theorem P4_forall_functions_coded : forall phi n,
  P4_forall_functions phi n <->
  (forall f : nat -> nat, (exists c : Program, f = eval_program c) -> phi f n).
```

Если в файле заменить `Parameter eval_program` переменной раздела (`Section` / `Variable ev`), все его теоремы
станут утверждениями «для любой таблицы» и строка `eval_program` из вывода компилятора уйдёт. Так уже сделано в
`src/cs/HaltingRoleLimit.v` (шапка, строки 19–21: «a TOTAL universal `eval_program` (no halting). Here we ADD the
partiality/halting dimension it omits … discharged as section hypotheses, not a Parameter»).

**(б) Поправить слова:**

> [^4]: `P4_Eliminates_Pi11.v`: `Program := nat`; `P4_forall_functions` — квантор по кодам,
> `forall c : Program, phi (eval_program c) n`; это определение и есть переинтерпретация. Теорема
> `P4_eliminates_Pi11` раскрывает определение и квантора по функциям не содержит. `eval_program` — `Parameter`
> типа `Program -> nat -> nat` без уточняющих свойств: таблица, сопоставляющая коду функцию; по
> `Print Assumptions` итог зависит только от него, логических аксиом нет. Утверждения «всякая функция имеет код» в
> файле нет, и для всюду определённой таблицы оно неверно (диагональная функция $n \mapsto \mathrm{ev}(n,n)+1$ в
> таблицу не входит): квантор по кодам — выбор области, а не равносильная замена.

## Расхождение 7. `P4_eliminates_Infinity` — четыре факта, не связанные с P4 (сноска 5, стр. 171)

**Было:** «`P4_Eliminates_Infinity.v`: `converges` (сходимость приближений), итог — `P4_eliminates_Infinity`.»

**Проверка.** `src/foundation/P4_Eliminates_Infinity.v:79`:

```coq
Theorem P4_eliminates_Infinity :
  (forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n) /\
  (forall n : nat, (n < S n)%nat) /\
  factorial 5 = 120 /\
  partial_sum (fun n => n) 3 = 6.
```

Closed under the global context. Члены: индукция по ℕ (`nat_ind`), $n < n+1$, $5! = 120$, $0+1+2+3 = 6$.
Определение `converges` в теорему не входит.

**В чём расхождение.** Теорема-итог не содержит ни P4, ни завершённого множества, ни сходимости; все четыре
факта верны при любой трактовке бесконечности.

**(а) Довести формализацию.** Возможно. Содержательная форма тезиса «бесконечность — процесс, а не завершённый
объект» в терминах файла: никакая конечная стадия не исчерпывает натуральных чисел. Набросок проверен
(`CheckInf.v`, Closed under the global context); он опирается на лемму `finite_list_bounded` (`:65`) того же файла:

```coq
Theorem no_finite_stage_exhausts_nat : forall l : list nat, exists n, ~ In n l.
Proof.
  intro l. destruct (finite_list_bounded l) as [b Hb].
  exists (S b). intro Hin. specialize (Hb (S b) Hin). lia.
Qed.

Theorem infinity_as_process :
  (forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n) /\
  (forall l : list nat, exists n, ~ In n l) /\
  (forall n : nat, exists m, n < m).
```

Запрет завершённой формы доказан в соседнем файле — `completed_inf_contradicts_P4`
(`foundation/P4CompletedInfinity.v:64`); его можно включить в итог ссылкой.

**(б) Поправить слова:**

> [^5]: `P4_Eliminates_Infinity.v`: индукция как встроенное правило (`nat_induction_works`), рекурсия как
> `Fixpoint` (`factorial`, `partial_sum`), ограниченность всякого конечного списка (`finite_list_bounded`);
> итоговая теорема `P4_eliminates_Infinity` собирает четыре факта — индукцию по $ℕ$, $n<n+1$, $5!=120$,
> $0+1+2+3=6$. 10 Qed, 0 аксиом. Ср. 10.4: потенциальная бесконечность с P4 совместима, завершённая — нет.

## Расхождение 8. По определению `converges` предел не единствен (сноска 5, стр. 171)

**Было:** «`converges` (сходимость приближений)»

**Проверка.** `src/foundation/P4_Eliminates_Infinity.v:28`:

```coq
Definition converges (a : nat -> nat) (L : nat) : Prop :=
  forall eps, (eps > 0)%nat -> exists N, forall n, (n >= N)%nat ->
    (if (a n <=? L)%nat then L - a n else a n - L) <= eps.
```

`eps` — натуральное, неравенство нестрогое; наименьшее допустимое `eps` равно 1, так что условие означает «с
некоторого места $|a_n - L| \le 1$». Проверено (`CheckInf.v`, Closed under the global context):

```coq
Lemma converges_not_unique :
  converges (fun _ => 1) 0 /\ converges (fun _ => 1) 1 /\ converges (fun _ => 1) 2.
Proof.
  split; [| split]; intros eps Heps; exists 0; intros n _; simpl; lia.
Qed.
```

О `converges` в файле доказана одна лемма — `const_converges` (`:32`). В других файлах это определение не
применяется.

**В чём расхождение.** Определение слабее сходимости: постоянная последовательность «сходится» к трём разным
числам.

**(а) Довести формализацию.** Возможно: заменить `<=` на `<`. Тогда сходимость в ℕ равносильна стабилизации, и
предел единствен (`CheckInf.v`, Closed under the global context):

```coq
Definition converges_strict (a : nat -> nat) (L : nat) : Prop :=
  forall eps, (eps > 0)%nat -> exists N, forall n, (n >= N)%nat ->
    (if (a n <=? L)%nat then L - a n else a n - L) < eps.

Lemma converges_strict_iff : forall a L,
  converges_strict a L <-> exists N, forall n, n >= N -> a n = L.
Lemma converges_strict_unique : forall a L1 L2,
  converges_strict a L1 -> converges_strict a L2 -> L1 = L2.
```

Доказательство `const_converges` при такой замене проходит без изменений (разность равна нулю). Сходимость
рациональных приближений в проекте выражается свойством Коши `is_Cauchy` (`src/process/ProcessCore.v:68`); здесь
уместна ссылка на него.

**(б) Поправить слова:** упоминание `converges` из сноски снять (текст сноски — в расхождении 7) либо оговорить:
«определение `converges` записано для последовательностей натуральных чисел и в теоремах файла не участвует».
Слова основного текста «в духе сходящихся приближений» (стр. 99) на это определение не опираются и могут остаться.

## Расхождение 9. В `P4ProhibitsImpredicative.v` нет теоремы о тотальности или об импредикативном определении (сноска 6, стр. 172)

**Было:** «`P4ProhibitsImpredicative.v`: P1${}+{}$P4 исключают завершённую тотальность, по которой идёт
импредикативное определение.»

**Проверка.** Все семь утверждений файла — Closed under the global context. Содержание:

- `P1_blocks_russell` (`:56`): если `forall x, ~ member x x`, то `~ member x x` для всякого `x` — заключение
  повторяет посылку;
- `russell_contradiction_without_P1` (`:69`): `(forall x, member x r <-> ~ member x x) -> False` для любого
  отношения `member` на `nat` — диагональ Рассела; посылок о P1 и P4 в теореме нет;
- `nat_is_inductive` (`:92`), `nat_staged_bounded` (`:102`), `nat_eventually_actual` (`:109`) — о стадиях
  `n <= stage`;
- `P4_dissolves_russell` (`:124`), `p4_impredicative_synthesis` (`:144`) — конъюнкции перечисленного.

Определения `NatTotality` (`:33`) и `impredicative_prop` (`:41`) ни в одну теорему не входят. `NatTotality` —
`forall P : nat -> Prop, exists n : nat, True` — верно при любом `P` (проверено в `CheckInf.v`).

**В чём расхождение.** Сноска описывает теорему, которой в файле нет. Доказано другое: множество Рассела не
образуется ни при каком отношении принадлежности — без обращения к P1 и P4. Слова основного текста (стр. 99–101,
153: «при P1 и P4 оно не формируется») этому не противоречат, но роль P1 и P4 теоремами файла не показана.

**(а) Довести формализацию.** Возможно. Точная форма тезиса «импредикативное определение не формируется»:
множество, заданное условием Рассела на области $D$, само в $D$ не лежит; взятое по стадии — выходит за стадию,
взятое по всей тотальности — не существует. Набросок проверен (`CheckInf.v`, все — Closed under the global
context); вторая теорема использует стадии самого файла (`nat_staged_actual`):

```coq
Theorem russell_outside_its_domain : forall (A : Type) (D : A -> Prop)
  (member : A -> A -> Prop) (r : A),
  (forall x, D x -> (member x r <-> ~ member x x)) -> ~ D r.
Proof.
  intros A D member r H Hr. destruct (H r Hr) as [H1 H2].
  assert (Hn : ~ member r r) by (intro Hm; exact (H1 Hm Hm)).
  exact (Hn (H2 Hn)).
Qed.

Corollary russell_escapes_stage : forall (member : nat -> nat -> Prop) (r s : nat),
  (forall x, nat_staged_actual s x -> (member x r <-> ~ member x x)) ->
  ~ nat_staged_actual s r.

Corollary russell_over_totality : forall (member : nat -> nat -> Prop) (r : nat),
  (forall x, member x r <-> ~ member x x) -> False.
```

С этими теоремами слова сноски получают опору: определение по стадии законно и выводит за стадию (P4),
определение по тотальности, включающей определяемое, не образуется.

**(б) Поправить слова:**

> [^6]: `P4ProhibitsImpredicative.v`: множество Рассела не образуется ни при каком отношении принадлежности
> (`russell_contradiction_without_P1` — диагональ); при иррефлексивной принадлежности условию Рассела
> удовлетворяет всё (`P1_blocks_russell`); поэтапная актуальность $ℕ$ ограничена на каждой стадии
> (`nat_staged_bounded`). 7 Qed, 0 аксиом.

## Расхождение 10 (цена). Функциональная экстенсиональность в `Ordinal.v` (сноска 1, стр. 167)

**Было:** «Арифметика ($+,\cdot,{}^\wedge$) — структурной рекурсией, но часть её лемм опирается на функциональную
экстенсиональность.»

**Проверка.** После правки формализации 12.11 (коммит 8f834c6) `Ordinal.v` подключает только `Lia`, `ZArith`,
`List`. Два тождества, проходящие через предел, сформулированы с точностью до постадийного равенства `ord_eq`
(`:86`): `ord_add_zero_l : forall a, ord_eq (ord_add OZero a) a` (`:120`),
`ord_mul_one_r : forall a, ord_eq (ord_mul a (OSucc OZero)) a` (`:131`). `Print Assumptions` для всех 24 лемм
файла — Closed under the global context.

**(б) Стало:**

> Арифметика ($+,\cdot,{}^\wedge$) — структурной рекурсией; два тождества, проходящие через предел
> (`ord_add_zero_l`, `ord_mul_one_r`), записаны с точностью до постадийного равенства `ord_eq`, и функциональная
> экстенсиональность не привлекается: все 24 леммы файла закрыты.

## Расхождение 11 (числа)

- **Стр. 169:** «15 Qed, 0 аксиом» — в `P4_Eliminates_ATR.v` 17 `Qed`. Стало: «17 Qed, 0 аксиом». Из 17
  утверждений различных 13: `iterate_zero`, `ATR_pattern`, `iterate_identity` совпадают дословно; дословно
  совпадают `CB_trans_decreasing` и `succ_stage_monotone`; `CB_trans_lim_forward` и `lim_below_all` совпадают с
  точностью до порядка кванторов.
- **Стр. 171:** «12 Qed, 0 аксиом» — в `P4_Eliminates_Infinity.v` 10 `Qed`. Стало: «10 Qed, 0 аксиом».
- **Стр. 172:** «10 Qed, 0 аксиом» — в `P4ProhibitsImpredicative.v` 7 `Qed`. Стало: «7 Qed, 0 аксиом».

Во всех трёх случаях шапка файла называет действительное число; слова «0 аксиом» верны (все утверждения трёх
файлов — Closed under the global context).

## Расхождение 12 (имена). Имя файла в перечне теорем (стр. 125)

**Было:** «(`P4_eliminates_ATR0`, `P4_eliminates_Pi11`, `P4_eliminates_Infinity`, `P4ProhibitsImpredicative`; …)»

**Проверка.** Первые три имени — теоремы; `P4ProhibitsImpredicative` — имя файла (модуля), теоремы с таким именем
нет. Итоговые теоремы файла — `P4_dissolves_russell` (`:124`) и `p4_impredicative_synthesis` (`:144`).

**(б) Стало:** «(`P4_eliminates_ATR0`, `P4_eliminates_Pi11`, `P4_eliminates_Infinity`, `P4_dissolves_russell`; …)».

## Сомнительные места (не расхождения)

- **Стр. 37–39, `epsilon_0`.** Имя дано определением (`OLim omega_tower`). О нём доказана одна лемма —
  `epsilon_0_is_limit` (не является успешником; по различию конструкторов). Равенство $\omega^{\varepsilon_0} =
  \varepsilon_0$ и минимальность не формулируются; по отношению `ord_lt` у `epsilon_0` и `omega` одни и те же
  предшественники (расхождение 1). Слова главы читаются как определение и с формализацией согласны.
- **Стр. 57–60 и 169, два типа `Ord`.** `P4_Eliminates_ATR.v` объявляет собственную копию `Ord`, `nat_to_ord`,
  `omega` (`:21–29`, «replicated from Ordinal.v for standalone compilation»). Теоремы `TransfiniteInduction.v` к
  типу, на котором определены `iterate_pred` и `CB_transfinite`, не применимы: это разные типы.
- **Стр. 168, `level_strong_induction`.** Тип `Level` — `L1 | LS Level` (`TheoryOfSystems_Core_ERR.v:59`), его
  ранг `level_depth` — натуральное число; теорема есть сильная индукция по конечным уровням. Слова «индукция по
  уровневой иерархии» точны; к трансфинитной индукции она не относится.
- **Стр. 150–153, имена теорем как указатели.** «ATR₀ — структурная рекурсия по нотациям (`P4_eliminates_ATR0`);
  Π¹₁ — второй порядок как первый по кодам (`P4_eliminates_Pi11`); Бесконечность — схема процесса
  (`P4_eliminates_Infinity`)»: во всех трёх случаях содержание несут определения (`iterate_pred`,
  `P4_forall_functions`) и встроенная индукция, а названные теоремы раскрывают определения или собирают простые
  факты (расхождения 6, 7). В ведомости эти строки записаны как ok с отсылкой к сноскам.
- **Стр. 82–89, «отождествление функции с программным кодом».** Глава называет его выбором онтологии, и
  расхождения здесь нет. В формализации отождествление не записано и записано быть не может: для любой таблицы
  `nat -> nat -> nat` есть функция вне её (расхождение 6). Формально принято определение квантора по кодам;
  уместно сказать об этом в тексте одной фразой.
- **Стр. 99–101 и 153, «при P1 и P4 оно не формируется».** По теореме файла множество Рассела не образуется ни
  при каких условиях; слова главы слабее доказанного (расхождение 9).
- **Стр. 134–138, «более сильный P4/P1-запрет object-формы».** Для завершённой бесконечности запрет доказан при
  посылке-мосте: `completed_inf_contradicts_P4 : CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual
  -> False`. Для «импредикативной тотальности» теоремы в `P4ProhibitsImpredicative.v` нет (расхождение 9);
  отсылка идёт к главе 10.1, здесь не сверявшейся.
- **Стр. 125 и 170, «0 логических аксиом».** Для `P4_eliminates_Pi11` верно. В том же файле лемма
  `pi11_negation` (`:73`) стоит на `Classical_Prop.classic` (и на `eval_program`); глава о ней не говорит.
- **Стр. 62, «см. §10.5.1».** Разделы страницы не нумерованы.

## Вне главы: шапки и состав файлов

Для сведения (в главе эти строки не цитируются, кроме отмеченных выше):

- `TransfiniteInduction.v:12` — «Print Assumptions: classic, L4_witness only»; по компилятору все 12 утверждений
  закрыты (глава это отмечает). Из 12 `Qed`: `axiom_count_documentation` (`:151`) — лемма `True`;
  `nat_induction_from_transfinite` (`:87`) и `omega_tower_induction` (`:96`) — индукция по ℕ, первая доказана без
  `transfinite_ind`, вопреки имени; `transfinite_ind_zero`, `_succ`, `_omega`, `_epsilon_0` — частные случаи
  `transfinite_ind`.
- `Ordinal.v:4` — «Rules: Structural recursion, well-ordering»: линейность и транзитивность `ord_lt` в
  формализации не доказаны; о его составе — расхождение 1.
- `P4_Eliminates_Pi11.v:5` — «0 new axioms»: в файле один `Parameter`, одна лемма на `Classical_Prop.classic`.
  `pi11_hierarchy_collapse` (`:138`) — посылка в доказательстве отбрасывается (`intros phi _ n`);
  `decidable_lift` (`:128`) — заключение совпадает с посылкой; `P4_functions_are_nat` (`:47`) — `Program = nat`
  по определению.
- `P4_Eliminates_ATR.v` — семь из 17 лемм образуют три группы совпадающих утверждений (расхождение 11).
- `src/foundation/FiniteWqoPigeonhole.v:7` ссылается на «ε0/transfinite_ind достигнуты как процессы, 0-ax» —
  с той же оговоркой, что в расхождении 1.
- `src/settheory/CantorBendixsonFull.v:393` — `CB_ord_step` не рекурсивна: на `OSucc _` возвращает одну
  производную, на `OLim f` — пересечение конечных стадий, независимо от аргумента.

## Дополнительные проверки

- `Print Assumptions` снят для всех 91 утверждения семи файлов главы. Отличны от «Closed under the global context»
  только утверждения `P4_Eliminates_Pi11.v`: одиннадцать зависят от `eval_program`, из них `pi11_negation` — ещё и
  от `Classical_Prop.classic`.
- Файлы в репозитории и в собранной копии совпадают побайтно (SHA-1 семи файлов и `P4CompletedInfinity.v`).
- Счёт `Qed` (`grep -c 'Qed\.'`): `Ordinal.v` — 24, `TransfiniteInduction.v` — 12, `TransfiniteInductionLevel.v`
  — 6, `P4_Eliminates_ATR.v` — 17, `P4_Eliminates_Pi11.v` — 15, `P4_Eliminates_Infinity.v` — 10,
  `P4ProhibitsImpredicative.v` — 7.
- Оговорки главы о масштабе (стр. 14–30, 62–67, 82–93, 130–143, 154, 161–163: «P4-переинтерпретация, а не
  метатеорема обратной математики») соответствуют содержанию формализации: утверждений о подсистемах арифметики
  второго порядка в файлах нет. Блоков кода на странице нет.
- `P4_eliminates_ATR0` описан в сноске 3 точно: два определяющих равенства, оба закрываются `reflexivity`
  (перепроверено в `CheckATR.v`).
