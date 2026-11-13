# Глава I.6 «Аксиоматический минимум и механизм статуса», вторая половина (стр. 1069–1898, сноски 12–16) — заметки к ведомости (13.11.2026)

Ведомость: `part01-ch06b.json` — 47 ручных записей; `merge --dry` проходит без замечаний; в списке «без сверки»
остаются только имена первой половины главы (`co_constitution`, `L3_informative`, `L4_definite`, `NNPP_from_L3`,
`P4_eliminates_ATR0`, `P4_eliminates_Pi11`, `completed_inf_contradicts_P4`, `P4_dissolves_russell`). Вердикты ручных
записей: ok — 39, mismatch-price — 4, mismatch-statement — 4.

Четыре записи mismatch-price относятся к одному месту (расхождение 2), четыре записи mismatch-statement — к трём
(расхождения 1, 3, 4).

Участок: разделы «Статус, роль, передача: механизм через $E/R/R$», «Что в CIC встроено структурно», «Онтологические
Законы и технические аксиомы», «Незавершённость: математика и квантовая суперпозиция» и сноски 12–16 (их знаки стоят
на стр. 1367, 1383, 1492, 1824, 1856). Блоков кода в участке нет.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part01/ch06b/`: `Check.v` (универсы и уровни, выбор из
`L4_witness`, автомат статуса, модель допущений раздела Навье — Стокса), `Check2.v` (посылка `bridge`, определения
файла об унистохастичности, набросок к сноске 15), `Univ4.v` (универсы `Prop` и `Set`, `nat_ind`) — собираются;
`Univ1.v`, `Univ2.v`, `Univ3.v` намеренно не собираются: каждый содержит одно определение, отвергаемое проверкой
универсов, и нужен ради текста сообщения компилятора. В `src` и в собранной копии ничего не менялось; файлы, на
которые опирается участок, в репозитории и в собранной копии совпадают побайтно (SHA-1 тринадцати файлов).

## Что проверить не удалось

- Число «316 теорем на допущениях раздела Навье — Стокса» взято из обхода компилятором от 13.11.2026 и здесь не
  пересчитывалось (общий обход запускать было нельзя). Проверено: четыре объявления существуют (файл и строка — в
  расхождении 2); две теоремы раздела, взятые на пробу, показывают эти имена в `Print Assumptions`. Сводные числа
  обхода приведены как получены; их сумма по видам допущений (26 906 + 250 + 78 + 8 + 316 = 27 558) на 12 меньше
  общего числа 27 570 — разница здесь не разбиралась.
- Предложение «а» расхождения 2 (перевести допущения раздела Навье — Стокса в переменные раздела; свести `classic` к
  одному объявлению) сборкой не проверялось: оно требует пересборки `src`.
- Отсылки к Главам 1–4 и к §§ 6.1–6.5 (первая половина главы) не сверялись; первую половину проверяет другой
  помощник.
- Утверждения о самой платформе CIC (стр. 1463–1490: универс не обитает в себе, парадокс Рассела невыразим; стр.
  1619–1620: CIC не выводит $L3$ и извлечение свидетеля; стр. 1739–1741: объявлений «именно столько») —
  утверждения метатеории; компилятором проверено только то, что из них названо ниже.
- Глава о коиндуктивных системах, на которую ссылаются стр. 1366–1367 и сноска 12 («в последующих частях настоящего
  тома»), в томе не найдена: слова «коиндуктивн…», `Observable`, `CoinductiveSystems` встречаются на страницах тома
  только в этой главе.
- Содержание файлов физической программы (`L1_DoublyStochastic.v`, `L5_Indivisible.v`, `BlockCayleyUnistochastic.v`,
  `DoublyStochasticForkBridge.v`, `GeneralHermitianCayley.v`) сверено только по главным утверждениям двух первых;
  страница говорит о них словом «намечается».
- Для наброска «а» расхождения 1 не доказана связь меток `Level` с универсами: уровни универсов не являются
  значениями языка, и такую связь нельзя записать теоремой.
- Английская страница не смотрелась.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Иерархия уровней ToS в репозитории не стоит на универсной иерархии CIC (стр. 1492–1494; сноска 14, стр. 1912)

**Было:**

> (1492–1494) В репозитории иерархия уровней ToS[^14] строится поверх универсной иерархии CIC: формальная иерархия
> типов ToS опирается на ту, что в CIC уже есть.
>
> (сноска 14) Тип `Level` и отношение `level_lt` в файле `src/TheoryOfSystems_Core_ERR.v`; формальная иерархия ToS
> строится поверх универсной иерархии CIC.

**Проверка.** `src/TheoryOfSystems_Core_ERR.v:59`, `:68`, `:126`, `:163`, `:203`:

```coq
Inductive Level : Set :=
  | L1 : Level
  | LS : Level -> Level.

Fixpoint level_lt (l1 l2 : Level) : Prop :=
  match l2 with
  | L1 => False
  | LS l2' => l1 = l2' \/ level_lt l1 l2'
  end.

Theorem P1_no_self_membership : forall L, ~ (L << L).

Record Criterion (L : Level) : Type := mkCriterion {
  crit_domain : Type;
  crit_predicate : crit_domain -> Prop;
  crit_level_witness : Level;
  crit_level_valid : crit_level_witness << L;
}.

Record System (L : Level) : Type := mkSystem {
  sys_criterion : Criterion L;  sys_pos_bound : PositionBound;  sys_uniqueness : UniquenessConstraint;
}.
```

`Level` — индуктивный тип меток в `Set` (тот же, что положительные натуральные числа), `level_lt` — порядок на
метках. `P1_no_self_membership` есть иррефлексивность этого порядка; она доказана через ранг `level_depth` и
арифметику (`level_lt_irrefl`, `:96`). `Print Assumptions`: Closed under the global context.

Универсы (`Check.v`, `Set Printing Universes`):

```
Level         : Set
System L1     : Type@{max(Set+1,Criterion.u0+1)}
System L2     : Type@{max(Set+1,Criterion.u0+1)}
System L3     : Type@{max(Set+1,Criterion.u0+1)}
Criterion L1  : Type@{max(Set+1,Criterion.u0+1)}
Criterion L3  : Type@{max(Set+1,Criterion.u0+1)}
```

Системы всех уровней лежат в одном универсе. Уровень области — поле `crit_level_witness`, метка, которую вписывают
при построении критерия; от типа `crit_domain` она не зависит. Проверено (`Check.v`, Closed under the global context):

```coq
Lemma level_label_independent_of_domain :
  crit_domain L2 nat_labelled_L1 = crit_domain L3 nat_labelled_L2 /\
  crit_level_witness L2 nat_labelled_L1 <> crit_level_witness L3 nat_labelled_L2.
```

(одна и та же область `nat` несёт метку `L1` в критерии уровня `L2` и метку `L2` в критерии уровня `L3`).

Универсная иерархия действует независимо от меток и запрещает больше, чем требует $P1$. Критерий уровня `L3`, областью
которого служат системы уровня `L2`, с законной меткой `L2 << L3` (`Univ1.v`):

```coq
Definition system_of_L2_systems : Criterion L3 := {|
  crit_domain := System L2;
  crit_predicate := fun _ => True;
  crit_level_witness := L2;
  crit_level_valid := L2_lt_L3;
|}.
```

Ответ компилятора: `The term "System L2" has type "Type@{max(Set+1,Criterion.u0+1)}" while it is expected to have
type "Type@{Criterion.u0}" (universe inconsistency: Cannot enforce Criterion.u0 < Criterion.u0 …)`. То же для области
`Criterion L1` с меткой `L1 << L3` (`Univ2.v`). Сам файл это отмечает (`:364–368`): «Attempting to use System L2
directly as domain for Criterion L3 fails with "universe inconsistency" … We use indices as a practical workaround» —
и вводит `SystemL2Index := nat` (`:372`): системы уровня `L3` ссылаются на системы уровня `L2` через номера.

**В чём расхождение.** Иерархия уровней в коде есть отдельная разметка — тип меток с порядком; на универсы CIC она
не опирается, а универсная проверка в этой записи не пропускает и законный случай «система старшего уровня над
системами младшего».

**(а) Довести формализацию.** Иерархия, действительно стоящая на универсах, записывается универсно-полиморфной
записью; набросок проверен (`Check.v`; третье определение — `Univ3.v`):

```coq
Polymorphic Record UCrit@{u} : Type@{u+1} := mkUCrit {
  ucrit_domain : Type@{u};
  ucrit_predicate : ucrit_domain -> Prop;
}.

(* система систем: область — системы строго меньшего универса; проходит *)
Polymorphic Definition usystem_of_systems@{u v | u < v} : UCrit@{v} :=
  {| ucrit_domain := UCrit@{u}; ucrit_predicate := fun _ => True |}.

(* система над системами своего же универса; отвергается *)
Polymorphic Definition usystem_of_itself@{u} : UCrit@{u} :=
  {| ucrit_domain := UCrit@{u}; ucrit_predicate := fun _ => True |}.
(* universe inconsistency: Cannot enforce … = u because u < … *)
```

Здесь запрет самовключения есть правило формирования типов, как и сказано на стр. 1473–1479, а система старшего
уровня над системами младшего строится без индексов. Такую запись можно добавить отдельным файлом, не трогая `Level`
и `System` (менять их запрещено). Ограничение: связь меток `Level` с уровнями универсов теоремой не записывается —
уровни универсов не являются значениями языка; останутся две параллельные конструкции.

**(б) Поправить слова:**

> (1492–1494) В репозитории иерархия уровней ToS[^14] задана рядом с универсной иерархией CIC, отдельной
> разметкой: типом меток `Level` с порядком `level_lt`, для которого невозможность самовключения доказана теоремой
> (`P1_no_self_membership`). Универсная иерархия CIC действует при этом независимо от меток: систему, областью
> которой служили бы сами системы, проверка универсов не пропускает, и системы старшего уровня ссылаются в коде на
> системы младшего через индексы.
>
> (сноска 14) Тип `Level` и отношение `level_lt` в файле `src/TheoryOfSystems_Core_ERR.v`; иррефлексивность порядка —
> `P1_no_self_membership`. Системы всех уровней лежат в одном универсе; уровень области задаётся полем-меткой
> `crit_level_witness` записи `Criterion`.

Та же мысль стоит в первой половине главы (стр. 866–873: «Эта стратификация встроена в систему типов CIC через
универсную иерархию») — она вне этого участка.

## Расхождение 2 (цена). В репозитории объявлены не только `classic` и `L4_witness` (стр. 1451–1454, 1731–1732, 1736–1743, 1747–1748)

**Было:**

> (1451–1454) Именно поэтому ToS-репозиторий обходится всего двумя техническими объявлениями: платформа CIC
> структурно созвучна позиции ToS, и многое из того, что иначе пришлось бы вводить явно, в CIC уже присутствует по
> построению.
>
> (1731–1732) Формально аксиомы у ToS есть — два объявления в CIC; …
>
> (1738–1743) Этот объём — два объявления, `classic` и `L4_witness`. Они минимальны не в смысле «мы выбрали взять
> поменьше», а в смысле «CIC по своему устройству требует именно стольких, и не больше»: всё прочее, что нужно ToS,
> либо встроено в платформу (§ 6.7), либо выводится (Законы, Принципы, определения, теоремы).
>
> (1747–1748) … ToS объявляет в CIC две технические аксиомы.

**Проверка.** Объявления без доказательства в `src` и `Architecture_of_Reasoning` (поиск директив `Axiom`,
`Parameter`, `Conjecture` в начале строки):

| объявление | файл:строка | вид |
|---|---|---|
| `classic` | стандартная библиотека, подключена строкой `Require Export Coq.Logic.Classical_Prop` — `src/ToS_Axioms.v:31` | `Axiom` библиотеки |
| `classic` | `src/foundation/Distinction.v:36` | `Axiom` |
| `classic` | `src/settheory/BorelDeterminacy.v:21` | `Axiom` |
| `L4_witness` | `src/ToS_Axioms.v:105` | `Axiom` |
| `C_B` | `src/navier_stokes/TriadicInteraction.v:119` | `Parameter` |
| `C_B_positive : 0 < C_B` | `src/navier_stokes/TriadicInteraction.v:120` | `Axiom` |
| `B_coeff_bounded` | `src/navier_stokes/TriadicInteraction.v:122` | `Axiom` |
| `B_raw` | `src/navier_stokes/GalerkinSystem.v:208` | `Parameter` |

По обходу компилятором 13.11.2026: из 27 570 теорем и лемм без допущений 26 906; на `classic` — 250; на `classic` и
`L4_witness` — 78; только на `L4_witness` — 8; на двух аксиомах и двух параметрах раздела Навье — Стокса — 316.
Выборочно:

- `coupling_for_sum_triad` (`TriadicInteraction.v:125`) — `Axioms: TriadicInteraction.C_B, GalerkinSystem.B_raw,
  TriadicInteraction.B_coeff_bounded`;
- `ns_galerkin_bound_chain` (`navier_stokes/MillenniumComplete.v:102`) — `Axioms: TriadicInteraction.C_B_positive,
  TriadicInteraction.C_B`.

**В чём расхождение.** Логических допущений действительно два, но слова «всего двумя», «не больше», «всё прочее …
выводится» сказаны о репозитории целиком, а в нём 316 теорем стоят ещё на двух аксиомах и двух параметрах одного
раздела; кроме того, `classic` объявлен в трёх местах (о `Distinction.v` глава говорит на стр. 228–245,
`BorelDeterminacy.v` не называет).

**(а) Довести формализацию.** Возможно без новых аксиом; сборкой здесь не проверялось.

1. Допущения раздела Навье — Стокса перевести из объявлений в переменные раздела — так же, как 13.11 сделано с
   `eval_program` в `P4_Eliminates_Pi11.v`: `Section` с `Variable C_B : Q`, `Hypothesis C_B_positive`,
   `Variable B_raw`, `Hypothesis B_coeff_bounded`. После закрытия раздела каждая из 316 теорем станет утверждением
   «для любого сопряжения с такой оценкой», и имён раздела в выводе `Print Assumptions` не останется. Условные
   теоремы при этом не пусты — допущения имеют модель (`Check.v`, Closed under the global context):

   ```coq
   Definition ns_coupling_hypotheses (C : Q) (Braw : nat -> nat -> nat -> Q) : Prop :=
     (0 < C)%Q /\
     forall k l m,
       (Qabs (Braw k l m - Braw k m l) <= C * inject_Z (Z.of_nat (Nat.max k (Nat.max l m))))%Q.

   Lemma ns_coupling_hypotheses_have_model :
     exists (C : Q) (Braw : nat -> nat -> nat -> Q), ns_coupling_hypotheses C Braw.
   (* C = 1, Braw = 0 *)
   ```

   Работа затрагивает файлы раздела `navier_stokes` и всех, кто их подключает.
2. `classic` свести к одному объявлению: в `foundation/Distinction.v` и `settheory/BorelDeterminacy.v` заменить
   местную строку `Axiom classic` подключением `ToS_Axioms` (глава сама предлагает это для `Distinction.v` на стр.
   242–245). `ToS_Axioms.v` при этом не меняется.

После обоих шагов слова главы верны буквально: в выводе компилятора остаются только `Classical_Prop.classic` и
`ToS_Axioms.L4_witness`.

**(б) Поправить слова** (если формализацию не трогать):

> (1451–1454) Именно поэтому логический слой ToS-репозитория обходится всего двумя техническими объявлениями:
> платформа CIC структурно созвучна позиции ToS, и многое из того, что иначе пришлось бы вводить явно, в CIC уже
> присутствует по построению. Сверх них в репозитории объявлены только предметные допущения одного раздела — Навье —
> Стокса: две аксиомы (`C_B_positive`, `B_coeff_bounded`) и два параметра (`C_B`, `B_raw`); на них стоят теоремы
> этого раздела, и регистрацией Законов они не являются.
>
> (1731–1732) Формально логические аксиомы у ToS есть — два объявления в CIC; …
>
> (1738–1743) Этот объём — два объявления, `classic` и `L4_witness`. Они минимальны не в смысле «мы выбрали взять
> поменьше», а в смысле «CIC по своему устройству требует именно стольких, и не больше»: всё прочее, что нужно ToS,
> либо встроено в платформу (§ 6.7), либо выводится (Законы, Принципы, определения, теоремы). Предметные допущения
> раздела Навье — Стокса в этот счёт не входят: это условия одной задачи, названные в её разделе, а не объявления,
> которых требует платформа.
>
> (1747–1748) … ToS объявляет в CIC две технические аксиомы — регистрацию двух Законов.

Строки 1442–1444 и 1719–1720 («два технических объявления `classic` и `L4_witness` (слой B)»; «технический слой —
два объявления, регистрирующие два из Законов») после этих оговорок читаются верно; в ведомости они записаны как ok
с отсылкой сюда.

## Расхождение 3 (статус). «Этот аппарат построен и формально проверен» — о механизме статуса и о Законах (стр. 1874–1877)

**Было:**

> Глава 6 завершила *формальное* измерение Части I: разобран аппарат — Законы, Принципы, $E/R/R$-структура,
> технические основания реализации в Rocq, механизм статуса. Этот аппарат построен и формально проверен.

**Проверка.**

- О механизме статуса та же глава говорит обратное (стр. 1390–1401): полный механизм «в текущем репозитории отдельным
  файлом-автоматом *не* формализован … машинно-проверенной регистрацией всего механизма она пока не подкреплена».
  Поиск по `src` это подтверждает: записи состояния «действующий максимум + список повторов» с шаг-функцией нет.
  Формализованы более простые конструкции — `l5_resolve_gen` (`src/L5Resolution.v:76`), `L5_choose`
  (`src/foundation/P4_Eliminates_AC.v:25`).
- О Законах: $L3$ и $L4$ в Rocq — объявления без доказательства (`classic`, `L4_witness`); сама глава называет их
  так на стр. 1616–1623 и 1703–1705.

**В чём расхождение.** Итоговая фраза относит слова «формально проверен» ко всему перечню, в который входят
механизм, по словам той же главы не формализованный, и два Закона, принятые объявлением.

**(а) Довести формализацию.** Для механизма статуса — возможно, без допущений. Набросок автомата, каким его
описывает стр. 1393–1398 («с записью состояния, шаг-функцией и теоремами о единственности статуса максимума на
каждой стадии и о сбросе повторов»), проверен (`Check.v`; все утверждения — Closed under the global context):

```coq
Record StatusState := mkStatusState {
  st_max_pos : nat;        (* позиция носителя статуса максимума *)
  st_max_val : nat;        (* его значение *)
  st_repeats : list nat;   (* позиции повторных максимумов, в порядке появления *)
}.

(* None — шаг 0: система не развёрнута *)
Definition status_step (s : option StatusState) (pos val : nat) : option StatusState :=
  match s with
  | None => Some (mkStatusState pos val [])
  | Some st =>
      if st_max_val st <? val then Some (mkStatusState pos val [])            (* Правило 1 *)
      else if val =? st_max_val st
           then Some (mkStatusState (st_max_pos st) (st_max_val st) (st_repeats st ++ [pos]))  (* Правило 2 *)
           else Some st
  end.

(* процесс p : nat -> nat; позиции с 1; состояние стадии n строится из состояния стадии n-1 и текущего элемента *)
Fixpoint status_run (p : nat -> nat) (n : nat) : option StatusState :=
  match n with
  | O => None
  | S k => status_step (status_run p k) (S k) (p k)
  end.

Theorem status_run_none_iff : forall p n, status_run p n = None <-> n = 0.

Definition status_inv (p : nat -> nat) (n : nat) (st : StatusState) : Prop :=
  (1 <= st_max_pos st <= n) /\
  p (st_max_pos st - 1) = st_max_val st /\
  (forall k, k < n -> p k <= st_max_val st) /\
  (forall k, k < st_max_pos st - 1 -> p k < st_max_val st) /\
  (forall j, In j (st_repeats st) <-> (st_max_pos st < j <= n /\ p (j - 1) = st_max_val st)).

Theorem status_run_inv : forall p n st, status_run p n = Some st -> status_inv p n st.

Theorem status_reset_on_new_max : forall p n st,
  status_run p n = Some st -> st_max_val st < p n ->
  status_run p (S n) = Some (mkStatusState (S n) (p n) []).

Theorem status_holder_changes_only_on_strict_excess : forall p n st st',
  status_run p n = Some st -> status_run p (S n) = Some st' ->
  st_max_pos st' <> st_max_pos st -> st_max_val st < p n.

Inductive StatusRole := RoleMaximum | RoleRepeatMaximum | RoleBaseOnly.
Definition status_of (st : StatusState) (j : nat) : StatusRole := …
Theorem status_maximum_unique : forall st j, status_of st j = RoleMaximum <-> j = st_max_pos st.
```

Инвариант `status_run_inv` говорит: действующий максимум — наибольшее из пройденных значений; его несёт первая
позиция, на которой оно достигнуто (все более ранние значения строго меньше); список повторов — в точности позиции
после носителя, значение которых равно действующему максимуму. Доказательство — индукцией по числу шагов с разбором
трёх исходов шага; полный текст в `Check.v`.

Пример главы воспроизведён вычислением (`reflexivity`):

```coq
Definition chapter_example (k : nat) : nat := nth k [1; 3; 2; 5; 4; 5; 7; 7] 0.

Lemma example_stage_0 : status_run chapter_example 0 = None.
Lemma example_stage_1 : status_run chapter_example 1 = Some (mkStatusState 1 1 []).
Lemma example_stage_2 : status_run chapter_example 2 = Some (mkStatusState 2 3 []).
Lemma example_stage_3 : status_run chapter_example 3 = Some (mkStatusState 2 3 []).
Lemma example_stage_4 : status_run chapter_example 4 = Some (mkStatusState 4 5 []).
Lemma example_stage_5 : status_run chapter_example 5 = Some (mkStatusState 4 5 []).
Lemma example_stage_6 : status_run chapter_example 6 = Some (mkStatusState 4 5 [6]).
Lemma example_stage_7 : status_run chapter_example 7 = Some (mkStatusState 7 7 []).
Lemma example_stage_8 : status_run chapter_example 8 = Some (mkStatusState 7 7 [8]).

Lemma example_sixth_gains_and_loses :
  (exists st6, status_run chapter_example 6 = Some st6 /\ status_of st6 6 = RoleRepeatMaximum) /\
  (exists st7, status_run chapter_example 7 = Some st7 /\ status_of st7 6 = RoleBaseOnly).
```

Все девять стадий совпадают с разбором стр. 1243–1310, включая утрату статуса шестым элементом на шаге 7 (стр.
1315–1320). Состояние стадии зависит только от пройденных значений процесса `nat -> nat` — это формальная сторона
слов стр. 1364–1373 о потенциально продолжающихся процессах.

Если такой файл добавить, абзац стр. 1390–1401 заменяется ссылкой на него. Для Законов $L3$ и $L4$ слово «проверен»
делом не достигается: в Rocq они остаются объявлениями.

**(б) Поправить слова** (если формализацию не трогать):

> Глава 6 завершила *формальное* измерение Части I: разобран аппарат — Законы, Принципы, $E/R/R$-структура,
> технические основания реализации в Rocq, механизм статуса. Этот аппарат построен; формально проверены те его
> части, которые названы в главе по именам, — производные принципы из двух объявлений, разрешение списка по порядку
> $L5$, выбор как правило и условный запрет завершённого графа. Два Закона зарегистрированы объявлениями, а полный
> механизм статуса § 6.6 пока остаётся содержательной схемой.

(После добавления файла-автомата последняя оговорка о механизме снимается.)

## Расхождение 4 (статус). Формулировка «бесконечность есть процесс, не объект» в `ProcessP4Synthesis.v` — комментарий, а не теорема (сноска 15, стр. 1913)

**Было:** «Процессная природа бесконечности зафиксирована в файле `src/foundation/ProcessP4Synthesis.v` репозитория —
в формулировке «бесконечность есть процесс, не объект» и в конструкции порождающего процесса.»

**Проверка.** Слова «Infinity is a process, not an object» стоят в заголовке-комментарии файла (строка 9; строка 4:
«Rules: infinity = process (potential), not object (completed)»). Теоремы файла (`:45–:140`; 9 `Qed`, шапка называет
10; все — Closed under the global context):

- `process_finite_at_stage` (`:45`) — значение процесса на стадии есть дробь `num # den`;
- `const_process_compatible` (`:50`), `process_equiv_refl` (`:94`), `const_equiv` (`:102`);
- `pillar1_prohibition` (`:59`) — повтор `completed_inf_contradicts_P4`: противоречие при трёх посылках, включая
  мост `bridge`;
- `pillar2_potential` (`:66`) — `forall n, exists m, n < m`;
- `pillar3_completeness` (`:71`) — повтор `process_completeness`;
- `gp_prefix_length` (`:128`) — `length (gp_prefix p n) = n`;
- `process_p4_grand_synthesis` (`:140`) — конъюнкция шести перечисленных и соседних фактов (запрет при `bridge`;
  `potential_infinity`; неотрицательность стадийной метрики и её нуль на диагонали; полнота; длина префикса).

«Конструкция порождающего процесса» — определение `GenProcess (A : Type) := nat -> A` (`:115`; в `ProcessGeneral.v`
то же имя расшифровано как «general process» — процесс общего вида, значение на каждом шаге) с функциями
`gp_observe`, `gp_prefix`.

**В чём расхождение.** Названная формулировка в файле есть комментарий; доказаны условный запрет завершённой
бесконечности, неограниченность натурального ряда и свойства процессов, собранные в одну конъюнкцию.

**(а) Довести формализацию.** Возможно. Содержательная форма тезиса для процесса общего вида — «всякая стадия
продолжается следующей, и никакой конечный список не вмещает всех стадий» (`Check2.v`, обе — Closed under the global
context):

```coq
Theorem gen_process_stage_extends : forall (A : Type) (p : GenProcess A) (n : nat),
  gp_prefix p (S n) = gp_prefix p n ++ [gp_observe p n].
Proof. intros. reflexivity. Qed.

Theorem gen_process_never_completed : forall (A : Type) (p : GenProcess A) (l : list A),
  exists n, length l < length (gp_prefix p n).
Proof.
  intros A p l. exists (S (length l)). rewrite gp_prefix_length. lia.
Qed.
```

Вместе с уже имеющейся `potential_process_compatible_with_P4` (`foundation/P4CompletedInfinity.v:190`: стадии
ограничены, вложены, всякое число достигается на некоторой стадии, и ни одна стадия не содержит всего) они дают
теорему, которую сноска может назвать по имени.

**(б) Поправить слова:**

> [^15]: Процессная природа бесконечности представлена в файле `src/foundation/ProcessP4Synthesis.v` репозитория:
> формулировка «бесконечность есть процесс, не объект» стоит в его заголовке, а доказаны в нём условный запрет
> завершённой бесконечности (при мосте `bridge`, § 6.5), потенциальная бесконечность — за всяким числом есть
> большее, — полнота пространства процессов и конечность всякого начального отрезка процесса `GenProcess`.

## Сомнительные места (не расхождения)

- **Стр. 1073–1076, 1369–1370, 1432–1433 («Аксиома Выбора … в ToS не воспроизводится», «не работает», «без её
  принятия»).** В Rocq выбор по $ℕ$-индексированному семейству непустых списков — теорема без допущений
  (`AC_on_nat_as_rule`), а из `L4_witness` функция выбора строится для любого семейства: `functional_choice_from_L4 :
  forall (I A : Type) (R : I -> A -> Prop), (forall i, exists x, R i x) -> exists f : I -> A, forall i, R i (f i)`
  (`Check.v`; `Print Assumptions`: только `L4_witness`). Глава оговаривает это сама (стр. 582–615, 1403–1430), и
  точная её позиция — стр. 1426–1430. Если нужна точность в самой фразе стр. 1073: «…Аксиома Выбора, прочитанная
  как завершённый граф функции выбора, в ToS не воспроизводится…».
- **Стр. 1380–1388 и сноска 13, `l5_res_rule`.** Лемма утверждает только, что результат имеет вид `Some v`; это
  верно по определению для непустого списка, свойства порядка в доказательстве не участвуют (`some_without_order`
  в `Check.v`). Слова «всегда приходит к определённому результату» по существу несут три теоремы `src/L5Resolution.v`:
  `l5_resolve_gen_in` (`:176`), `l5_resolve_gen_minimal` (`:188`), `l5_resolve_gen_deterministic` (`:208`); уместно
  назвать их в сноске 13.
- **Стр. 1385–1386, «при наличии порядка над элементами».** К `L5_choose` это не относится: функция берёт голову
  списка `list nat`, порядок на элементах в ней не участвует, а для пустого списка она возвращает переданное
  значение `default`.
- **Стр. 1364–1367 и сноска 12, `Observable`.** Тип существует, но коиндуктивным не является: это запись из функции
  `nat -> A` и критерия. Главы о коиндуктивных системах в томе не найдено (см. «Что проверить не удалось»).
- **Стр. 1380–1401, близкий файл не назван.** `src/foundation/StatusFromERR.v` (11 `Qed`, шапка называет 12)
  присваивает статусы `PrimaryMax` / `SecondaryMax` / `Candidate` / `Invalid` по готовому списку сущностей с весами:
  наибольший вес, при равенстве — меньший номер; равный вес получает `SecondaryMax`. Это тот же замысел («максимум и
  повторный максимум») в виде одной функции без шагов и сброса; слова главы «отдельным файлом-автоматом не
  формализован» остаются верными.
- **Стр. 1408–1412, формула.** Внутри `$$…$$` имя `family` обрамлено звёздочками (`*family*`); в формуле они не
  дают курсива и печатаются как знаки. Утверждение формулы с `AC_is_L5` совпадает.
- **Стр. 1416–1426, посылка `bridge`.** Слова «взятая как завершённое целое» и «чтение функции как завершённого
  графа» соответствуют посылке `bridge`: всякий индекс графа актуален на стадии 0. Для графа функции она равносильна
  `forall n, actual 0 n` и от функции не зависит (`bridge_of_graph_iff_all_actual`, `Check2.v`, Closed) — это
  согласуется со словами «верно для графа любой всюду определённой функции». В первой половине (стр. 989–1000) мост
  назван по имени; здесь — описан словами.
- **Стр. 1465–1467, счёт универсов.** По ответу компилятора `Prop : Type@{Set+1}` и `Set : Type@{Set+1}`
  (`Univ4.v`); «`Type`$_0$» страницы — обозначение первого универса над `Set`.
- **Стр. 1585–1586, «этот вывод выдерживает формализацию».** Вывод $L3$ и $L4$ из акта различения в Rocq не
  проводится: оба Закона приняты объявлениями (`Law_of_ExcludedMiddle` в `foundation/LawsFromDistinction.v:63` есть
  `exact classic`; `L3_from_distinction`, `:67`, возвращает поле `exhaustive` записи `Distinction`). Формализация
  показывает, что результат вывода можно зарегистрировать и что он работает. Возможная точная форма: «…CIC лишь
  показывает, что результат этого вывода реализуем: два Закона зарегистрированы объявлениями, остальное доказано».
- **Стр. 1616–1618, место объявления `classic`.** В `ToS_Axioms.v` директива `Axiom` одна — `L4_witness`; `classic`
  там реэкспортируется из стандартной библиотеки (первая половина главы, стр. 208–219, говорит это точно). Третье
  текстовое объявление — `settheory/BorelDeterminacy.v:21` — в главе не названо.
- **Стр. 1652–1658, 1674–1679, «$L3$ выведен из тотальности акта различения».** Слово «выведен» отнесено к выводу
  Главы 3; о Rocq в этих местах сказано «объявление `classic`». Статус назван честно.
- **Стр. 1739–1741, «именно стольких».** Независимость двух объявлений друг от друга и от CIC — утверждение
  метатеории; внутри Rocq оно не доказывается и в формализации не записано.
- **Сноска 16, определения файла.** (1) `is_doubly_stochastic` (`:94`) требует только единичных сумм строк и
  столбцов; неотрицательность в определение не входит — ему удовлетворяет матрица `[[2, −1], [−1, 2]]`
  (`doubly_stochastic_without_nonneg`, `Check2.v`, Closed). Для унистохастической матрицы неотрицательность верна и
  доказывается (`unistochastic_nonneg`, там же, Closed), но в заключение `unistochastic_implies_DS` не входит.
  (2) `is_unistochastic` (`:100`) определено через рациональную ортогональную матрицу — в обычной терминологии это
  ортостохастическая матрица, частный случай унистохастической; условия `U·Uᵀ = I` и `Uᵀ·U = I` входят в
  определение оба (комментарий `:73–74`: вывод второго из первого требует теории определителей).
- **Стр. 1849–1853, сопоставления программы.** Слово «намечается» честное. Для сведения: `L1_doubly_stochastic`
  (`foundation/L1_DoublyStochastic.v:84`) — строчно-стохастическая матрица, для которой равномерное распределение
  стационарно, столбцово-стохастична (закон $L1$ входит как это условие стационарности); `L5_implies_indivisible`
  (`foundation/L5_Indivisible.v:141`) — утверждение о двух конкретных историях `H1`, `H2`, посылки `L5_monotone` в
  доказательстве не используются (`intros T Hm1 Hm2 Hsens _ _`). Оба — Closed under the global context.

## Вне участка: шапки и состав файлов

Для сведения (в участке эти строки не цитируются):

- `src/ToS_Axioms.v:14–15` — «These are the ONLY axioms in the entire ToS formalization. Every theorem ultimately
  depends on at most these two»: не учитывает раздел Навье — Стокса (расхождение 2). Строка `:27` — «STATUS: 3 Qed»;
  в файле две строки `Qed.` и одна `Defined.`
- `src/TheoryOfSystems_Core_ERR.v:1233–1237` (комментарий) — «System L1 : Type@{u1}, System L2 : Type@{u2} where
  u2 > u1»: по компилятору все `System L` лежат в одном универсе (расхождение 1). Строки `:364–368` — «fails with
  "universe inconsistency" — exactly what we want»: отвергается и законный случай (область младшего уровня).
- `src/TheoryOfSystems_Core_ERR.v:248`, `:1255`, `:1300` — `russell_paradox_blocked`, `cantor_paradox_blocked_v1`,
  `cantor_no_system_of_all_L2_systems`: в каждой первая часть условия (`crit_domain = System L`) в доказательстве не
  используется; противоречие получается из метки `crit_level_witness = L` и поля `crit_level_valid`. В участке эти
  имена не названы.
- `src/foundation/ProcessP4Synthesis.v:5` — «STATUS: 10 Qed»; в файле 9.
- `src/foundation/StatusFromERR.v:5` — «STATUS: 12 Qed»; в файле 11. В теореме `uniqueness` (`:119`) посылки
  `find_primary entities = Some p` и `In e entities` в доказательстве не используются.
- `src/CoinductiveSystems.v:179` — `no_complete_observation : exists n, n >= length l`: наблюдаемый процесс `o` в
  заключение не входит.

## Дополнительные проверки

- `Print Assumptions` снят для всех имён участка и для утверждений, на которые опираются записи: `l5_res_rule`,
  `l5_resolve_gen_some`, `_in`, `_minimal`, `_deterministic`; `L5_choose` (оба файла), `L5_choose_in_nonempty`,
  `AC_is_L5`, `P4_eliminates_AC`, `P4_eliminates_AC_finite`; `AC_on_nat`, `AC_on_nat_as_rule`,
  `completed_graph_contradicts_P4`, `ac_completed_graph_contradicts_P4`, `ac_implies_completed`,
  `finite_choice_works`, `choice_as_rule_compatible_with_P4`, `P4_cuts_completed_keeps_rule`,
  `completed_reading_strictly_stronger`, `P4_prohibits_AC`; `P1_no_self_membership`, `level_lt_irrefl`,
  `russell_paradox_blocked`; `factorial_5`; все 9 утверждений `ProcessP4Synthesis.v`; все 19 утверждений
  `UnistochasticFromGraph.v`. Ответ везде — Closed under the global context. `nat_ind` — Closed.
- Счёт `Qed` (`grep -c 'Qed\.'`): `FormationRules.v` — 18, `L5Resolution.v` — 18, `CoinductiveSystems.v` — 16,
  `TheoryOfSystems_Core_ERR.v` — 36, `ToS_Axioms.v` — 2, `P4_Eliminates_AC.v` — 17, `P4ProhibitsAC.v` — 15,
  `ProcessP4Synthesis.v` — 9, `UnistochasticFromGraph.v` — 19, `P4_Eliminates_Infinity.v` — 13,
  `P4CompletedInfinity.v` — 10. Чисел `Qed` и чисел файлов в участке страница не называет.
- Абзац стр. 1403–1430 о двух файлах выбора соответствует их нынешнему содержанию: `AC_is_L5` и `P4_eliminates_AC`
  совпадают дословно, `AC_on_nat` имеет ту же сигнатуру, `AC_on_nat_as_rule` доказывает `AC_on_nat` головой списка,
  `completed_graph_contradicts_P4` сформулирована для произвольной функции.
- Оговорки участка о статусе (стр. 1377–1401: полный механизм не формализован; стр. 1853–1862, 1864–1870:
  формализованы отдельные матричные леммы, а не вывод квантовой теории; стр. 1561–1586: созвучие платформы не есть
  доказательство позиции) соответствуют содержанию формализации.
