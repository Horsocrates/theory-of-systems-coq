# Глава I.5 «Со-определение A и ¬A» — заметки к ведомости (13.11.2026)

Ведомость: `part01-ch05.json` — 53 ручные записи + 7 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты ручных записей: ok — 40, mismatch-statement — 11, mismatch-price — 2
(с автоматическими: ok — 47).

Тринадцать записей с расхождением относятся к восьми местам (расхождения 1–8): три записи — о слове «выведены»
применительно к законам, три — о лемме `co_constitution`, две — о словах «формальные теоремы о со-определении».

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part01/ch05/`: `Check.v` (эквивалентности сторон, примеры
экземпляров, ослабленные записи, прежняя формулировка `co_constitution`, цена обратного перехода, выбор из
`L4_witness`), `CheckCoDef.v` (запись с одним правилом — со-определением — и законы как теоремы о ней),
`CheckFail.v` и `Bad1.v`–`Bad3.v` (ответы Rocq на неполное построение записи; три последних намеренно не
собираются). `Check.v`, `CheckCoDef.v`, `CheckFail.v` собираются; ответы `Print Assumptions` приведены по месту.
В `src` и в собранной копии ничего не менялось.

Глава называет три файла `src/foundation/`: `Distinction.v` (20 `Qed`), `LawsFromDistinction.v` (22),
`ERRFromDistinction.v` (17). Для проверки слов главы прочитаны ещё `PrinciplesFromLaws.v` (20),
`BinarityVsTotality.v` (9), `PrinciplesToERR.v`, а также определения уровней в `TheoryOfSystems_Core_ERR.v` и
аксиома в `ToS_Axioms.v`. Для всех объявлений первых пяти файлов снят `Print Assumptions`.

## Что проверить не удалось

- Отсылки к другим главам (§ 2.1, § 2.6, § 3.7, § 4.2.2, § 4.8, § 4.9.3, Глава 6) не сверялись; это предмет
  ведомостей этих глав. Из соседних глав прочитано только нужное для слов этой главы: объединяющие теоремы
  `five_laws_from_distinction` и `four_principles_from_five_laws`, шапка `PrinciplesToERR.v`, строки 1140–1152
  главы 3 (о форме, в которой в теорему входит $L5$).
- Слова о применении $E/R/R$ к Абсолюту (стр. 30–31) с формализацией не сверялись.
- Слова о дальнейших частях тома — числовые системы (Часть III), групповые структуры (Часть XI), категории
  (стр. 1066–1069, 1363–1366, 1425, 1552) — не сверялись. Проверен только один факт: какие файлы подключают
  `foundation.Distinction` (см. «Сомнительные места», п. 5).
- Утверждение «исчерпанность не строится конструктивно» (стр. 398–400) в полном смысле есть утверждение о
  недоказуемости исключённого третьего в CIC; внутри Rocq оно не проверяется. Проверены его внутренние формы:
  из существования различения по всякой пропозиции следует исключённое третье (`Check.v`, Closed under the
  global context).
- Утверждения о типизированных системах вообще («не существует в любой системе, реализующей запись с
  зависимыми полями», стр. 422–427, 472–479) проверены только для Rocq 9.0.1 — командами `Check` и тремя
  намеренно неполными определениями.
- Исторические и филологические сведения (Соссюр, Якобсон, Гегель, «И цзин», Нагарджуна; сноски 6–9) вне
  предмета аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Выведены» при том, что $L2$ и $L3$ даны полями, а $L1$ и $L5$ от записи не зависят (стр. 12–14, 486–488; в части законов — стр. 27–28)

**Было:**

> (12–14) …этот акт получил запись `Distinction` с четырьмя полями (Глава 2); из структуры записи были выведены
> законы $L1$–$L5$ (Глава 3);
>
> (486–488) В Главе 3 законы $L1$–$L5$ были выведены как *теоремы* о произвольной `Distinction` — утверждения,
> которые *держатся* на каждом экземпляре.

**Проверка.** `src/foundation/LawsFromDistinction.v:139`:

```coq
Theorem five_laws_from_distinction : forall D : Distinction,
  (positive D = positive D /\ negative D = negative D) /\
  (~ (positive D /\ negative D)) /\
  (positive D \/ negative D) /\
  (positive D -> ~ negative D) /\
  (forall l : Level, ~ (l << l)).
Proof.
  intro D. split; [|split; [|split; [|split]]].
  - split; reflexivity.
  - exact (exclusive D).
  - exact (exhaustive D).
  - intros p n. apply (exclusive D). split; [exact p | exact n].
  - intro l. exact (level_lt_irrefl l).
Qed.
```

Closed under the global context. По членам:

| закон | утверждение | чем закрыт |
|---|---|---|
| $L1$ | `positive D = positive D /\ negative D = negative D` | `reflexivity` — верно для любого терма, устройство записи не используется |
| $L2$ | `~ (positive D /\ negative D)` | `exact (exclusive D)` — проекция поля |
| $L3$ | `positive D \/ negative D` | `exact (exhaustive D)` — проекция поля |
| $L4$ | `positive D -> ~ negative D` | из поля `exclusive` — один шаг вывода |
| $L5$ | `forall l : Level, ~ (l << l)` | `level_lt_irrefl` — `D` в утверждение не входит |

То же для отдельных теорем: `L2_from_distinction` (`:50`) — `exact L2_exclusivity`, `L3_from_distinction` (`:67`) —
`exact L3_totality`; обе вспомогательные теоремы (`Distinction.v:107`, `:117`) — проекции полей.

**В чём расхождение.** Из пяти законов из устройства записи выводится один — $L4$. $L2$ и $L3$ заданы полями, и
теоремы их возвращают; $L1$ есть рефлексивность равенства; $L5$ — теорема о типе уровней, запись в неё не входит.
Сама глава говорит это точно в других местах: о $L2$ и $L3$ — «само поле записи есть структурная реализация»
(стр. 554–559, 577–580), о $L5$ — «от конкретного $D$ не зависит» (стр. 671–678).

**(а) Довести формализацию.** Для $L2$, $L4$ и для $L3$ в форме «третьего нет» — возможно, без аксиом: взять
данным одно правило, со-определение сторон, и получить остальное теоремами. Набросок проверен (`CheckCoDef.v`):

```coq
Record CoDefinition := mkCoDef {
  c_pos   : Prop;
  c_neg   : Prop;
  c_codef : c_neg <-> ~ c_pos
}.

Theorem L2_from_codef : forall C : CoDefinition, ~ (c_pos C /\ c_neg C).
Proof. intros C [p n]. exact (proj1 (c_codef C) n p). Qed.

Theorem L4_from_codef : forall C : CoDefinition, c_pos C -> ~ c_neg C.
Proof. intros C p n. exact (proj1 (c_codef C) n p). Qed.

Theorem L3_binarity_from_codef : forall C : CoDefinition, ~ ~ (c_pos C \/ c_neg C).
Proof.
  intros C H. apply H. right. apply (proj2 (c_codef C)). intro p. apply H. left. exact p.
Qed.

Theorem L3_totality_from_codef : forall C : CoDefinition, c_pos C \/ c_neg C.
Proof.
  intro C. destruct (Distinction.classic (c_pos C)) as [p | np].
  - left. exact p.
  - right. exact (proj2 (c_codef C) np).
Qed.

Theorem totality_for_codef_is_EM :
  (forall C : CoDefinition, c_pos C \/ c_neg C) -> forall P : Prop, P \/ ~ P.
Proof. intros H P. exact (H (mkCoDef P (~ P) (iff_refl (~ P)))). Qed.

Definition codef_of_distinction (D : Distinction) : CoDefinition.   (* всякое различение есть со-определение *)
Definition distinction_of_codef (C : CoDefinition) (a : c_pos C \/ c_neg C) : Distinction :=
  mkDistinction (c_pos C) (c_neg C) (L2_from_codef C) a.
```

`Print Assumptions`: `L2_from_codef`, `L4_from_codef`, `L3_binarity_from_codef`, `totality_for_codef_is_EM`,
`codef_of_distinction`, `distinction_of_codef` — Closed under the global context; `L3_totality_from_codef` —
`Axioms: classic : forall P : Prop, P \/ ~ P`. То есть из со-определения несовместность, самообоснование и
отсутствие третьего следуют без допущений, а исчерпанность стоит ровно `classic`. Близкая запись уже есть в
формализации — `PendingDistinction` (`src/foundation/BinarityVsTotality.v:94`), но там несовместность оставлена
полем `p_exclusive`, хотя следует из поля `p_codef`.

Для $L1$ и $L5$ довести нельзя по существу: `x = x` верно для любого терма и из записи не следует, а $L5$
говорит об уровнях — это отдельный слой, как и сказано на стр. 671–678.

**(б) Поправить слова:**

> (12–14) …этот акт получил запись `Distinction` с четырьмя полями (Глава 2); по структуре записи были прослежены
> законы $L1$–$L5$ (Глава 3): $L2$ и $L3$ — сами поля записи, $L1$ и $L4$ — теоремы о всяком её экземпляре,
> $L5$ — теорема об уровнях;
>
> (486–488) В Главе 3 законы $L1$–$L4$ были получены как *теоремы* о произвольной `Distinction` — утверждения,
> которые *держатся* на каждом экземпляре ($L2$ и $L3$ — как сами поля записи); $L5$ — как теорема об уровнях.

## Расхождение 2. «Вывод $P1$–$P4$ из законов суть формальные теоремы» (стр. 25–31)

**Было:**

> …вывод $L1$–$L5$ из `Distinction` и вывод $P1$–$P4$ из законов суть формальные теоремы, тогда как мост
> $P1$–$P4 \to E/R/R$ есть архитектурная интерпретация, а применение $E/R/R$ к Абсолюту — метафизический, а не
> машинно-проверенный шаг.

**Проверка.** `src/foundation/PrinciplesFromLaws.v:242`:

```coq
Theorem four_principles_from_five_laws :
  (forall l : Level, ~ (l << l)) /\
  (forall L (C : Criterion L), P2_valid L C) /\
  (forall L (S : System L), systems_intensionally_equal S S) /\
  (forall (R : nat -> Q) n, exists (num : Z) (den : BinNums.positive), R n = num # den).
Proof.
  split; [|split; [|split]].
  - exact level_lt_irrefl.
  - exact P2_always_holds.
  - intros L S. exact (P3_reflexivity L S).
  - exact P4_finite_at_each_stage.
Qed.
```

Closed under the global context. Посылок у теоремы нет; ни один закон и ни одна теорема о `Distinction` в
доказательстве не участвуют. По членам: $P1$ — `forall l : Level, ~ (l << l)`, дословно то же утверждение, что
конъюнкт $L5$ в `five_laws_from_distinction`; $P2$ — `P2_valid L C := crit_level_witness L C << L`, проекция поля
`crit_level_valid` записи `Criterion` (`TheoryOfSystems_Core_ERR.v:163–178`); $P3$ — рефлексивность тройки
равенств `systems_intensionally_equal` (`:282`); $P4$ — разбор значения типа `Q` на числитель и знаменатель.

О мосте к $E/R/R$ статус на странице назван честно: шапка `PrinciplesToERR.v` (раздел F-2) говорит
«соответствие, не вывод».

**В чём расхождение.** Формальными теоремами записаны сами утверждения $P1$–$P4$; перехода «из законов» в
формализации нет — теорема с таким именем законов не использует.

**(а) Довести формализацию.** В пределах этой главы — нечем: формулировки принципов лежат в
`PrinciplesFromLaws.v` и `TheoryOfSystems_Core_ERR.v` и разбираются при проверке глав 3 и 4. Для «вывода» нужна
теорема, в которой закон стоит посылкой, а принцип — заключением; при нынешних формулировках $P1$ и $L5$ — одно и
то же утверждение, так что содержательного шага между ними нет. Набросок не делался.

**(б) Поправить слова:**

> …и не всегда сведены в одну единую теорему: законы $L1$–$L5$ и принципы $P1$–$P4$ записаны формальными
> теоремами ($L1$–$L4$ — о всяком экземпляре `Distinction`, $L5$ и принципы — об уровнях, критериях, системах и
> процессах), тогда как переходы между звеньями — от законов к принципам и мост $P1$–$P4 \to E/R/R$ — есть
> архитектурная интерпретация, а применение $E/R/R$ к Абсолюту — метафизический, а не машинно-проверенный шаг.

## Расхождение 3. Лемма `co_constitution`: на странице прежняя формулировка и прежнее доказательство (стр. 601–622)

**Было:**

> В Rocq-репозитории ToS[^3] есть лемма, носящая имя со-определения:
>
> ```coq
> Lemma co_constitution : forall P : Prop,
>   (P -> exists Q, Q = ~P) /\ ((~P) -> exists Q, Q = P).
> ```
>
> …Её доказательство в репозитории — `split; intro H; eexists; reflexivity` — тривиально, и тривиальность эта
> показательна: предпосылки $P$ и $\neg P$ в нём фактически *не используются*. С тем же успехом доказуемы и более
> простые утверждения $\forall P,\ \exists Q,\ Q = \neg P$ и $\forall P,\ \exists Q,\ Q = P$. Поэтому
> `co_constitution` *не* является сильным доказательством со-определения… Её содержание скромнее: как только
> пропозиция $P$ дана как объект языка, выражение $\neg P$ уже синтаксически доступно как пропозиция.

**Проверка.** `src/foundation/Distinction.v:202`:

```coq
Lemma co_constitution : forall P : Prop,
  positive (distinction_of P) = P /\ negative (distinction_of P) = ~ P.
Proof. intro P. split; reflexivity. Qed.
```

Формулировка заменена 10.06.2026 (коммит 4b5e0e8); комментарий над леммой (`:197–201`) называет прежнюю
«vacuous» по той же причине, что и глава. `Print Assumptions co_constitution`:
`Axioms: Distinction.classic : forall P : Prop, P \/ ~ P` — аксиома приходит через `distinction_of`, о котором
говорит лемма; о цене леммы страница не говорит. В других файлах лемма не применяется.

Прежняя формулировка и оба «более простых утверждения» по-прежнему доказуемы названной тактикой (`Check.v`:
`co_constitution_old`, `old_without_premise_1`, `old_without_premise_2` — Closed under the global context), так
что рассуждение главы о них верно, но относится к лемме, которой в репозитории уже нет.

**В чём расхождение.** Блок кода, текст доказательства и описание содержания относятся к прежней лемме. Нынешняя
утверждает другое: каноническое различение по $P$ имеет сторонами $P$ и $\neg P$. Оба равенства верны по
определению `distinction_of`, поэтому вывод главы — «не является сильным доказательством со-определения» —
остаётся в силе.

**(а) Довести формализацию.** Сама лемма соответствует своему комментарию; менять её незачем. Чтобы у тезиса
главы была формальная опора, нужны леммы о связи сторон во всяком экземпляре — они приведены в расхождении 6.

**(б) Поправить слова** (стр. 603–622):

> В Rocq-репозитории ToS[^3] есть лемма, носящая имя со-определения:
>
> ```coq
> Lemma co_constitution : forall P : Prop,
>   positive (distinction_of P) = P /\ negative (distinction_of P) = ~ P.
> ```
>
> Здесь требуется точность относительно того, *что именно* эта лемма доказывает. Её доказательство в
> репозитории — `intro P. split; reflexivity` — тривиально, и тривиальность эта показательна: оба равенства верны
> по определению `distinction_of`, которое само помещает $P$ в поле `positive`, а $\neg P$ — в поле `negative`.
> Поэтому `co_constitution` *не* является сильным доказательством со-определения в смысле зависимости истинности
> или осмысленности сторон. Её содержание скромнее: каноническое различение по $P$ одним актом задаёт обе
> стороны — $P$ и $\neg P$. Это — *минимальный след* со-определения в каноническом случае, а не полная
> формализация центрального тезиса главы.

Если нужно сохранить рассуждение о прежней формулировке, его можно дать одной фразой после блока: «Прежняя
формулировка леммы — `(P -> exists Q, Q = ~P) /\ ((~P) -> exists Q, Q = P)` — была слабее: её посылки в
доказательстве не использовались; в июне 2026 года она заменена».

## Расхождение 4. $L5$ в `five_laws_from_distinction` — иррефлексивность для всякого уровня, а не базового (стр. 673–678)

**Было:** «…объединяющая теорема `five_laws_from_distinction` там подключает иерархический слой, причём $L5$ в ней
представлен иррефлексивностью базового уровня и от конкретного $D$ не зависит (как было разобрано в Главе 3).»

**Проверка.** Пятый конъюнкт теоремы (`LawsFromDistinction.v:144`) — `forall l : Level, ~ (l << l)`. Вид
`~ (L1 << L1)` он имел до 24.05.2026 (коммит 0b2d17b). Глава 3 (стр. 1148–1149) говорит о нынешнем виде: «$L5$
представлен общим утверждением об иррефлексивности *для всякого уровня*, $\forall l,\ \neg(l \ll l)$, а не только
для базового».

**В чём расхождение.** Страница описывает прежний, более слабый конъюнкт; в формализации он общий.

**(а) Довести формализацию.** Не требуется: формализация сильнее слов.

**(б) Поправить слова:**

> …объединяющая теорема `five_laws_from_distinction` там подключает иерархический слой, причём $L5$ в ней
> представлен иррефлексивностью порядка уровней — для всякого уровня, $\forall l,\ \neg(l \ll l)$, — и от
> конкретного $D$ не зависит (как было разобрано в Главе 3).

## Расхождение 5 (цена). «Совокупность эквивалентна» — обратный переход стоит $L3$ (стр. 862–866)

**Было:** «Это утверждение легко проверить структурно. Если `exclusive` утверждает
$\neg (\texttt{positive} \wedge \texttt{negative})$, а `exhaustive` — $\texttt{positive} \vee \texttt{negative}$, то
их совокупность *эквивалентна* утверждению $\texttt{negative} \leftrightarrow \neg \texttt{positive}$:»

**Проверка.** В формализации такого утверждения нет. В пробном файле (`Check.v`):

```coq
Lemma fields_give_iff : forall p n : Prop, ~ (p /\ n) -> p \/ n -> (n <-> ~ p).      (* Closed *)
Lemma iff_gives_exclusive : forall p n : Prop, (n <-> ~ p) -> ~ (p /\ n).             (* Closed *)
Lemma iff_gives_exhaustive_classic : forall p n : Prop, (n <-> ~ p) -> p \/ n.        (* Distinction.classic *)
Lemma iff_gives_exhaustive_is_EM :
  (forall p n : Prop, (n <-> ~ p) -> p \/ n) -> forall P : Prop, P \/ ~ P.            (* Closed *)
```

Последняя лемма показывает, что без `classic` обратный переход не получить: он равносилен исключённому третьему
(достаточно взять $n := \neg p$).

**В чём расхождение.** Два пункта, идущие на странице следом, доказывают одну сторону: из полей следует
равносильность. Обратная сторона — от равносильности к исчерпанности — верна только ценой $L3$; в другом месте
(стр. 398–402) глава эту цену называет, здесь — нет.

**(а) Довести формализацию.** Возможно. Двусторонняя форма без допущений (`CheckCoDef.v`, Closed under the global
context):

```coq
Theorem fields_iff_codef_and_assignment : forall p n : Prop,
  (~ (p /\ n) /\ (p \/ n)) <-> ((n <-> ~ p) /\ (p \/ n)).
```

то есть два поля записи равносильны со-определению вместе с назначением стороны; а назначение при
со-определении даёт `classic` (`iff_gives_exhaustive_classic`).

**(б) Поправить слова:**

> …то из их совокупности *следует* утверждение $\texttt{negative} \leftrightarrow \neg \texttt{positive}$:

либо, сохраняя слово «эквивалентна», добавить после двух пунктов фразу: «Обратный переход — от этой
равносильности к несовместности — столь же прямой; к исчерпанности он ведёт уже ценой $L3$».

## Расхождение 6. «Утверждения ToS о со-определении суть формальные теоремы, проверяемые Rocq» (стр. 1353–1359)

**Было:**

> **Второе: проверяемость.** Формальная запись позволяет *доказывать* утверждения о со-определении. Леммы,
> разобранные в § 5.3, и теоремы, выведенные в Главе 3 — это формальные результаты, имеющие силу в CIC. …
> Утверждения ToS о со-определении суть формальные теоремы, проверяемые Rocq.

**Проверка.** В § 5.3 разобраны: лемма `co_constitution` — о ней сама глава говорит, что это не доказательство
со-определения (стр. 616–622); и эквивалентности `negative D <-> ~ positive D`, `positive D <-> ~ negative D`,
названные «точной формальной опорой тезиса» (стр. 624–638). О вторых сноска 4 сообщает, что лемм
`negative_iff_not_positive` и `positive_iff_not_negative` в файле нет. Поиск по `src` (по именам и по
формулировкам) это подтверждает. В `Distinction.v` есть две половины, идущие из поля `exclusive`:
`L4_self_grounding : positive D -> ~ negative D` (`:128`) и `L4_contrapositive : negative D -> ~ positive D`
(`:133`); половин, идущих из `exhaustive`, нет.

**В чём расхождение.** Сноска 4 называет положение дел честно, а раздел «Что даёт формализация» говорит о тех же
утверждениях как о доказанных в Rocq. Утверждения верны, но в репозитории теоремами не записаны.

**(а) Довести формализацию.** Возможно, без аксиом. Леммы проверены (`Check.v`; все — Closed under the global
context) и могут быть добавлены в `Distinction.v` без новых подключений:

```coq
Lemma negative_iff_not_positive : forall D : Distinction,
  negative D <-> ~ positive D.
Proof.
  intro D. split.
  - intros n p. exact (exclusive D (conj p n)).
  - intro np. destruct (exhaustive D) as [p | n].
    + exfalso. exact (np p).
    + exact n.
Qed.

Lemma positive_iff_not_negative : forall D : Distinction,
  positive D <-> ~ negative D.
Proof.
  intro D. split.
  - intros p n. exact (exclusive D (conj p n)).
  - intro nn. destruct (exhaustive D) as [p | n].
    + exact p.
    + exfalso. exact (nn n).
Qed.

Theorem negative_determined_by_positive : forall D1 D2 : Distinction,
  (positive D1 <-> positive D2) -> (negative D1 <-> negative D2).
Proof.
  intros D1 D2 H.
  pose proof (negative_iff_not_positive D1) as H1.
  pose proof (negative_iff_not_positive D2) as H2.
  split; intro n.
  - apply (proj2 H2). intro p2. exact (proj1 H1 n (proj2 H p2)).
  - apply (proj2 H1). intro p1. exact (proj1 H2 n (proj1 H p1)).
Qed.

Theorem positive_determined_by_negative : forall D1 D2 : Distinction,
  (negative D1 <-> negative D2) -> (positive D1 <-> positive D2).
```

Третья и четвёртая теоремы выражают тезис главы прямо: какой бы пропозицией ни была заполнена одна сторона,
другая определена ею с точностью до равносильности. К ним примыкает утверждение о том, когда различение по
данной пропозиции вообще существует (`CheckCoDef.v`, Closed under the global context):

```coq
Theorem distinction_on_P_iff_decided : forall P : Prop,
  (exists D : Distinction, positive D = P) <-> (P \/ ~ P).
```

После добавления слова стр. 1353–1359 верны без правки; сноску 4 тогда следует заменить: «Эти эквивалентности
оформлены в файле `Distinction.v` леммами `negative_iff_not_positive` и `positive_iff_not_negative`; обе
доказаны из полей `exclusive` и `exhaustive` без аксиом».

**(б) Поправить слова** (если формализацию не трогать):

> **Второе: проверяемость.** Формальная запись позволяет *доказывать* утверждения о со-определении. Теоремы,
> выведенные в Главе 3, — формальные результаты, имеющие силу в CIC; эквивалентности сторон, разобранные в
> § 5.3, доказываются из полей записи в несколько шагов, хотя отдельными леммами в репозитории пока не
> оформлены. Соссюровское «в языке нет ничего, кроме различий» не есть теорема и не может быть доказано или
> опровергнуто; это — общее наблюдение. Утверждения ToS о со-определении суть утверждения о записи
> `Distinction`, допускающие проверку в Rocq.

## Расхождение 7 (цена). `L4_witness` среди аксиом, на которые опирается работа с `Distinction` (стр. 1545–1549)

**Было:** «В Главе 6 настоящей части обсуждаются технические аксиомы Rocq, на которые опирается работа с
`Distinction`, — классическая аксиома `classic` и аксиома `L4_witness`, реализующая механизм передачи статуса
через E/R/R вместо Аксиомы Выбора.»

**Проверка.** `Print Assumptions` для всех объявлений пяти файлов:

- `Distinction.v`: `distinction_of`, `every_prop_distinguishes`, `one_distinction_exists`,
  `two_distinctions_exist`, `distinction_count_succ`, `distinction_count_any`, `co_constitution`,
  `distinction_decidable`, `distinction_and`, `distinction_or` — `Distinction.classic`; остальное — Closed under
  the global context (в том числе `true_distinction_positive`, `true_distinction_negative`,
  `false_distinction_positive`, хотя их формулировки упоминают `distinction_of`: в доказательство оно не входит);
- `LawsFromDistinction.v`: `Law_of_ExcludedMiddle`, `L4_double_negation`, `laws_consistent`, `L3_independence` —
  `Distinction.classic`; остальные 18 теорем — Closed;
- `ERRFromDistinction.v`: `complete_foundation`, `foundation_summary` — `Distinction.classic`; остальное — Closed;
- `PrinciplesFromLaws.v`: все 20 теорем — Closed;
- `BinarityVsTotality.v`: `classic_decides`, `totality_completes`, `distinction_of_is_actualization` —
  `Distinction.classic`; остальное — Closed.

`ToS_Axioms.L4_witness` не встречается ни в одном ответе. В 23 файлах `src`, подключающих `foundation.Distinction`,
имя `L4_witness` стоит один раз — в комментарии (`PrinciplesFromLaws.v:190`).

**В чём расхождение.** Цена названа по соседству аксиом, а не по компилятору: работа с записью `Distinction`
опирается на `classic` и только на неё.

**(а) Довести формализацию.** Не требуется: зависимость от `L4_witness` вводить незачем.

**(б) Поправить слова:**

> В Главе 6 настоящей части обсуждаются аксиомы формализации: классическая аксиома `classic`, на которую
> опирается каноническое построение `distinction_of`, и аксиома `L4_witness`, реализующая механизм передачи
> статуса через E/R/R вместо Аксиомы Выбора.

## Расхождение 8 (имена). `L2` в сноске 2 (стр. 1558)

**Было:** «Аналогично `L2`: в `LawsFromDistinction.v` теорема `L3_from_distinction` утверждает…»

**Проверка.** В формализации идентификатор `L2` — второй уровень иерархии: `Definition L2 := LS L1`
(`TheoryOfSystems_Core_ERR.v:63`); он входит, например, в `L5_concrete : L1 << L2`. Объявления закона под этим
именем нет. Во всём остальном тексте главы законы набраны формулой.

**(а)** Не требуется.

**(б) Стало:** «Аналогично $L2$: в `LawsFromDistinction.v` теорема `L3_from_distinction` утверждает…»

## Сомнительные места (не расхождения)

1. **Стр. 392–402 и 704–713, незавершённое различение.** С июля 2026 года в формализации есть файл
   `src/foundation/BinarityVsTotality.v`, которого глава не упоминает. В нём: запись `PendingDistinction` (`:94`) —
   две стороны, со-определение `p_neg <-> ~ p_pos` и несовместность, без исчерпанности; `pending_of` (`:117`) —
   такая запись по любой пропозиции, Closed under the global context; `actualize` (`:130`) — переход к
   `Distinction` при предъявленном назначении стороны; `distinction_of_is_actualization` (`:191`) —
   `distinction_of P = actualize (pending_of P) (classic P)`. Формула стр. 401–402 («одна пропозиция $P$ задаёт
   обе стороны и их несовместность; их совместная исчерпанность добавляется принципом $L3$») этим файлом
   подтверждена дословно, и на него можно сослаться. С другой стороны, слова стр. 708–713 («в ToS невозможно
   описать „частичное“ различение, в котором какая-то часть структуры есть, а другая ещё не пришла») и стр.
   591–593 («запись без `exhaustive` описывает не акт различения, а его *отсутствие*») расходятся с тем, как
   этот файл называет `PendingDistinction` («the pending act», формальный тип слоя «может быть, но нет»).
   Замечание: в `PendingDistinction` есть поле со-определения, поэтому третье для неё исключено
   (`pending_binarity : ~ ~ (p_pos D \/ p_neg D)`, Closed) — «зазора» в смысле стр. 582–586 в ней нет. Как
   согласовать главу с этим файлом, решает автор.
2. **Стр. 710–711, «все пять структурных следствий».** По стр. 665–687 той же главы из построения экземпляра
   следуют четыре свойства $L1$–$L4$ (`five_properties_of_distinction`), а $L5$ обеспечен отдельным слоем.
   Согласованная форма: «все четыре поля и все четыре структурных следствия $L1$–$L4$».
3. **Стр. 477–479, «отвергнет … как синтаксически некорректное».** Rocq отвергает такие выражения на проверке
   типов, а не синтаксиса: для `mkDistinction P` — «The term … has type "forall negative : Prop, …" while it is
   expected to have type "Distinction"», для `{| positive := P |}` — «Cannot infer field negative of record
   Distinction» (`Bad1.v`–`Bad3.v`). Точнее: «отвергнет любое такое выражение как не имеющее типа
   `Distinction`».
4. **Стр. 957–966, таблица E/R/R.** Формально в `ERRFromDistinction.v` определён только список элементов
   `err_elements`. Роли и правила представлены там числами `err_role_count D := 2`, `err_rule_count D := 2`,
   не зависящими от `D`; строки таблицы о ролях и правилах повторяют комментарий файла (`:32–35`). В
   `PrinciplesToERR.v:97` есть рукописная таблица `distinction_meta_system` из шести узлов; теорема
   `every_distinction_err_well_formed` (`:111`) свою посылку `D` не использует (`intros _`). Глава на эти
   объявления не ссылается.
5. **Стр. 1362–1370, «`Distinction` есть фундамент … рабочий инструмент, на котором строится последующее».**
   В формализации модуль `foundation.Distinction` подключают 23 файла `src` из более чем двух тысяч — 22 файла
   каталога `foundation/` и `stdlib/PiFromDistinction.v`. Ядро (`ToS_Axioms.v`,
   `TheoryOfSystems_Core_ERR.v`) его не подключает; теоремы о принципах $P1$–$P4$ запись не используют
   (расхождение 2); лемма `co_constitution` вне своего файла не применяется. Слова читаются как порядок
   изложения в томе; как утверждение о зависимостях в формализации они шире проверенного.
6. **Стр. 1548–1549, «вместо Аксиомы Выбора».** По записи `L4_witness` извлекает свидетеля из одного
   существования; из этой формулировки следует функциональный выбор по произвольному семейству —
   `l4_statement_gives_functional_choice` (`src/settheory/ChoicePriceMap.v:234`, Closed under the global
   context); то же перепроверено в `Check.v` (`functional_choice_from_L4_witness`, допущение — `L4_witness`).
   Это предмет главы 6 и Части X; здесь формула автора оставлена как есть.
7. **Стр. 1546, «технические аксиомы Rocq».** `classic`, на которую опирается `distinction_of`, объявлена в самой
   формализации (`Distinction.v:36`); в выводе компилятора она значится как `Distinction.classic`, отдельно от
   `Classical_Prop.classic` стандартной библиотеки, которую вывозит `ToS_Axioms.v`. Формулировки двух аксиом
   совпадают.
8. **Стр. 1425 и 1552, «Часть VIII» о категориях.** На сайте Часть VIII — «Обыкновенные дифференциальные
   уравнения», категориям посвящена Часть XIV («Категория систем»). Ссылки на Часть III и Часть XI
   (стр. 1066–1069, 1365, 1553) нумерации сайта не противоречат.
9. **Стр. 201–203, «ни одно из полей нельзя предъявить без остальных».** Две пропозиции существуют и сами по
   себе; без остального нельзя предъявить два доказательства, типы которых упоминают обе стороны. Глава
   уточняет это сама на стр. 294–308.
10. **Сноска 3 (стр. 1559), «в секции».** В `Distinction.v` это раздел, отмеченный комментарием (`:186`); команды
    `Section` в файле нет. Слово можно заменить на «в разделе».
11. **Стр. 862–873, 871.** Слова «содержательно `negative` *всегда* есть отрицание `positive`» верны в смысле
    равносильности (`negative_iff_not_positive`, Closed); равенства пропозиций нет, что глава и оговаривает на
    стр. 640–648. Пример: `mkDistinction True False …` (`Check.v`, `D_true_false`).

## Вне главы: шапки и состав файлов

Для сведения (в главе эти строки не цитируются):

- `Distinction.v:34–35` — комментарий «Not an additional axiom — L3 = classic» стоит над объявлением
  `Axiom classic`. `distinction_theorem_count := 22` (`:250`) при 20 `Qed`.
- `LawsFromDistinction.v:6` — «0 new axioms»: четыре теоремы файла зависят от `Distinction.classic`
  (`Law_of_ExcludedMiddle`, `L4_double_negation`, `laws_consistent`, `L3_independence`).
- `LawsFromDistinction.v:172`, `L3_independence : (forall D : Distinction, positive D \/ negative D) -> (forall P :
  Prop, P \/ ~ P)` — посылка в доказательстве отбрасывается (`intros _ P. exact (classic P)`), а сама посылка
  есть теорема (`L3_from_distinction`), так что утверждение равносильно `classic`. Содержательная внутренняя
  форма доказуема без аксиом (`Check.v`, Closed under the global context):
  `every_prop_distinguishes_gives_EM : (forall P : Prop, exists D : Distinction, positive D = P) -> forall P :
  Prop, P \/ ~ P` — то есть теорема `every_prop_distinguishes` (`Distinction.v:82`) равносильна исключённому
  третьему.
- `LawsFromDistinction.v:155`, `laws_consistent` — зависит от `classic` только потому, что свидетелем взято
  `distinction_of True`; со свидетелем `mkDistinction True False …` утверждение закрыто.
- `ERRFromDistinction.v` — `err_distinction_theorem_count := 22` (`:225`) при 17 `Qed`; `err_element_count`,
  `err_role_count`, `err_rule_count` (`:51–57`) — константа 2, не зависящая от аргумента; на них стоят
  `minimum_two_roles`, `err_balanced`, `err_complete_spec`, `su2_from_distinction`.
- `PrinciplesFromLaws.v:43–52` — `P1_from_L1_L5`, `P1_no_self_membership`, `P1_blocks_russell` — три теоремы с
  одним утверждением `forall l : Level, ~ (l << l)`; то же утверждение — `L5_hierarchy`
  (`LawsFromDistinction.v:111`).
- `BinarityVsTotality.v:94` — поле `p_exclusive` записи `PendingDistinction` следует из поля `p_codef`
  (`Check.v`, `iff_gives_exclusive`, Closed).

## Дополнительные проверки

- Файлы `Distinction.v`, `LawsFromDistinction.v`, `ERRFromDistinction.v`, `PrinciplesFromLaws.v`,
  `PrinciplesToERR.v`, `BinarityVsTotality.v`, `TheoryOfSystems_Core_ERR.v`, `ToS_Axioms.v`,
  `settheory/ChoicePriceMap.v` в репозитории и в собранной копии совпадают побайтно.
- Счёт `Qed` (`grep -c 'Qed\.'`): `Distinction.v` — 20, `LawsFromDistinction.v` — 22, `ERRFromDistinction.v` — 17,
  `PrinciplesFromLaws.v` — 20, `BinarityVsTotality.v` — 9. Чисел такого рода на странице нет.
- Объявления `Axiom` и `Parameter` в `src` (поиск по началу строки): `classic` (`foundation/Distinction.v:36`,
  `settheory/BorelDeterminacy.v:21`), `L4_witness` (`ToS_Axioms.v:105`), `C_B_positive`, `B_coeff_bounded`,
  `C_B`, `B_raw` (раздел Навье — Стокса). Пропозициональной и функциональной экстенсиональности нет (стр.
  645–647 главы верна).
- Статус исключённого третьего: во всех четырёх местах, где глава называет `classic` (стр. 390, 395, 400, 1548),
  она названа аксиомой; расхождения со статусом в `Distinction.v:36` нет.
- Блоки кода: `Record Distinction` (стр. 268, 803) отличается от исходника завершающей точкой с запятой и
  комментариями; `distinction_of` (стр. 374) — тот же терм, в исходнике записанный в режиме доказательства
  (равенство закрыто рефлексивностью, `distinction_of_unfold`); `co_constitution` (стр. 606) — расхождение 3.
- Сигнатура конструктора (стр. 325–329) совпадает с ответом `Check mkDistinction`.
- Утверждения о гипотетических ослабленных записях (стр. 561–564, 582–586) проверены на пробных записях
  `NoExclusive` и `NoExhaustive` (`Check.v`): первая допускает экземпляр с двумя истинными сторонами, вторая — с
  двумя ложными; обе леммы — Closed under the global context.
