# Глава I.4 «E/R/R: онтология системы», вторая половина — заметки к ведомости (13.11.2026)

Участок: строки 1030–2155 (от раздела «Иерархия уровней» до конца основного текста) и сноски 12–25
(стр. 2167–2180) — те, чей знак стоит в этих строках. Первую половину главы проверяет другой помощник.

Ведомость: `part01-ch04b.json` — 69 ручных записей; `merge --dry` проходит без замечаний (все цитаты и
объявления найдены). Вердикты ручных записей: ok — 45, mismatch-statement — 24; mismatch-price, wrong-number,
missing-name — нет. В списке «без сверки» остались только имена первой половины (стр. 338 и сноски 2, 4, 7, 10).

Двадцать четыре записи mismatch-statement относятся к четырнадцати местам (расхождения 1–14).

Пробный файл: `C:/Users/abary/tos-audit-build/_part01/ch04b/Check.v` — собирается; все 46 строк
`Print Assumptions` — «Closed under the global context». В `src` репозитория, в `tos-audit-build/src` и на сайте
ничего не менялось.

Участка касаются файлы: `TheoryOfSystems_Core_ERR.v` (36 Qed), `foundation/Distinction.v` (20),
`foundation/LawsFromDistinction.v` (22), `foundation/ERRFromDistinction.v` (17), `foundation/PrinciplesFromLaws.v` (20),
`foundation/ERRWellFormedness.v` (9), `foundation/ParadoxDiagnosis.v` (11), `foundation/PrinciplesToERR.v` (7);
попутно смотрелись `foundation/TransfiniteInductionLevel.v` (9), `foundation/MetaPairStrength.v` (17),
`UniversePolymorphism.v` (23), `foundation/ERRSystemBridge.v` (6), `foundation/KnowledgeQuestionPath.v` (26). Первые восемь
файлов в репозитории и в собранной копии совпадают побайтно. Чисел (`Qed`, файлов, аксиом) страница на этом участке
не называет.

Цена на участке названа верно везде, где названа: `classic` всюду назван аксиомой (стр. 1734, 1775, 1813, 1823,
1847; `Print Assumptions distinction_of` — `Axioms: Distinction.classic : forall P : Prop, P \/ ~ P`); «без аксиом»
о `err_self_well_formed` (стр. 1397) — Closed under the global context. Все теоремы, названные на участке, закрыты.

## Что проверить не удалось

- Ссылки назад, в первую половину главы («было показано, что $P1$ выводится из $L1 + L5$», стр. 1942–1944;
  «Минимальность: два элемента, две роли, два правила»), и в главы 2, 3, 6 не сверялись: это участки других
  проверок. Из главы 3 посмотрено одно место — § 3.5.2 о `L4_self_grounding` (к расхождению 3).
- Раздел «Мета-система: Абсолют» (стр. 1189–1349) сам объявляет себя не машинно-проверенным; его тезисы не
  оценивались. Проверено только утверждение об отсутствии объектов (см. «Сомнительные места», п. 4).
- Отрицательные утверждения страницы — «нет объекта `Absolute`», «`Distinction` и `distinction_of` не оформлены как
  `System L`» — проверены поиском по `src` и командой `Locate`, а не доказательством.
- Утверждение стр. 1775 («для произвольной пропозиции исчерпанность конструктивно не доказуема») метатеоретическое;
  компилятором не проверяется.
- Для наброска вычислимого критерия без циклов (`reach`, `acyclic`; расхождение 6) не доказывалось, что `reach`
  равносильно существованию цепочки ссылок. Для свойства `stratified` отсутствие циклов доказано.
- Замечание о парадоксе Ябло (расхождение 9) — рассуждение, не проверка: таблица для него не строилась.
- Сноска 19 (46 парадоксов, отдельная работа автора) — не о формализации; не сверялась.
- Английская страница и LaTeX-исходник не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. `L5_no_infinite_descent` описана по прежней формулировке (стр. 1084, 1168–1169, 2000–2002)

**Было:**

> (1084) Каждый конкретный уровень имеет конечную глубину относительно основания — это и фиксирует теорема
> `L5_no_infinite_descent` из Главы 3. Интерпретация этого факта как отсутствия неоснованного нисхождения
> естественна; но саму теорему о невозможности бесконечной нисходящей цепи уровней пришлось бы формулировать
> отдельно — теорема `L5_no_infinite_descent` доказывает более слабое утверждение о конечной глубине каждого уровня.
>
> (1168–1169) По теореме `L5_no_infinite_descent` (…) каждый уровень имеет конечную глубину; потому иерархия имеет
> *нижнюю границу* — базовый уровень $L_1$.
>
> (2000–2002) каждый *конкретный* уровень имеет конечную глубину относительно основания (это и есть содержание
> $L5$ и теоремы `L5_no_infinite_descent`)

**Проверка.** `src/foundation/LawsFromDistinction.v:126–132`:

```coq
(** L5 well-founded: no infinite descending chains — the depth measure STRICTLY
    DECREASES along <<, which is the genuine well-foundedness content (June 2026:
    was `exists n, level_depth l = n`, vacuous; the real theorem is Core_ERR's
    level_lt_depth). *)
Theorem L5_no_infinite_descent : forall l1 l2 : Level,
  l1 << l2 -> (level_depth l1 < level_depth l2)%nat.
Proof. exact level_lt_depth. Qed.
```

Closed under the global context. Теорема о невозможности бесконечной нисходящей цепи есть:

```coq
(* foundation/MetaPairStrength.v:137 *)
Theorem no_infinite_level_regress :
  forall f : nat -> Level, ~ (forall n : nat, level_lt (f (S n)) (f n)).
(* foundation/TransfiniteInductionLevel.v:43, :122 *)
Lemma level_lt_wf : well_founded level_lt.
Theorem level_foundation_form : forall P : Level -> Prop,
  (exists l, P l) -> ~ (forall l, P l -> exists l', P l' /\ l' << l).
```

Все — Closed. Нижняя граница: `L1_minimal : forall l, ~ (l << L1)` и `L1_lt_any_LS : forall l, L1 << LS l`
(`UniversePolymorphism.v:225`, `:248`) — из определения порядка, без обращения к `L5_no_infinite_descent`.

**В чём расхождение.** Страница описывает формулировку, заменённую в июне 2026: нынешняя теорема утверждает
строгое убывание глубины при спуске, а теорема, которую страница называет отсутствующей, доказана.

**(а) Довести формализацию.** Не требуется: формализация сильнее слов страницы. Если нужно, чтобы следствие
стояло в одном файле с законом, его можно добавить в `LawsFromDistinction.v`; набросок проверен (`Check.v`, Closed):

```coq
Theorem no_infinite_descent_from_L5 :
  forall f : nat -> Level, ~ (forall n, f (S n) << f n).
Proof.
  intros f H.
  assert (Hd : forall n, level_depth (f n) + n <= level_depth (f 0)).
  { induction n as [|n IH].
    - lia.
    - pose proof (L5_no_infinite_descent _ _ (H n)) as Hlt. lia. }
  specialize (Hd (S (level_depth (f 0)))). lia.
Qed.
```

**(б) Поправить слова:**

> (1084) Каждый конкретный уровень имеет конечную глубину относительно основания: глубина задана функцией
> `level_depth` со значениями в натуральных числах. Теорема `L5_no_infinite_descent` из Главы 3 фиксирует
> большее — при спуске по $\ll$ глубина строго убывает. Поэтому отсутствие неоснованного нисхождения здесь не
> интерпретация, а теорема: бесконечной нисходящей цепи уровней нет (`no_infinite_level_regress`), порядок $\ll$
> фундирован (`level_lt_wf`).
>
> (1168–1169) По теореме `L5_no_infinite_descent` (…) глубина уровня строго убывает при спуске, так что спуск от
> любого уровня конечен; потому иерархия имеет *нижнюю границу* — базовый уровень $L_1$.
>
> (2000–2002) каждый *конкретный* уровень имеет конечную глубину относительно основания, и при спуске она строго
> убывает (это и есть содержание $L5$ и теоремы `L5_no_infinite_descent`)

## Расхождение 2. «Вывод законов как теорем»: в записи L2 и L3 даны полями, L3 в общем виде — аксиома (стр. 1341–1343, 1532–1533, 1558–1559)

**Было:**

> (1341–1343) Их вывод в Rocq как теорем (Глава 3) — методологическое прослеживание, не онтологическое основание.
>
> (1532–1533) формальный вывод законов из этой записи — в Главе 3.
>
> (1558–1559) *Универсальный слой* — законы $L1$–$L5$. Они работают в `Distinction` как теоремы, выведенные в
> Главе 3.

**Проверка.** Запись (`src/foundation/Distinction.v:36`, `:67`):

```coq
Axiom classic : forall P : Prop, P \/ ~P.

Record Distinction := mkDistinction {
positive   : Prop;
negative   : Prop;
exclusive  : ~ (positive /\ negative);
exhaustive : positive \/ negative;
}.
```

Теоремы о законах (`Distinction.v`, `LawsFromDistinction.v`) и ответы компилятора:

| закон | теорема | чем доказана | `Print Assumptions` |
|---|---|---|---|
| L1 | `Law_of_Identity : forall A : Prop, A = A`; `L1_through_distinction` | `reflexivity` | Closed |
| L2 | `Law_of_NonContradiction : forall A, ~ (A /\ ~A)` | конструктивно | Closed |
| L2 | `L2_from_distinction : forall D, ~ (positive D /\ negative D)` | `exact (exclusive D)` | Closed |
| L3 | `Law_of_ExcludedMiddle : forall A, A \/ ~A` | `exact classic` | Axioms: Distinction.classic |
| L3 | `L3_from_distinction : forall D, positive D \/ negative D` | `exact (exhaustive D)` | Closed |
| L4 | `Law_of_SufficientReason : forall D, positive D -> ~ negative D` | из `exclusive D` | Closed |
| L5 | `L5_hierarchy : forall l : Level, ~ (l << l)` | `level_lt_irrefl` | Closed |

Сводная `five_laws_from_distinction : forall D : Distinction, …` (`LawsFromDistinction.v:139`) собирает те же пять
членов: `reflexivity`, `exclusive D`, `exhaustive D`, вывод из `exclusive D`, `level_lt_irrefl`. Closed.

`L3_from_distinction` закрыта потому, что поле `exhaustive` дано вместе с экземпляром. Построить экземпляр для
произвольной пропозиции можно только с аксиомой: `Print Assumptions distinction_of` —
`Axioms: Distinction.classic : forall P : Prop, P \/ ~ P`.

**В чём расхождение.** «Вывод из записи» для L2, L3 и L4 есть чтение полей записи: закон дан вместе с различием,
а не получен из него. L3 для произвольной пропозиции принят аксиомой; L1 и L5 от записи не зависят (первое —
рефлексивность равенства, второе — свойство отдельно определённого типа `Level`). На том же месте страницы
(стр. 1561–1565) поля `exclusive` и `exhaustive` названы конкретным слоем правил — так что универсальный слой
для L2 и L3 формально совпадает с конкретным.

**(а) Довести формализацию.** Для L3 — нельзя: исключённое третье в исчислении Rocq без аксиомы не доказуемо
(это отмечает и сам файл, `LawsFromDistinction.v:166–171`). Без допущений доказуемо следующее (`Check.v`, оба —
Closed under the global context):

```coq
(* L3 для одной пропозиции из одного её различия *)
Theorem L3_for_distinguished_prop :
  forall (P : Prop) (D : Distinction),
    Distinction.positive D = P -> negative D = (~ P) -> P \/ ~ P.
Proof.
  intros P D Hp Hn. pose proof (exhaustive D) as He. rewrite Hp, Hn in He. exact He.
Qed.

(* у всякой пропозиции есть различие со сторонами P и ~P  <->  исключённое третье *)
Theorem distinction_for_every_prop_iff_lem :
  (forall P : Prop, exists D : Distinction,
      Distinction.positive D = P /\ negative D = (~ P))
  <-> (forall P : Prop, P \/ ~ P).
Proof.
  split.
  - intros H P. destruct (H P) as [D [Hp Hn]].
    pose proof (exhaustive D) as He. rewrite Hp, Hn in He. exact He.
  - intros lem P.
    exists (mkDistinction P (~ P) (fun H => match H with conj p np => np p end) (lem P)).
    split; reflexivity.
Qed.
```

Вторая теорема даёт точную форму тезиса «L3 есть исчерпанность различия»: допущение стоит не в переходе от
различия к закону, а в том, что различие есть у всякой пропозиции; это допущение равносильно `classic`. С ней слова
«L3 выведен из различия» становятся верными в форме «для пропозиции, у которой есть различие». L2 в общей форме
уже является теоремой без допущений.

**(б) Поправить слова** (ход мысли автора — о первичности законов — не затрагивается):

> (1341–1343) Их запись в Rocq (Глава 3: $L2$ в общем виде — теорема без допущений; $L3$ для произвольной
> пропозиции — аксиома `classic`; в записи `Distinction` $L2$ и $L3$ даны полями `exclusive` и `exhaustive`) —
> методологическое прослеживание, не онтологическое основание.
>
> (1532–1533) формальное прослеживание законов на этой записи — в Главе 3.
>
> (1558–1559) *Универсальный слой* — законы $L1$–$L5$. В `Distinction` они записаны теоремами Главы 3; для $L2$
> и $L3$ эти теоремы читают поля `exclusive` и `exhaustive`, названные ниже.

## Расхождение 3. «$L4$ самообоснован в формальной системе Rocq» (стр. 1362–1364)

**Было:** «было показано, что $L4$ *самообоснован* в формальной системе Rocq — закон достаточного основания
обосновывает сам себя.»

**Проверка.** `src/foundation/Distinction.v:128`:

```coq
Theorem L4_self_grounding : forall D : Distinction,
  forall (p : positive D), ~ negative D.
Proof. intros D p n. apply (exclusive D). split; [exact p | exact n]. Qed.
```

Closed under the global context. `Law_of_SufficientReason` (`LawsFromDistinction.v:79`) — то же утверждение,
`exact L4_self_grounding`. Форма «из $P$ следует не-$N$» и форма «не ($P$ и $N$)» — одно утверждение в двух
записях (`Check.v`, Closed):

```coq
Theorem L4_form_is_L2_form : forall P N : Prop, (P -> ~ N) <-> ~ (P /\ N).
```

**В чём расхождение.** Теорема с именем «самообоснование» утверждает несовместность сторон и получена из поля
`exclusive`; применения закона достаточного основания к самому себе в формализации нет.

**(а) Довести формализацию.** В терминах записи `Distinction` утверждение «закон обосновывает сам себя» не
записывается: для него нужно отношение «быть основанием» между утверждениями, которого в `Distinction.v` нет. В
репозитории такое отношение рассматривается в двух местах, и к слову «самообоснование» они относятся по-разному:
в `foundation/GroundedOrderedStructure.v:64` для всякого фундированного отношения зависимости доказано
`no_self_ground : forall x, ~ dep x x` — ничто не есть собственное основание; в
`foundation/KnowledgeQuestionPath.v:100` `logic_self_grounded : parent SLogic = SLogic` — равенство, заданное
определением функции `parent`. Теоремы «L4 есть основание L4» ни там, ни там нет. Честно довести можно только до
`L4_form_is_L2_form`: формальное содержание L4 в записи совпадает с содержанием L2.

**(б) Поправить слова:**

> … в § 3.5 «Закон Достаточного Основания (L4)» было показано, как $L4$ записан в Rocq: его формальная запись
> получена из самой записи различия, из поля `exclusive`, без обращения к чему-либо внешнему. Содержательно это
> читается как *самообоснование* — закон достаточного основания обосновывает сам себя.

Слова стр. 1489–1491 («основанием $L4$ является … поле `exclusive` в записи `Distinction`») с доказательством
согласны и в ведомости записаны как ok.

## Расхождение 4. `self_application_not_self_membership` — два вычисления над двумя таблицами (стр. 1390–1396)

**Было:**

> теорема `self_application_not_self_membership` разделяет два смысла «E/R/R применяется к себе». Это
> *самоприменение* (стратифицированное самоописание, уровнем ниже), а *не* самочленство ($x \in x$, при котором
> $\mathrm{level}(S) < \mathrm{level}(S)$), запрещаемое $P1$; и потому оно $P1$-*совместимо*, а не исключение из
> неё.

**Проверка.** `src/foundation/PrinciplesToERR.v:59`:

```coq
Theorem self_application_not_self_membership :
  is_well_formed err_meta_system = true /\ is_well_formed russell_system = false.
Proof. split; [ exact err_self_well_formed | exact russell_ill_formed ]. Qed.
```

Closed under the global context. Запись `ERRSystem` (`ERRWellFormedness.v:39`) содержит число компонентов,
функцию категорий и таблицу ссылок; уровней и отношения принадлежности в ней нет. Таблица `russell_system`
отличается от «хорошей» одной клеткой: у неё задана ссылка компонента 0 на себя.

**В чём расхождение.** Теорема соединяет два вычисленных значения; о стратификации, уровнях, принадлежности и
$P1$ её утверждение не говорит.

**(а) Довести формализацию.** Возможно, без допущений: разделить два случая свойством, а не двумя вычислениями.
Свойство — «ссылки идут строго вниз по рангу категории» (Rule > Role > Element); ранг играет роль уровня.
Набросок проверен (`Check.v`; все — Closed under the global context):

```coq
Definition cat_rank (c : ERRCategory) : nat :=
  match c with Cat_Element => 0 | Cat_Role => 1 | Cat_Rule => 2 end.

Definition stratified (E : ERRSystem) : Prop :=
  forall i j, i < errs_n_components E -> j < errs_n_components E ->
    errs_references E i j = true ->
    cat_rank (errs_category E j) < cat_rank (errs_category E i).

Definition ref_rel (E : ERRSystem) (a b : nat) : Prop :=
  a < errs_n_components E /\ b < errs_n_components E /\ errs_references E a b = true.

Theorem stratified_well_formed :
  forall E : ERRSystem, stratified E -> is_well_formed E = true.

(* ни прямой, ни опосредованной самореференции *)
Theorem stratified_no_reference_cycle :
  forall E : ERRSystem, stratified E -> forall k, ~ clos_trans nat (ref_rel E) k k.

Theorem self_reference_not_stratified :
  forall (E : ERRSystem) (k : nat),
    k < errs_n_components E -> errs_references E k k = true -> ~ stratified E.

Theorem self_application_vs_self_membership :
  stratified err_meta_system /\
  (forall k, ~ clos_trans nat (ref_rel err_meta_system) k k) /\
  ~ stratified russell_system /\
  ref_rel russell_system 0 0.
```

Доказательства короткие: `stratified_well_formed` — через точное содержание критерия (`is_well_formed_spec`,
расхождение 6); отсутствие циклов — индукцией по транзитивному замыканию (ранг вдоль цепочки ссылок строго убывает);
для конкретных таблиц — разбором компонентов. Полный текст — в `Check.v`. С такой теоремой слова
«стратифицированное самоописание» и «не самочленство» получают формальную опору; запрет ссылки на себя оказывается
той же иррефлексивностью строгого порядка, что и $P1$.

**(б) Поправить слова** (если формализацию не трогать):

> Существенно, чем именно: теорема `self_application_not_self_membership` ставит рядом две записи — таблицу
> самоприменения E/R/R, которая критерий проходит, и таблицу Рассела, в которой компонент ссылается на самого себя
> и которая критерия не проходит. Содержательно это два смысла «E/R/R применяется к себе»: *самоприменение*
> (стратифицированное самоописание, уровнем ниже), а *не* самочленство ($x \in x$, при котором
> $\mathrm{level}(S) < \mathrm{level}(S)$), запрещаемое $P1$; и потому оно $P1$-*совместимо*, а не исключение из
> неё. Уровней в записи `ERRSystem` нет, так что связь с $P1$ здесь содержательная, а не доказанная.

## Расхождение 5. Таблица `err_meta_system` не совпадает с разбором, который она «фиксирует» (стр. 1396–1398, 1472–1475)

**Было:**

> (1396–1398) Самосогласованность E/R/R доказана отдельной Rocq-теоремой, без аксиом; содержательный разбор ниже
> разворачивает то, что эта теорема фиксирует.
>
> (1472–1475) Самосогласованность E/R/R доказана машинно (`err_self_well_formed`, `PrinciplesToERR.v`; см.
> замечание выше); содержательная проверка по критерию `ERRWellFormedness.v` с ней согласна: самоприменение E/R/R
> *не обнаруживает структурного нарушения* по тем же признакам (самореференция, смешение категорий), по которым
> формально диагностируются парадоксальные системы. Это содержательное свидетельство в пользу того, что E/R/R
> годится как универсальная онтология систем; сама же самосогласованность — доказанная в Rocq теорема.

**Проверка.** `src/foundation/PrinciplesToERR.v:45–54`:

```coq
Definition err_meta_system : ERRSystem := mkERRSys 3
  (fun i => match i with
            | 0%nat => Cat_Element
            | 1%nat => Cat_Role
            | _     => Cat_Rule
            end)
  (fun i j => (Nat.eqb i 2 && Nat.eqb j 1) || (Nat.eqb i 1 && Nat.eqb j 0)).

Theorem err_self_well_formed : is_well_formed err_meta_system = true.
Proof. vm_compute. reflexivity. Qed.
```

Closed under the global context; цена на странице («без аксиом») названа верно. В таблице три компонента: один
помечен `Cat_Element`, один `Cat_Role`, один `Cat_Rule`; ссылки — правило → роль, роль → элемент.

Разбор страницы (стр. 1402–1437) расставляет иначе: элементов три — категории «Elements», «Roles», «Rules»
(«Эти три аспекта — сами Elements»); ролей три («носитель субстрата», «носитель функциональных позиций», «носитель
организующих законов»); правил — универсальный слой и три конкретных. На стр. 1459–1461 сказано прямо: «Каждая из
трёх категорий … относится ровно к одной E/R/R-категории в самоприменении (как Element в нашем разборе)». В таблице
же категория «Roles» помечена ролью, категория «Rules» — правилом.

Признака «смешение категорий» у критерия нет (расхождения 6 и 8).

**В чём расхождение.** Машинно проверена таблица, расставленная иначе, чем разбор; свойства «самосогласованность
E/R/R» в формализации нет — доказано, что одна записанная рукой таблица проходит вычислимую проверку.

**(а) Довести формализацию.** Возможно: записать таблицу по разбору страницы. Набросок проверен (`Check.v`,
Closed): три элемента (0, 1, 2), три роли (3, 4, 5), три конкретных правила (6, 7, 8); роль 3+k исполняет
элемент k; правила задают роли.

```coq
Definition err_self_application_system : ERRSystem := mkERRSys 9
  (fun i => match i with
            | 0 | 1 | 2 => Cat_Element
            | 3 | 4 | 5 => Cat_Role
            | _ => Cat_Rule
            end)
  (fun i j =>
     ((3 <=? i) && (i <=? 5) && (j =? i - 3))
     || ((6 <=? i) && (i <=? 8) && (3 <=? j) && (j <=? 5))).

Lemma err_self_application_well_formed :
  is_well_formed err_self_application_system = true /\
  is_well_formed_strict err_self_application_system = true.
Theorem err_self_application_stratified : stratified err_self_application_system.
```

Какие ссылки считать верными для разбора, решает автор; набросок показывает, что таблица, отвечающая разбору,
критерий проходит и стратифицирована (нет ни прямой, ни опосредованной самореференции).

**(б) Поправить слова:**

> (1396–1398) Что таблица самоприменения проходит критерий, доказано отдельной Rocq-теоремой, без аксиом. Таблица
> в этой теореме краткая — три компонента, по одному на категорию, со ссылками правило → роль → элемент;
> содержательный разбор ниже подробнее и расставляет иначе: три категории выступают в нём элементами.
>
> (1472–1475) Что таблица самоприменения проходит критерий, доказано машинно (`err_self_well_formed`,
> `PrinciplesToERR.v`; см. замечание выше); содержательная проверка по критерию `ERRWellFormedness.v` с этим
> согласна: самоприменение E/R/R *не обнаруживает структурного нарушения* по тем же признакам (ссылка компонента на
> себя, ссылка правила на правило), по которым формально диагностируются парадоксальные системы. Это содержательное
> свидетельство в пользу того, что E/R/R годится как универсальная онтология систем; машинно же доказано
> прохождение критерия записанной таблицей.

## Расхождение 6. Критерий `is_well_formed` описан не так, как записан (стр. 1452–1454; сноска 17, стр. 2172)

**Было:**

> (1452–1454) зафиксирован критерий: система *хорошо сформирована*, если каждый её компонент относится ровно к
> одной E/R/R-категории и нет *самореференции* через категории.[^17]
>
> [^17]: Точные формулировки `no_self_reference` и `rules_above_elements` разбираются в «Парадоксы как смешение
> E/R/R-категорий».

**Проверка.** `src/foundation/ERRWellFormedness.v:61–98`: `no_self_reference` перебирает компоненты и возвращает
`false`, если `errs_references S k k`; `rules_above_elements` для каждого компонента-правила перебирает компоненты и
возвращает `false`, если правило ссылается на компонент-правило; `is_well_formed S := no_self_reference S &&
rules_above_elements S`. Точное содержание доказано в пробном файле (Closed under the global context):

```coq
Theorem is_well_formed_spec :
  is_well_formed E = true <->
  (forall k, k < errs_n_components E -> errs_references E k k = false) /\
  (forall i j, i < errs_n_components E -> j < errs_n_components E ->
     errs_category E i = Cat_Rule -> errs_references E i j = true ->
     errs_category E j <> Cat_Rule).
```

Следствия (`Check.v`, все — Closed):

```coq
(* взаимная ссылка двух компонентов проходит проверку *)
Definition two_cycle_system : ERRSystem :=
  mkERRSys 2 (fun _ => Cat_Element) (fun i j => negb (i =? j)).
Lemma two_cycle_well_formed : is_well_formed two_cycle_system = true.

(* элемент, ссылающийся на правило, проходит проверку *)
Lemma element_refers_rule_well_formed : is_well_formed element_refers_rule = true.

(* правило, ссылающееся на ДРУГОЕ правило: самореференции нет, проверка даёт false *)
Lemma rule_refers_other_rule_ill_formed :
  no_self_reference rule_refers_other_rule = true /\
  is_well_formed rule_refers_other_rule = false.
```

В разделе «Парадоксы как смешение E/R/R-категорий» (стр. 1866–2152) имена `no_self_reference` и
`rules_above_elements` не встречаются, формулировок там нет; на странице эти имена стоят только в сноске 17.

**В чём расхождение.** Описанное условие («нет самореференции через категории») и записанное (нет ссылки
компонента на себя; правило не ссылается на правило) — разные: самореференцию через посредника код не замечает, а
ссылку одного правила на другое запрещает, о чём страница не говорит. Обещанного сноской разбора формулировок на
странице нет.

**(а) Довести формализацию.** Возможно, двумя путями; оба проверены, допущений нет.

*Свойство стратификации* (расхождение 4): ссылки идут строго вниз по рангу категории. Оно влечёт нынешний критерий
(`stratified_well_formed`) и исключает циклы ссылок любой длины (`stratified_no_reference_cycle`); цикл длины 2 им
отвергается (`two_cycle_not_stratified`).

*Вычислимый критерий без циклов:*

```coq
Fixpoint reach (E : ERRSystem) (fuel i j : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if errs_references E i j then true
    else existsb (fun k => if errs_references E i k then reach E f k j else false)
                 (seq 0 (errs_n_components E))
  end.

Definition acyclic (E : ERRSystem) : bool :=
  forallb (fun k => negb (reach E (errs_n_components E) k k))
          (seq 0 (errs_n_components E)).

Definition is_well_formed_strict (E : ERRSystem) : bool :=
  acyclic E && rules_above_elements E.

Theorem acyclic_no_self_reference :
  forall E : ERRSystem, acyclic E = true -> no_self_reference E = true.
Theorem strict_implies_well_formed :
  forall E : ERRSystem, is_well_formed_strict E = true -> is_well_formed E = true.
```

На семи таблицах файлов он даёт тот же ответ, что нынешний (`nat_system`, `chess_system`, `err_meta_system`,
`distinction_meta_system` — `true`; `russell_system`, `liar_system`, `grelling_system` — `false`), а цикл длины 2
отвергает (`strict_examples`). Равносильность `reach` существованию цепочки ссылок не доказывалась.

В любом случае в `ERRWellFormedness.v` стоит добавить `is_well_formed_spec` — тогда содержание проверки будет
теоремой, а не чтением кода.

**(б) Поправить слова:**

> (1452–1454) зафиксирован критерий: система *хорошо сформирована*, если каждый её компонент относится ровно к
> одной E/R/R-категории, ни один компонент не ссылается на самого себя и ни одно правило не ссылается на
> правило.[^17]
>
> [^17]: В коде это два условия: `no_self_reference` — ни у одного компонента $k$ нет ссылки $k \to k$;
> `rules_above_elements` — компонент-правило не ссылается на компонент-правило. Первое требование (одна категория
> у компонента) выполнено самим представлением: категория задана функцией. Самореференция через посредника
> (взаимная ссылка двух компонентов) этими условиями не проверяется.

## Расхождение 7. `every_distinction_err_well_formed`: квантор по различиям без вхождения переменной (стр. 1685–1686)

**Было:** «а `every_distinction_err_well_formed` распространяет это на всякий такой разбор.»

**Проверка.** `src/foundation/PrinciplesToERR.v:107–113`:

```coq
Theorem distinction_err_well_formed : is_well_formed distinction_meta_system = true.
Proof. vm_compute. reflexivity. Qed.

Theorem every_distinction_err_well_formed :
  forall _ : Distinction, is_well_formed distinction_meta_system = true.
Proof. intros _. exact distinction_err_well_formed. Qed.
```

Обе — Closed under the global context. Таблица `distinction_meta_system` (`:97`) — шесть компонентов (два
элемента, две роли, два правила), записана определением и от экземпляра различия не зависит. Равносильность двух
теорем (`Check.v`, Closed):

```coq
Lemma every_distinction_is_one_fact :
  (forall _ : Distinction, is_well_formed distinction_meta_system = true) <->
  is_well_formed distinction_meta_system = true.
```

**В чём расхождение.** Квантор по различиям стоит перед утверждением, в которое различие не входит: вторая
теорема повторяет первую.

**(а) Довести формализацию.** Возможно. Запись `ERRSystem` содержимого компонентов не хранит, поэтому связать
таблицу с экземпляром нужно отдельно: указать, что стоит в её компонентах для данного $D$. Набросок проверен
(`Check.v`, Closed under the global context):

```coq
Definition distinction_content (D : Distinction) (i : nat) : Prop :=
  match i with
  | 0 => Distinction.positive D
  | 1 => negative D
  | 4 => ~ (Distinction.positive D /\ negative D)
  | 5 => Distinction.positive D \/ negative D
  | _ => True
  end.

Theorem every_distinction_typed : forall D : Distinction,
  is_well_formed distinction_meta_system = true /\
  [distinction_content D 0; distinction_content D 1] = err_elements D /\
  (forall i, i < 6 -> errs_category distinction_meta_system i = Cat_Rule ->
     distinction_content D i).
Proof.
  intro D. split; [exact distinction_err_well_formed | split; [reflexivity |]].
  intros i Hi Hc.
  destruct i as [|[|[|[|[|[|i]]]]]]; simpl in *; try discriminate Hc; try lia.
  - exact (exclusive D).
  - exact (exhaustive D).
Qed.
```

Здесь экземпляр входит в утверждение: компоненты-элементы таблицы суть `err_elements D`, а компоненты-правила —
утверждения, истинные для $D$ по его полям. Таблица стратифицирована (`distinction_meta_stratified`, Closed).

**(б) Поправить слова:**

> … и теорема `distinction_err_well_formed` машинно подтверждает, что она проходит критерий `is_well_formed`.
> Таблица одна для всех различий: она описывает схему записи и от экземпляра не зависит
> (`every_distinction_err_well_formed` повторяет то же утверждение под квантором по различиям).

## Расхождение 8. «Одна сущность в двух категориях» в записи невыразима; проверяется ссылка компонента на себя (стр. 1906–1910)

**Было:**

> Парадоксы — именно те конструкции, для которых такой разбор *невозможен*: одна и та же сущность пытается
> одновременно занимать места разных категорий. Это — структурное нарушение, которое формализуется в Rocq и
> проверяется машинно.[^18]

**Проверка.** В записи `ERRSystem` категория компонента — значение функции `errs_category : nat -> ERRCategory`
(`ERRWellFormedness.v:41`); страница сама отмечает это на стр. 1666–1669: «двух категорий у одного компонента быть
не может». Три таблицы парадоксов (`:113`, `:122`, `:127`):

```coq
Definition russell_system : ERRSystem := mkERRSys 2
  (fun i => match i with 0%nat => Cat_Element | _ => Cat_Rule end)
  (fun i j => (i =? 0)%nat && (j =? 0)%nat).
Definition liar_system : ERRSystem := mkERRSys 1
  (fun _ => Cat_Element) (fun i j => (i =? 0)%nat && (j =? 0)%nat).
Definition grelling_system : ERRSystem := mkERRSys 1
  (fun _ => Cat_Rule) (fun i j => (i =? 0)%nat && (j =? 0)%nat).
```

У каждой задана ссылка компонента 0 на себя. В `russell_system` «R как элемент» и «R как правило» — два разных
компонента; второй ни на что не ссылается. В пробном файле доказано (все — Closed under the global context):

```coq
(* ссылка компонента 0 на себя даёт false при любой расстановке категорий *)
Theorem diagonal_alone_decides :
  forall (n : nat) (cat : nat -> ERRCategory) (refs : nat -> nat -> bool),
    refs 0 0 = true -> is_well_formed (mkERRSys (S n) cat refs) = false.

(* компонент «R как правило» в проверке не участвует *)
Lemma russell_rule_component_inert :
  forall cat : nat -> ERRCategory,
    is_well_formed (mkERRSys 2 cat (fun i j => (i =? 0) && (j =? 0))) = false.

(* что различают сами записи: категорию компонента, ссылающегося на себя *)
Lemma paradox_records_two_kinds : forall p : ParadoxType,
  self_ref_categories (paradox_system p) =
  match p with
  | Paradox_Grelling | Paradox_BuraliForti => [Cat_Rule]
  | _ => [Cat_Element]
  end.
```

**В чём расхождение.** Диагноз страницы — совмещение категорий одной сущностью; формальная проверка обнаруживает
другое — ссылку компонента на себя, заданную при записи таблицы, — а совмещение категорий в записи `ERRSystem`
выразить нельзя.

**(а) Довести формализацию.** Возможно, добавлением записи, в которой компонент может выступать в нескольких
категориях. Набросок проверен (`Check.v`, Closed under the global context):

```coq
Record ERRSystemM := mkERRSysM {
  m_n : nat;
  m_plays : nat -> ERRCategory -> bool;   (* компонент k выступает в категории c *)
  m_refs : nat -> nat -> bool
}.

Definition unmixed (E : ERRSystemM) : Prop :=
  forall k, k < m_n E -> forall c1 c2,
    m_plays E k c1 = true -> m_plays E k c2 = true -> c1 = c2.

(* нынешние записи вкладываются и смешения не содержат — ни одна, включая russell_system *)
Theorem every_ERRSystem_unmixed : forall E : ERRSystem, unmixed (embed E).

(* «Element = Rule» буквально: один компонент в двух категориях *)
Definition russell_mixed : ERRSystemM :=
  mkERRSysM 1 (fun _ c => match c with Cat_Role => false | _ => true end) (fun _ _ => true).
Lemma russell_mixed_is_mixed : ~ unmixed russell_mixed.
```

В такой записи «Element = Rule» становится проверяемым свойством таблицы, и первое условие критерия («каждый
компонент — ровно в одной категории») перестаёт выполняться автоматически. Какой из двух признаков — совмещение
категорий или ссылку на себя — считать диагнозом, решает автор.

**(б) Поправить слова** (если формализацию не трогать):

> Парадоксы — именно те конструкции, для которых такой разбор *невозможен*: одна и та же сущность пытается
> одновременно занимать места разных категорий. В Rocq это структурное нарушение представлено его следом — ссылкой
> компонента на самого себя: в записи `ERRSystem` у компонента одна категория, и совмещение категорий передаётся
> тем, что компонент указывает на себя; наличие такой ссылки проверяется машинно.[^18]

## Расхождение 9. «Все классические парадоксы» — пять имён, три записи (сноска 18, стр. 2173)

**Было:** «Главная теорема `all_paradoxes_ill_formed` устанавливает, что все классические парадоксы — структурно
ill-formed.»

**Проверка.** `src/foundation/ParadoxDiagnosis.v:32`, `:79`, `:109`:

```coq
Inductive ParadoxType :=
  | Paradox_Russell | Paradox_Liar | Paradox_Grelling | Paradox_Cantor | Paradox_BuraliForti.

Definition paradox_system (p : ParadoxType) : ERRSystem :=
  match p with
  | Paradox_Russell => russell_system
  | Paradox_Liar => liar_system
  | Paradox_Grelling => grelling_system
  | Paradox_Cantor => russell_system
  | Paradox_BuraliForti => grelling_system
  end.

Theorem all_paradoxes_ill_formed : forall p : ParadoxType,
  is_well_formed (paradox_system p) = false.
```

Closed under the global context. Квантор — по перечислению из пяти имён; записей три. Страница на стр. 1917
относит к структурным ещё парадоксы Берри, Ричарда, Карри, Ябло; в сноске 19 говорится о 46 классических
парадоксах.

**В чём расхождение.** Утверждение о пяти записанных именах пересказано как утверждение обо всех классических
парадоксах. В основном тексте (стр. 2074–2084) сказано точно — «все пять разобранных».

**(а) Довести формализацию.** До «всех» — нельзя: теорема говорит о тех таблицах, которые записаны. Перечисление
можно расширять, записывая таблицу для каждого парадокса. Для парадокса Ябло (последовательность высказываний,
каждое из которых говорит о последующих) самореференции в таблице ссылок нет, и критерий, основанный на ссылках, —
ни нынешний, ни без циклов — такую таблицу не отвергнет; это не проверялось, таблица не строилась.

**(б) Стало:**

> Главная теорема `all_paradoxes_ill_formed` устанавливает, что записи всех пяти разобранных парадоксов —
> структурно ill-formed.

## Расхождение 10. `P1_blocks_russell` — иррефлексивность порядка уровней (сноска 20, стр. 2175)

**Было:** «В `PrinciplesFromLaws.v` («$P1$: иерархия») есть также отдельная теорема `P1_blocks_russell`,
фиксирующая, что $P1$ блокирует конструкцию Рассела.»

**Проверка.** `src/foundation/PrinciplesFromLaws.v:43–52`:

```coq
Theorem P1_from_L1_L5 : forall l : Level, ~ (l << l).
Proof. exact level_lt_irrefl. Qed.

Theorem P1_no_self_membership : forall l : Level, ~ (l << l).
Proof. exact P1_from_L1_L5. Qed.

Theorem P1_blocks_russell : forall l : Level, ~ (l << l).
Proof. exact level_lt_irrefl. Qed.
```

Все — Closed under the global context. Три теоремы и `L5_hierarchy` (`LawsFromDistinction.v:111`) — одно
утверждение под четырьмя именами. О конструкции Рассела говорят другие теоремы:

```coq
(* TheoryOfSystems_Core_ERR.v:248 — только для L2 *)
Theorem russell_paradox_blocked :
  ~ exists (C : Criterion L2), crit_domain L2 C = System L2 /\ crit_level_witness L2 C = L2.
(* foundation/TransfiniteInductionLevel.v:96, :109 *)
Theorem criterion_label_never_own_level :
  forall (L : Level) (C : Criterion L), crit_level_witness L C <> L.
Theorem russell_blocked_every_level :
  forall (L : Level) (mem : System L -> System L -> Prop),
    ~ exists R : System L, forall X : System L, mem X R <-> ~ mem X X.
```

Все — Closed.

**В чём расхождение.** Теорема, названная в сноске, не содержит конструкции Рассела: это само $P1$ в форме
иррефлексивности порядка.

**(а) Довести формализацию.** Не требуется: нужные теоремы есть (добавлены в ноябре 2026). Замечание к выбору
имени: `criterion_label_never_own_level` опирается на $P2$ и иррефлексивность — это и есть формальная форма слов
«$P1$ блокирует»; `russell_blocked_every_level` — диагональ, уровней не использующая (так сказано и в комментарии
файла, `:105–108`).

**(б) Стало:**

> [^20]: Само $P1$ записано в `PrinciplesFromLaws.v` («$P1$: иерархия») как иррефлексивность порядка уровней
> (`P1_from_L1_L5`; то же утверждение стоит там под именем `P1_blocks_russell`). Собственно о конструкции Рассела —
> теоремы файла `TransfiniteInductionLevel.v`: `criterion_label_never_own_level` (метка уровня у области критерия
> не бывает собственным уровнем критерия) и `russell_blocked_every_level` (ни на каком уровне нет системы,
> собирающей в точности те системы этого уровня, что не принадлежат себе).

## Расхождение 11. `paradox_diagnosis_synthesis`: «точная классификация нарушений для каждого парадокса» (сноска 23, стр. 2178)

**Было:** «Полный синтез — в теореме `paradox_diagnosis_synthesis`, объединяющей: (1) ill-formed-статус всех
парадоксов; (2) контрапозитив `well_formed_paradox_free`; (3) точную классификацию нарушений для каждого парадокса.»

**Проверка.** `src/foundation/ParadoxDiagnosis.v:148`:

```coq
Theorem paradox_diagnosis_synthesis :
  (forall p, is_well_formed (paradox_system p) = false) /\
  (forall S, is_well_formed S = true -> forall p, S <> paradox_system p) /\
  paradox_violation Paradox_Russell = Violation_ElementIsRule /\
  paradox_violation Paradox_Liar = Violation_SelfApplication /\
  paradox_violation Paradox_Grelling = Violation_RuleIsElement.
```

Closed under the global context. Третья часть — три равенства (для Кантора и Бурали-Форти равенств нет); каждое
доказано `reflexivity` на определении (`:57`):

```coq
Definition paradox_violation (p : ParadoxType) : ViolationType :=
  match p with
  | Paradox_Russell => Violation_ElementIsRule
  | Paradox_Liar => Violation_SelfApplication
  | Paradox_Grelling => Violation_RuleIsElement
  | Paradox_Cantor => Violation_SystemSelfMember
  | Paradox_BuraliForti => Violation_TotalitySelfMember
  end.
```

`ViolationType` — перечисление из пяти названий; с записью `ERRSystem` оно ничем не связано. Доказано (`Check.v`,
Closed):

```coq
Lemma violation_not_determined_by_system :
  exists p q : ParadoxType,
    paradox_system p = paradox_system q /\ paradox_violation p <> paradox_violation q.
```

**В чём расхождение.** «Классификация» в теореме — три строки таблицы, записанной определением, а не вывод вида
нарушения из устройства системы; и строк три, а не пять.

**(а) Довести формализацию.** Пять видов из трёх записей вывести нельзя: одной записи отвечают два вида
(`violation_not_determined_by_system`). Сами записи различают два случая — на себя ссылается элемент (Рассел,
Лжец, Кантор) или правило (Грелинг, Бурали-Форти): `paradox_records_two_kinds` (расхождение 8). Чтобы вид
нарушения стал теоремой, нужны пять различных таблиц и функция, вычисляющая вид нарушения по таблице (например, в
записи `ERRSystemM` расхождения 8 — по тому, какие категории совмещены); тогда равенства третьей части будут
вычислением по устройству системы, а не чтением определения.

**(б) Стало:**

> [^23]: Сводная теорема `paradox_diagnosis_synthesis` объединяет: (1) ill-formed-статус записей всех пяти
> парадоксов; (2) контрапозитив `well_formed_paradox_free`; (3) для Рассела, Лжеца и Грелинга — значения таблицы
> `paradox_violation`, сопоставляющей парадоксу вид нарушения. Таблица видов нарушений задана определением; с
> записями систем теоремы её не связывают.

## Расхождение 12. `well_formed_paradox_free`: «исключает парадоксальность» (стр. 2098–2100)

**Было:** «Это зафиксировано теоремой `well_formed_paradox_free`: хорошая сформированность *исключает*
парадоксальность.»

**Проверка.** `src/foundation/ParadoxDiagnosis.v:120`:

```coq
Theorem well_formed_paradox_free : forall S,
  is_well_formed S = true ->
  forall p : ParadoxType, S <> paradox_system p.
Proof.
  intros S HS p Heq. subst S.
  rewrite all_paradoxes_ill_formed in HS. discriminate.
Qed.
```

Closed under the global context. Утверждение: система, проходящая проверку, не равна ни одной из трёх записанных
таблиц. Первая фраза абзаца («она не может совпадать ни с одной из парадоксальных конструкций») передаёт его точно и
записана как ok. Свойства «быть парадоксальной» в формализации нет. Взаимная ссылка двух компонентов проверку
проходит (`two_cycle_well_formed`, расхождение 6).

**В чём расхождение.** Несовпадение с тремя записанными таблицами пересказано как исключение парадоксальности
вообще.

**(а) Довести формализацию.** До «исключает парадоксальность» — нельзя, пока парадоксальность не определена. Общее
утверждение, не привязанное к таблицам, доказуемо для стратификации (`stratified_no_reference_cycle`, расхождение 4):
стратифицированная система не содержит самореференции — ни прямой, ни через посредников. Для нынешнего критерия
общее утверждение уже есть в файле: `well_formed_no_self_ref` (`ERRWellFormedness.v:151`) — проходящая проверку
система не содержит прямой ссылки компонента на себя.

**(б) Стало:**

> Это зафиксировано теоремой `well_formed_paradox_free`: хорошая сформированность *исключает* совпадение с любой
> из записанных парадоксальных конструкций.

## Расхождение 13. `nat_well_formed`, `chess_well_formed`: таблицы без ссылок (сноски 24 и 25, стр. 2179–2180)

**Было:**

> [^24]: Это зафиксировано в `ERRWellFormedness.v` теоремой `nat_well_formed`: формальное представление натуральных
> чисел как `ERRSystem` проходит проверку `is_well_formed`.
>
> [^25]: Теорема `chess_well_formed`.

**Проверка.** `src/foundation/ERRWellFormedness.v:105`, `:135`, `:172`, `:180`:

```coq
Definition nat_system : ERRSystem := mkERRSys 3
  (fun i => match i with 0%nat => Cat_Element  (* 0 *)
                       | 1%nat => Cat_Rule     (* successor S *)
                       | _ => Cat_Role         (* "is a nat" *)
            end)
  (fun _ _ => false).
Lemma nat_well_formed : is_well_formed nat_system = true.

Definition chess_system : ERRSystem := mkERRSys 4
  (fun i => match i with 0%nat => Cat_Element  (* pieces *)
                       | 1%nat => Cat_Element  (* squares *)
                       | 2%nat => Cat_Role     (* attacker/defender *)
                       | _ => Cat_Rule         (* movement rules *)
            end)
  (fun _ _ => false).
Lemma chess_well_formed : is_well_formed chess_system = true.
```

Обе леммы — Closed under the global context. В обеих таблицах ссылок нет вовсе. Доказано (`Check.v`, Closed):

```coq
Theorem no_references_well_formed :
  forall (n : nat) (cat : nat -> ERRCategory),
    is_well_formed (mkERRSys n cat (fun _ _ => false)) = true.
```

Расстановка в `nat_system` расходится и с разбором страницы (стр. 2120–2122): на странице элементы — числа
$1, 2, 3, …$, роли — «единица» и «преемник», правила — правила построения; в записи — один элемент «0», правило
«преемник», роль «быть числом».

**В чём расхождение.** Таблица без ссылок проходит проверку при любом числе компонентов и любой расстановке
категорий; леммы фиксируют расстановку меток, а о натуральных числах и о шахматах ничего не утверждают.

**(а) Довести формализацию.** Возможно: записать в таблицах ссылки. Набросок для натуральных чисел проверен
(`Check.v`, Closed): правило «преемник» ссылается на элемент и на роль, роль — на элемент.

```coq
Definition nat_system_refs : ERRSystem := mkERRSys 3
  (fun i => match i with 0 => Cat_Element | 1 => Cat_Rule | _ => Cat_Role end)
  (fun i j => ((i =? 1) && ((j =? 0) || (j =? 2))) || ((i =? 2) && (j =? 0))).

Lemma nat_system_refs_well_formed :
  is_well_formed nat_system_refs = true /\ is_well_formed_strict nat_system_refs = true.
Theorem nat_system_refs_stratified : stratified nat_system_refs.
```

Тогда проверка содержательна: правило ссылается только вниз, самореференции нет. Для шахмат — так же (правила
ходов ссылаются на роли, роли — на фигуры и клетки). Расстановку и состав ссылок задаёт автор.

**(б) Стало:**

> [^24]: В `ERRWellFormedness.v` натуральные числа записаны как `ERRSystem` из трёх компонентов (элемент, правило
> «преемник», роль) без ссылок между ними; лемма `nat_well_formed` подтверждает, что такая запись проходит
> `is_well_formed`. Запись без ссылок проходит проверку всегда, так что лемма фиксирует расстановку категорий.
>
> [^25]: Лемма `chess_well_formed` — то же для записи из четырёх компонентов (фигуры, клетки, роль, правила ходов)
> без ссылок.

## Расхождение 14. «Отличает … точно и формально» (стр. 2139–2144)

**Было:**

> E/R/R-диагностика отличает парадоксы от хорошо сформированных систем точно и формально. Парадоксы выявляются как
> ill-formed автоматически (Rocq компилирует и проверяет); хорошо сформированные системы — от арифметики до игр —
> проходят проверку. Это — систематический критерий, не зависящий от частных особенностей рассматриваемой
> структуры.

**Проверка.** Формально установлено: три записанные таблицы дают `false` (`russell_system`, `liar_system`,
`grelling_system`), четыре — `true` (`nat_system`, `chess_system`, `err_meta_system`, `distinction_meta_system`).
Утверждения «конструкция парадоксальна тогда и только тогда, когда её таблица не проходит проверку» в формализации
нет. Для нынешнего критерия оно не выполняется ни в одну сторону (расхождение 6): взаимная ссылка двух компонентов
проверку проходит; ссылка правила на другое правило, без самореференции, — не проходит. Вычисление автоматическое
(`vm_compute`); сами таблицы — и ссылка компонента на себя у парадоксов, и пустые таблицы ссылок у арифметики и
шахмат — записаны рукой.

**В чём расхождение.** Семь вычислений над записанными таблицами пересказаны как точное разделение парадоксов и
хорошо сформированных систем.

**(а) Довести формализацию.** До «точно» — нельзя: парадоксальность в формализации не определена, а для нынешнего
критерия есть примеры в обе стороны. Доказуемо достаточное условие (расхождение 4): стратифицированная система
проходит критерий и не содержит самореференции никакой длины; система со ссылкой компонента на себя не
стратифицирована.

**(б) Стало:**

> Для записанных конструкций E/R/R-диагностика различает парадоксы и хорошо сформированные системы формально.
> Записи парадоксов выявляются как ill-formed вычислением (Rocq компилирует и проверяет); записи хорошо
> сформированных систем — от арифметики до игр — проходят проверку. Критерий систематичен в том смысле, что ко
> всякой таблице «компоненты — категории — ссылки» применяется одинаково; саму таблицу для данной конструкции
> составляет исследователь.

## Сомнительные места (не расхождения)

1. **Стр. 1037–1038, 1053–1066, «Элементы системы уровня $n+1$ суть сами системы уровня $n$»; «иерархия —
   следствие $L5$ и $P1$».** О Rocq здесь не говорится. В формализации элементы функциональной системы — значения
   произвольного типа `fs_domain` с назначенной меткой уровня; что элементы суть системы, не записано (в
   `TheoryOfSystems_Core_ERR.v:1674` это комментарий: «Products(L) = Elements(L+1)»). Тип `Level` и порядок на нём
   определены независимо, а «L5» и «P1» — имена свойств этого порядка: в Rocq иерархия дана определением, а не
   получена из $L5$ и $P1$.
2. **Стр. 1083, уровень элемента.** Слова страницы соответствуют полю `fs_level_valid` записи `FunctionalSystem`
   (ok). Это требование, встроенное в запись; метка уровня у элемента назначается полем и элементом не определяется
   (`element_label_is_assigned`: одни и те же элементы с меткой `L1` и с меткой `L2`). В записи `System L` метка
   одна на критерий и с областью не связана (`label_not_determined_by_domain`).
3. **Стр. 1082, 1099–1107, 1168–1182, 1537–1544, формальный уровень `L1`.** `System L1` пуст, у
   `FunctionalSystem L1` нет элементов (`no_system_at_L1`, `functional_system_L1_has_no_elements`): на формальном
   `L1` систем с элементами нет; в примере `nat_gt_5_criterion : Criterion L2` метка области — `L1`. На
   стр. 1099–1107 страница оставляет обозначение $L_1$ за формальным уровнем («Логика / основание»), а на
   стр. 1169–1174 называет $L_1$ уровнем натуральных чисел, частиц, символов — то есть первым доменным ярусом.
   Слова о `Distinction` как «системе уровня основания» страница сама называет интерпретацией.
4. **Стр. 1194–1196, «нет Логики и Источника как элементов некоторой мета-системы».** Объекта `Absolute` нет.
   Логика и Источник в формализации названы: `Inductive Sys := SLogic | SSource | SLight | SNest n` и функция
   `parent` в `foundation/KnowledgeQuestionPath.v:74–86` (`source_inside_logic : parent SSource = SLogic`,
   `logic_self_grounded : parent SLogic = SLogic` — оба по определению `parent`). Это перечисление с Логикой
   наверху, не мета-система с двумя элементами, так что слова страницы остаются верными; при правке можно
   упомянуть.
5. **Стр. 1942–1948, «было показано, что $P1$ … выводится из $L1 + L5$».** Отсылка в первую половину главы. К
   сведению: `P1_from_L1_L5` доказана как `exact level_lt_irrefl`, утверждение дословно совпадает с `L5_hierarchy`;
   $L1$ в доказательстве не участвует (расхождение 10).
6. **Стр. 1602–1652, два уровня чтения.** Оговорка страницы точна. В самой формализации расстановка двоякая: в
   `ERRFromDistinction.v` элементы — `positive D`, `negative D`; в шапке `Distinction.v` (`:5–21`) и в таблице
   `distinction_meta_system` `positive`/`negative` — роли, а элементы — «стороны». В `ERRFromDistinction.v` роли и
   правила представлены числами `err_role_count D := 2`, `err_rule_count D := 2`, не зависящими от $D$.
7. **Стр. 1597–1600, «ровно два элемента».** `distinction_has_two_elements` — длина списка из двух записей,
   `reflexivity`. Что две стороны различны, в формализации не доказано; доказуемо без допущений (`Check.v`:
   `sides_differ : forall D, Distinction.positive D <> negative D`, Closed).
8. **Стр. 1589–1592, `distinction_of` $(A)$.** Равенства `positive (distinction_of P) = P`,
   `negative (distinction_of P) = ~ P` (`co_constitution`) верны по определению; `Print Assumptions` показывает
   `classic` — через само определение `distinction_of`.
9. **Стр. 1706–1711, 1819–1838, «`distinction_of` хорошо сформирована».** Записи `ERRSystem` и теоремы для
   `distinction_of` в формализации нет; страница формального здесь не заявляет (в отличие от раздела о
   `Distinction`). Таблица по стр. 1809–1817 (три правила, две роли, два элемента) критерий проходит и
   стратифицирована (`Check.v`: `distinction_of_system_well_formed`, `distinction_of_system_stratified`). Слово
   «наследует» формального содержания не имеет: таблицы независимы.
10. **Стр. 2060–2065, Кантор и Бурали-Форти.** Страница называет обе конструкции эквивалентными расселовой;
    Бурали-Форти сопоставлена запись `grelling_system` (единственный компонент — правило), а не `russell_system`.
    Своих записей у двух парадоксов нет; диагнозы «System = Element», «Totality = Element» существуют только как
    названия конструкторов `ViolationType`.
11. **Стр. 2086–2095, унифицированная таблица.** Совпадает с определениями `paradox_violation` и
    `paradox_solution`; машинной проверкой страница её не называет (шапка `ParadoxDiagnosis.v` — называет). О
    `paradox_solution` в файле нет ни одной леммы.
12. **Стр. 2102–2109, связь парадоксов с $P1$–$P4$.** Теорем, связывающих $P2$ с Лжецом, $P3$ с пустыми
    системами в этом контексте, $P4$ с парадоксами бесконечности, названные файлы не содержат; страница их и не
    заявляет. `principles_err_correspondence` (`PrinciplesToERR.v:78`) — конъюнкция иррефлексивности порядка уровней
    и двух вычислений над `err_meta_system`; шапка файла сама называет это соответствием, а не выводом.
13. **«Теорема» и `Lemma`.** `liar_is_ill_formed`, `grelling_is_ill_formed`, `cantor_is_ill_formed`,
    `buraliforti_is_ill_formed`, `nat_well_formed`, `chess_well_formed` объявлены словом `Lemma`; страница называет
    их теоремами. Для Rocq это одно и то же.
14. **Пары одинаковых лемм.** `russell_ill_formed` и `russell_is_ill_formed`, `liar_ill_formed` и
    `liar_is_ill_formed`, `grelling_ill_formed` и `grelling_is_ill_formed` утверждают одно и то же
    (`paradox_system` раскрывается по определению); `cantor_is_ill_formed` и `buraliforti_is_ill_formed` — те же
    вычисления ещё раз. Из 11 `Qed` файла `ParadoxDiagnosis.v` различных вычислений о системах — три.

## Вне участка: шапки и состав файлов

Для сведения (на участке эти строки не цитируются):

- `foundation/ERRWellFormedness.v:6` — «STATUS: 12 Qed»; действительный счёт — 9. Шапка (`:14–16`) и заключительный
  комментарий (`:224–226`) говорят, что предикат «EXACTLY captures the criterion» и что доказано «well-formed
  systems are paradox-free»; точное содержание предиката — `is_well_formed_spec` (расхождение 6). Комментарий к
  `rules_above_elements` (`:71`) — «Rules don't reference Rules at same level»; уровней в записи нет, и имя
  определения («правила выше элементов») его содержанию не отвечает.
- `foundation/ParadoxDiagnosis.v:5` — «STATUS: 12 Qed»; действительный счёт — 11. Комментарии `:108`, `:173`,
  `:178`: «ALL known paradoxes», «EVERY paradox … (universal quantifier!)», «The unified table … is
  MACHINE-VERIFIED» — с теми же оговорками, что расхождения 9 и 11.
- `foundation/PrinciplesToERR.v:28` — «7 Qed, 0 axioms»: верно. Комментарий `:110` к
  `every_distinction_err_well_formed` — «The typing applies to EVERY distinction» (расхождение 7).
- `foundation/LawsFromDistinction.v:172` — `L3_independence : (forall D, positive D \/ negative D) -> forall P,
  P \/ ~ P`: посылка в доказательстве отбрасывается (`intros _ P. exact (classic P)`); `Print Assumptions` —
  `Axioms: Distinction.classic`. Без аксиомы доказуема равносильность `distinction_for_every_prop_iff_lem`
  (расхождение 2). Это участок главы 3.
- `foundation/Distinction.v:250` — `distinction_theorem_count := 22` при 20 `Qed`;
  `foundation/ERRFromDistinction.v:225` — `err_distinction_theorem_count := 22` при 17 `Qed`.
- `foundation/ERRFromDistinction.v:189` — `err_well_formed : forall D, length (err_elements D) = err_role_count D`
  (2 = 2, `reflexivity`) под комментарием «ERR is well-formed for any Distinction»: второе, не связанное с
  `is_well_formed`, употребление слов «хорошо сформирована». Это участок первой половины главы.

## Дополнительные проверки

- `Print Assumptions` снят для всех теорем, названных на участке, и для привлечённых к сверке (вывод сохранён в
  `status.txt`, `pa1.txt`, `pa2.txt` папки пробных доказательств). Отличны от «Closed under the global context»
  только `distinction_of`, `co_constitution`, `Law_of_ExcludedMiddle`, `L3_independence` и сама аксиома `classic`: во
  всех случаях `Axioms: Distinction.classic : forall P : Prop, P \/ ~ P`. Других имён в выводе компилятора нет.
- Блок кода участка (стр. 2077–2080, `all_paradoxes_ill_formed`) совпадает с исходником.
- Статусные оговорки страницы проверены и верны: раздел об Абсолюте не формализован (стр. 1193–1197); `Distinction`
  и `distinction_of` не размечены типом `Level` (стр. 1537–1544, 1744–1755); категория компонента задана функцией
  (стр. 1666–1669); доменные ярусы не суть формальные уровни (стр. 1095–1107).
- В пробном файле нет `Axiom`, `Parameter`, `Admitted`, библиотеки `Reals` и функциональной экстенсиональности.
