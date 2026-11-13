# Глава I.4 «E/R/R: онтология системы», первая половина (стр. 1–1029, сноски 1–11) — заметки к ведомости (13.11.2026)

Ведомость: `part01-ch04a.json` — 62 ручные записи; `merge --dry` проходит без замечаний (цитаты и объявления
найдены). В списке «без сверки» остаются только имена второй половины главы (стр. 1084 и далее, сноски 13–25).
Вердикты: ok — 42, mismatch-statement — 20. Расхождений цены, отсутствующих имён и неверных чисел на участке нет:
чисел `Qed`, файлов и аксиом участок не называет, кроме слов «обе фундаментальные аксиомы» в сноске 8.

Двадцать записей mismatch-statement относятся к восьми местам (расхождения 1–8).

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part01/ch04a/`:

- `Check.v` — 35 утверждений с `Print Assumptions` (вывод — `Check.out`): 33 — Closed under the global context;
  `complete_foundation_with_sides` — `classic` (ожидаемо: первый член); `choice_function_from_L4_witness` —
  `ToS_Axioms.L4_witness` (ожидаемо). Файл собирается.
- `PrinciplesNoLaws.v` — копия `PrinciplesFromLaws.v` без двух строк подключения (`foundation.Distinction`,
  `foundation.LawsFromDistinction`). Собирается; `four_principles_from_five_laws` — Closed.
- `CheckUniv.v`, `CheckUniv2.v`, `CheckUniv3.v` — три определения критерия с областью `Criterion L2` и
  `System L2`; все три Rocq отклоняет (universe inconsistency) — это и проверялось.

В `src` и в собранной копии ничего не менялось.

Участка касаются файлы: `foundation/Distinction.v` (20 `Qed`), `foundation/LawsFromDistinction.v` (22),
`foundation/PrinciplesFromLaws.v` (20), `foundation/ERRFromDistinction.v` (17), `TheoryOfSystems_Core_ERR.v` (36),
`Judgments.v` (23), `FormationRules.v` (18), `ToS_Axioms.v`. Копии в репозитории и в собранной папке совпадают
(SHA-1).

## Что проверить не удалось

- Отсылки к Главам 2, 3, 6 и к Части IV не сверялись. В частности, слова «минимальность записи `Distinction`,
  доказанная в Главе 2» (стр. 458–459) отсылают к рассуждению § 2.6; теоремы о необходимости полей в `Distinction.v`
  нет. Формальный вид этого утверждения проверен в `Check.v` (расхождение 7).
- Стр. 282–290 (конструкция действительных чисел без аксиом бесконечности и выбора): проверены определение
  `RealProcess` и состав объявленных в репозитории аксиом; цены теорем Части IV взяты из ведомостей `part04-*`,
  сами теоремы не перепроверялись.
- Статья, на которую ссылаются комментарии `PrinciplesFromLaws.v` («PROOF (from article)»,
  `Laws_of_Logic_Article.tex`), не смотрелась: сверялись только утверждения Rocq.
- Два утверждения о самом исчислении приняты как известные и компилятором не проверялись: что исключённое третье в
  Rocq без аксиомы не выводится (расхождение 2) и что неравенство двух экстенсионально равных предикатов в Rocq не
  доказуемо (сомнительные места, стр. 208–221).
- Примеры вне формализации (группа $\mathbb{Z}/n\mathbb{Z}$, грамматики, схема $S_c$) компилятором не проверялись;
  два замечания — в конце раздела «Сомнительные места».
- Английская страница не смотрелась. Вторая половина главы (стр. 1030–2155, сноски 12–25) записана в ведомости
  другого помощника.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Звено «законы → принципы» в утверждения теорем не входит (стр. 39–41; сноски 1 и 4)

**Было:**

> (39–41) Звенья $\text{Distinction} \to L1$–$L5$ и $L1$–$L5 \to P1$–$P4$ суть формальные теоремы Rocq (файлы
> `LawsFromDistinction.v` и `PrinciplesFromLaws.v`).
>
> (сноска 1) Формализация четырёх принципов и их деривация от законов содержится в файле `PrinciplesFromLaws.v`
> репозитория ToS-Coq; файл опирается на `Distinction.v`, `LawsFromDistinction.v` и `TheoryOfSystems_Core_ERR.v`.
>
> (сноска 4) … Также присутствует теорема `derivation_chain`, явно указывающая закон-источник для каждого принципа:
> $P1$ от $L1 + L5$; $P2$ от $L5$; $P3$ от $L1 + L4$; $P4$ от $L5$.

**Проверка.** Утверждения `src/foundation/PrinciplesFromLaws.v` (все — Closed under the global context):

| теорема | утверждение | из чего получено заключение |
|---|---|---|
| `P1_from_L1_L5` (:43) | `forall l : Level, ~ (l << l)` | `exact level_lt_irrefl`; дословно то же утверждение, что `L5_hierarchy` (`LawsFromDistinction.v:111`) |
| `P2_from_L5` (:91), `P2_structural` (:98) | `crit_level_witness L C << L` | поле `crit_level_valid` записи `Criterion` |
| `P3_reflexivity`, `P3_symmetry`, `P3_transitivity`, `P3_from_L1_L4` (:125–:155) | свойства `systems_intensionally_equal` | свойства равенства и определение отношения |
| `P4_from_L5` (:191), `P4_finite_at_each_stage` (:218) | значение `R n` есть `num # den` | разбор конструктора типа `Q` |
| `four_principles_from_five_laws` (:242) | конъюнкция четырёх утверждений | четыре предыдущих |
| `derivation_chain` (:262) | та же конъюнкция, дословно | `exact four_principles_from_five_laws` |

Ни одна из этих теорем не имеет закона в посылках. Теоремы `LawsFromDistinction.v` и определения `Distinction.v` в
доказательствах не используются: копия файла без строк

```coq
From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.LawsFromDistinction.
```

собирается без изменений в доказательствах (`PrinciplesNoLaws.v`), и `Print Assumptions
four_principles_from_five_laws` отвечает: Closed under the global context. Используются `level_lt_irrefl`,
`level_lt_trans`, `L1_lt_L2`, `P2_always_holds`, `crit_level_valid` из `TheoryOfSystems_Core_ERR.v` и `Qeq_dec` из
стандартной библиотеки.

Ход «закон → принцип» изложен в комментариях файла (по четыре-восемь шагов под заголовком «PROOF (from article)»).
О четвёртом принципе комментарий самого файла (:183–:190) говорит: «P4 is enforced by the CHOICE of nat -> Q … not
derived as a theorem». В `derivation_chain` закон-источник стоит в комментариях к членам; для $P1$ там назван один
$L5$ («L5 → P1», :263), а не $L1 + L5$.

**В чём расхождение.** Принципы записаны теоремами, но зависимость принципа от закона в утверждения не входит: она
стоит в именах теорем и в комментариях. Файл опирается на `TheoryOfSystems_Core_ERR.v`; два других файла он только
подключает.

**(а) Довести формализацию.** Для $P1$ возможно, без допущений: записать оба закона посылками и вывести отсутствие
самопринадлежности. Набросок проверен (`Check.v`; Closed under the global context); он повторяет шаги 4–7
комментария файла (:31–:39):

```coq
Section P1_Derived.
  Variable U : Type.                      (* системы *)
  Variable Lv : Type.                     (* уровни *)
  Variable lt : Lv -> Lv -> Prop.         (* порядок уровней *)
  Variable at_level : U -> Lv -> Prop.    (* «x расположено на уровне l» *)
  Variable mem : U -> U -> Prop.          (* «x организуется системой y» *)

  (* L1: определённое тождество — у системы один уровень *)
  Definition L1_determinate_level : Prop :=
    forall x l1 l2, at_level x l1 -> at_level x l2 -> l1 = l2.
  (* L5: порядок иррефлексивен; организуемое ниже организатора *)
  Definition L5_irreflexive : Prop := forall l, ~ lt l l.
  Definition L5_organized_below : Prop :=
    forall x y, mem x y ->
      exists lx ly, at_level x lx /\ at_level y ly /\ lt lx ly.

  Theorem P1_from_L1_and_L5 :
    L1_determinate_level -> L5_irreflexive -> L5_organized_below ->
    forall x, ~ mem x x.
  Proof.
    intros HL1 Hirr Hbelow x Hm.
    destruct (Hbelow x x Hm) as [lx [ly [Hx [Hy Hlt]]]].
    rewrite (HL1 x lx ly Hx Hy) in Hlt.
    exact (Hirr ly Hlt).
  Qed.
End P1_Derived.
```

Обе посылки нужны — для каждой проверена модель, в которой остальные условия выполнены, а система содержит себя
(`Check.v`, Closed):

```coq
Theorem P1_needs_L1 : exists U Lv lt at_level mem,
  L5_irreflexive Lv lt /\ L5_organized_below U Lv lt at_level mem /\ exists x, mem x x.
Theorem P1_needs_L5 : exists U Lv lt at_level mem,
  L1_determinate_level U Lv at_level /\ L5_organized_below U Lv lt at_level mem /\ exists x, mem x x.
```

Частный случай для типа `Level` формализации (`Check.v`, Closed):

```coq
Corollary no_self_membership_Level :
  forall (U : Type) (lev : U -> Level) (mem : U -> U -> Prop),
    (forall x y, mem x y -> lev x << lev y) -> forall x, ~ mem x x.
```

Для $P2$, $P3$, $P4$ вывода из законов при нынешней конструкции нет: $P2$ — поле записи `Criterion` (что глава
говорит сама, стр. 138–144), $P3$ — определение отношения, $P4$ — выбор типа $\mathbb{N} \to \mathbb{Q}$ (что
говорит комментарий файла). Для них остаётся поправка слов.

**(б) Поправить слова:**

> (39–41) Звено $\text{Distinction} \to L1$–$L5$ записано формальными теоремами Rocq (файл
> `LawsFromDistinction.v`). Принципы $P1$–$P4$ записаны теоремами файла `PrinciplesFromLaws.v`: каждая утверждает
> сам принцип — для типов `Level`, `Criterion`, `System` и последовательностей $\mathbb{N} \to \mathbb{Q}$. Законы
> в условия этих теорем не входят: ход от закона-источника к принципу проведён в тексте настоящей главы и в
> комментариях файла.
>
> (сноска 1) Формализация четырёх принципов содержится в файле `PrinciplesFromLaws.v` репозитория ToS-Coq; их
> деривация от законов изложена в комментариях файла. Доказательства опираются на `TheoryOfSystems_Core_ERR.v`;
> файлы `Distinction.v` и `LawsFromDistinction.v` подключены, но в доказательствах не участвуют.
>
> (сноска 4) Соответствующая теорема в файле — `four_principles_from_five_laws`. Теорема `derivation_chain`
> повторяет её утверждение; закон-источник каждого принципа ($P1$ от $L1 + L5$; $P2$ от $L5$; $P3$ от $L1 + L4$;
> $P4$ от $L5$) указан в комментариях, в само утверждение он не входит.

Если теорема из пункта (а) будет добавлена, к стр. 39–41 можно дописать: «Для $P1$ вывод записан и теоремой с
законами в посылках (`P1_from_L1_and_L5`)».

## Расхождение 2. Закон $L3$ назван выведенным и теоремой; в формализации это аксиома (стр. 60; 752–753)

**Было:**

> (60) Законы $L1$–$L5$, выведенные в Главе 3, суть условия определённости в их самом общем виде.
>
> (752–753) Это — условия самой возможности системности, выводимые из деривационной цепи и зафиксированные в
> Главе 3 как формальные теоремы Rocq.

**Проверка.** `src/foundation/Distinction.v:36`:

```coq
Axiom classic : forall P : Prop, P \/ ~P.
```

`src/foundation/LawsFromDistinction.v:63`:

```coq
Theorem Law_of_ExcludedMiddle : forall (A : Prop), A \/ ~A.
Proof. exact classic. Qed.
```

`Print Assumptions Law_of_ExcludedMiddle`: `Axioms: Distinction.classic : forall P : Prop, P \/ ~ P`.

Для записи $D$ закон $L3$ — её поле: `L3_from_distinction : forall D, positive D \/ negative D` (:67) проецирует
`exhaustive`; Closed. Но сама запись для произвольной пропозиции строится на `classic` (`distinction_of`,
`Distinction.v:75`), и обойти аксиому через запись нельзя — проверено (`Check.v`, Closed under the global context):

```coq
Theorem every_prop_distinguishes_iff_em :
  (forall P : Prop, exists D : Distinction, positive D = P) <-> (forall P : Prop, P \/ ~ P).
```

Остальные четыре закона записаны теоремами без допущений: `Law_of_Identity` (`A = A`, reflexivity),
`Law_of_NonContradiction`, `Law_of_SufficientReason` (из поля `exclusive`), `L5_hierarchy` — все Closed.

Комментарии файлов называют статус $L3$ прямо: «uses classic = our L3 axiom» (`LawsFromDistinction.v:60`); «L3 and
L4 require explicit declaration because CIC is constructive» (`ToS_Axioms.v:8–9`).

**В чём расхождение.** Из пяти законов четыре записаны теоремами, а $L3$ принят аксиомой. Слова «выведенные» и
«формальные теоремы» относят его к теоремам. Первое из двух мест расходится и с началом самой главы (стр. 11–15:
законы «не выводятся… а лишь прослеживаются»), и со сноской 8, где `classic` названа аксиомой.

**(а) Довести формализацию.** Нельзя: исключённое третье в исчислении Rocq без аксиомы не выводится (известный
факт о самом исчислении), а возможность построить запись `Distinction` для любой пропозиции ему равносильна
(теорема выше).

**(б) Поправить слова:**

> (60) Законы $L1$–$L5$, прослеженные в Главе 3 в записи `Distinction`, суть условия определённости в их самом
> общем виде.
>
> (752–753) Это — условия самой возможности системности, выводимые из деривационной цепи и зафиксированные в
> Главе 3 в формализации Rocq: $L1$, $L2$, $L4$, $L5$ — теоремами, $L3$ — аксиомой `classic` и полем `exhaustive`
> записи `Distinction`.

## Расхождение 3. `P1_blocks_russell` повторяет иррефлексивность порядка уровней (сноска 3; стр. 105–116)

**Было:**

> (112–116) **Следствие: парадокс Рассела блокирован.** … По $P1$ такой вопрос не имеет определённого содержания:
> самопринадлежности нет ни в одной правильно построенной системе.[^3]
>
> (сноска 3) Этот результат зафиксирован в теореме `P1_blocks_russell`.

**Проверка.** `src/foundation/PrinciplesFromLaws.v:51`:

```coq
Theorem P1_blocks_russell : forall l : Level, ~ (l << l).
Proof. exact level_lt_irrefl. Qed.
```

Closed under the global context. Утверждение дословно совпадает с `P1_from_L1_L5` (:43) и `P1_no_self_membership`
(:47). Отношения принадлежности между системами в формализации нет: запись `System L` состоит из критерия, границы
позиций и ограничения единственности. Шаг «если $S \in S$, то $\text{Level}(S) < \text{Level}(S)$» (стр. 105–110)
проведён в тексте главы, в Rocq он не записан.

Одноимённая теорема есть в `foundation/P4ProhibitsImpredicative.v:72` с другим утверждением:
`(forall x, ~ member x x) -> forall x, russell_criterion member x`, где `russell_criterion member x := ~ member x x`,
— заключение повторяет посылку.

**В чём расхождение.** Под именем «$P1$ блокирует Рассела» стоит иррефлексивность порядка на типе `Level`; ни
принадлежность, ни условие Рассела в утверждение не входят.

**(а) Довести формализацию.** Возможно, без допущений. Для любого отношения принадлежности, понижающего уровень
(это и есть $P1$), доказываются три утверждения (`Check.v`; все — Closed under the global context):

```coq
Section RussellHierarchy.
  Variable U : Type.
  Variable lev : U -> Level.
  Variable mem : U -> U -> Prop.
  Hypothesis mem_lowers : forall x y, mem x y -> lev x << lev y.

  (* условие Рассела «x не содержит себя» выполнено для всего *)
  Theorem russell_condition_holds_everywhere : forall x, ~ mem x x.
  Proof. exact (no_self_membership_Level U lev mem mem_lowers). Qed.

  (* собирателя условия Рассела по всему универсуму нет: он содержал бы и себя *)
  Theorem no_russell_collector : forall r,
    ~ (forall x, mem x r <-> ~ mem x x).
  Proof.
    intros r H.
    apply (russell_condition_holds_everywhere r).
    apply (proj2 (H r)). exact (russell_condition_holds_everywhere r).
  Qed.

  (* собиратель по уровням ниже своего непротиворечив:
     содержит всё, что ниже, и не содержит себя *)
  Theorem levelled_collector_is_harmless : forall r,
    (forall x, lev x << lev r -> (mem x r <-> ~ mem x x)) ->
    ~ mem r r /\ (forall x, lev x << lev r -> mem x r).
  Proof.
    intros r H. split.
    - exact (russell_condition_holds_everywhere r).
    - intros x Hx. apply (proj2 (H x Hx)).
      exact (russell_condition_holds_everywhere x).
  Qed.
End RussellHierarchy.
```

Оговорка: второе утверждение верно и без иерархии (это диагональ Рассела); иерархия даёт первое и третье — что
вопрос о самопринадлежности всегда решён отрицательно и что собиратель, взятый по низшим уровням, существует без
противоречия.

**(б) Поправить слова:**

> (сноска 3) Формальная опора — иррефлексивность порядка уровней: теорема `P1_blocks_russell` повторяет утверждение
> `P1_from_L1_L5`; отношение принадлежности между системами и множество Рассела в неё не входят, шаг от порядка
> уровней к принадлежности проведён в тексте. Подробное обсуждение связи с парадоксами — в «Парадоксы как смешение
> E/R/R-категорий».

## Расхождение 4. `P2_no_circularity` запрещает совпадение метки уровня, а не самоссылочное определение (стр. 160–162)

**Было:**

> Иначе говоря: «$S$ есть то, что удовлетворяет $S$» — формулировка, заблокированная самой типовой системой Rocq,
> поскольку требует построить критерий, нарушающий $P2$.

**Проверка.** `src/foundation/PrinciplesFromLaws.v:103` (блок кода на странице совпадает; Closed):

```coq
Theorem P2_no_circularity : forall L,
  ~ exists C : Criterion L, crit_level_witness L C = L.
```

Запись (`TheoryOfSystems_Core_ERR.v:163`):

```coq
Record Criterion (L : Level) : Type := mkCriterion {
  crit_domain : Type;
  crit_predicate : crit_domain -> Prop;
  crit_level_witness : Level;
  crit_level_valid : crit_level_witness << L;
}.
```

Поле `crit_level_witness` с областью и предикатом не связано: к любым области и предикату приписывается любая
допустимая метка (`Check.v`, Closed under the global context):

```coq
Theorem level_label_is_free : forall (L l : Level) (D : Type) (p : D -> Prop),
  l << L ->
  exists C : Criterion L, crit_domain L C = D /\ crit_level_witness L C = l.
```

Так устроен и пример самого репозитория: `co_all_L1` и `co_all_L2` (`IntensionalIdentity.v:165`, `:172`) — два
критерия с одной областью и одним предикатом, с метками `L1` и `L2`.

Критерий, областью которого служат системы, Rocq отклоняет при допустимой метке — и для того же уровня, и для
низшего (`CheckUniv2.v`, `CheckUniv3.v`):

```
Definition crit_over_systems : Criterion L2 :=
  mkCriterion L2 (System L2) (fun _ => True) L1 L1_lt_L2.

Error: The term "System L2" has type "Type@{max(Set+1,Criterion.u0+1)}"
while it is expected to have type "Type@{Criterion.u0}"
(universe inconsistency: Cannot enforce Criterion.u0 < Criterion.u0 …).
```

То же сообщение — для `Criterion L3` с областью `System L2`. Это отмечено и в самом файле
(`TheoryOfSystems_Core_ERR.v:365–368`: «We use indices as a practical workaround»).

**В чём расхождение.** Теорема запрещает одно: совпадение метки уровня критерия с уровнем системы. С содержанием
критерия метка не связана, поэтому о том, к чему критерий применяется, теорема не говорит. Самоссылочное
определение Rocq действительно не допускает, но по своим причинам (определение не может упоминать определяемое;
проверка вселенных), и поле `crit_level_valid` в этом не участвует.

**(а) Довести формализацию.** Типы `Criterion` и `System` менять нельзя (`CLAUDE.md`); возможно добавление —
критерий, у которого уровень связан с содержанием: всё, что ему удовлетворяет, лежит ниже его уровня. Набросок
проверен (`Check.v`; оба утверждения — Closed under the global context):

```coq
Section LevelledCriterionSketch.
  Variable U : Type.
  Variable lev : U -> Level.

  Record LevelledCriterion (L : Level) : Type := mkLevelledCriterion {
    lc_pred : U -> Prop;
    lc_below : forall x, lc_pred x -> lev x << L
  }.

  (* объект уровня L не удовлетворяет критерию уровня L *)
  Theorem criterion_excludes_own_level :
    forall (L : Level) (C : LevelledCriterion L) (s : U),
      lev s = L -> ~ lc_pred L C s.
  Proof.
    intros L C s Hs Hp. apply (level_lt_irrefl L).
    rewrite <- Hs at 1. exact (lc_below L C s Hp).
  Qed.

  (* «S есть то, что удовлетворяет S» исключено *)
  Theorem levelled_membership_no_self :
    forall (crit : forall s : U, LevelledCriterion (lev s)) (s : U),
      ~ lc_pred (lev s) (crit s) s.
End LevelledCriterionSketch.
```

С таким критерием слова главы получают буквальную опору, а принадлежность «$x$ удовлетворяет критерию $s$»
понижает уровень, так что к ней применимы теоремы расхождений 1 и 3.

**(б) Поправить слова:**

> Иначе говоря: метка уровня критерия не может совпасть с уровнем системы. Формулировку «$S$ есть то, что
> удовлетворяет $S$» Rocq не допускает и сам: определение не может ссылаться на определяемое.

## Расхождение 5. `P3_from_L1_L4`: совпадают три поля системы, а не три компоненты критерия; теорема раскрывает определение (стр. 205–206)

**Было:**

> …четвёртая фиксирует содержательное условие: совпадение трёх компонент критерия влечёт интенсиональное равенство
> систем.

**Проверка.** Определение (`TheoryOfSystems_Core_ERR.v:282`) и теорема (`PrinciplesFromLaws.v:155`; блок кода на
странице совпадает; Closed):

```coq
Definition systems_intensionally_equal {L : Level} (S1 S2 : System L) : Prop :=
  sys_criterion L S1 = sys_criterion L S2 /\
  sys_pos_bound L S1 = sys_pos_bound L S2 /\
  sys_uniqueness L S1 = sys_uniqueness L S2.

Theorem P3_from_L1_L4 : forall L (S1 S2 : System L),
  sys_criterion L S1 = sys_criterion L S2 ->
  sys_pos_bound L S1 = sys_pos_bound L S2 ->
  sys_uniqueness L S1 = sys_uniqueness L S2 ->
  systems_intensionally_equal S1 S2.
```

Три посылки — равенства трёх полей записи `System` (`:203`): критерия, границы позиций и ограничения
единственности. Критерий — одно поле из трёх. Заключение есть конъюнкция тех же трёх равенств.

Проверено дополнительно (`Check.v`, Closed under the global context):

```coq
Theorem intensional_iff_eq : forall (L : Level) (S1 S2 : System L),
  systems_intensionally_equal S1 S2 <-> S1 = S2.

Theorem same_criterion_not_enough :
  exists S1 S2 : System L2,
    sys_criterion L2 S1 = sys_criterion L2 S2 /\ ~ systems_intensionally_equal S1 S2.
```

То есть отношение совпадает с равенством записей `System`, и при одном и том же критерии две системы с разной
границей позиций интенсионально различны.

**В чём расхождение.** Совпадать должны три поля системы, а не три компоненты критерия; теорема не добавляет
условия, а раскрывает определение. Тезис стр. 175–177 «тождество системы определяется через её критерий» определение
передаёт не буквально: кроме критерия в него входят ещё два поля.

**(а) Довести формализацию.** Для слов стр. 203–206 не требуется. Если тезис «тождество через критерий» должен иметь
буквальную формальную опору, можно добавить отношение по одному полю и доказать, что оно — эквивалентность
(`Check.v`, Closed):

```coq
Definition same_criterion {L : Level} (S1 S2 : System L) : Prop :=
  sys_criterion L S1 = sys_criterion L S2.

Theorem same_criterion_equivalence : forall L : Level,
  (forall S : System L, same_criterion S S) /\
  (forall S1 S2 : System L, same_criterion S1 S2 -> same_criterion S2 S1) /\
  (forall S1 S2 S3 : System L,
     same_criterion S1 S2 -> same_criterion S2 S3 -> same_criterion S1 S3).
```

Какое из двух отношений считать тождеством системы — решает автор.

**(б) Поправить слова:**

> …четвёртая раскрывает определение: интенсиональное равенство систем есть совпадение трёх полей записи `System` —
> критерия, границы позиций и ограничения единственности.

## Расхождение 6. Блоки кода `P4_from_L5` и `four_principles_from_five_laws` отстали от исходника (стр. 246–247; 306)

**Было:**

```coq
Theorem P4_from_L5 : forall (R : nat -> Q) (n : nat),
  exists q : Q, R n = q.
```

```coq
  (forall (R : nat -> Q) n, exists q : Q, R n = q). (* P4 *)
```

**Проверка.** `src/foundation/PrinciplesFromLaws.v:191` и `:251` (обе теоремы — Closed under the global context):

```coq
Theorem P4_from_L5 : forall (R : nat -> Q) (n : nat),
  (exists (num : Z) (den : BinNums.positive), R n = num # den) /\
  (n = 0%nat \/ exists m : nat, n = S m).
```

```coq
  (forall (R : nat -> Q) n,
     exists (num : Z) (den : BinNums.positive), R n = num # den).
```

Комментарий файла (:183–:190) объясняет замену, сделанную в июне 2026: прежняя форма `exists q, R n = q` пуста
(свидетелем служит само `R n`). Остальные десять объявлений в блоках кода участка совпадают с исходником (два — с
точностью до имени `BinNums.positive`).

**В чём расхождение.** Страница приводит прежнюю форму двух утверждений. Слова стр. 256–267 о «скромном»
содержании теорем к нынешней форме подходят.

К тому же месту (стр. 294–298): четыре члена `four_principles_from_five_laws` говорят о разных предметах — об
уровнях, о критериях, о системах (рефлексивность равенства) и о последовательностях $\mathbb{N} \to \mathbb{Q}$;
утверждения вида «для любой системы $S$ выполнены все четыре» в теореме нет. Глава называет доказательство
конъюнкцией четырёх теорем (стр. 309–310), и это верно.

**(а) Довести формализацию.** Не требуется: формализация новее страницы.

**(б) Поправить слова** — заменить два блока:

```coq
Theorem P4_from_L5 : forall (R : nat -> Q) (n : nat),
  (exists (num : Z) (den : positive), R n = num # den) /\
  (n = 0%nat \/ exists m : nat, n = S m).
```

```coq
  (forall (R : nat -> Q) n,
     exists (num : Z) (den : positive), R n = num # den). (* P4 *)
```

К фразе стр. 256–257 можно дописать: «…и всякая стадия — начальная либо следующая за некоторой». Для стр. 297–298,
по желанию автора: «Формально четыре утверждения — об уровнях, о критериях, о системах и о процессах — собраны в
одной теореме:».

## Расхождение 7. E/R/R-структура в `ERRFromDistinction.v`: числа ролей и правил заданы определениями (стр. 42–45; 338–343; 461–468; сноска 7)

**Было:**

> (42–45) …этот файл фиксирует более *узкое* ядро цепи, чем полная архитектурная схема: он выводит E/R/R-структуру
> прямо из записи `Distinction` и законов…
>
> (338–343) Теорема `complete_foundation` … доказывает следующее: из любой пропозиции строится `Distinction`; для
> всякой `Distinction` выполнены законы $L2$ и $L3$; всякая `Distinction` даёт E/R/R-структуру не менее чем с двумя
> ролями; и уровневая иерархия иррефлексивна.
>
> (461–468) **Числовая фиксация в формализации.** В Rocq двойственность зафиксирована числовыми инвариантами:[^7]
> для всякой $D : \texttt{Distinction}$: $\texttt{err\_element\_count}(D) = 2$, $\texttt{err\_role\_count}(D) = 2$,
> $\texttt{err\_rule\_count}(D) = 2$.
>
> (сноска 7) … Также присутствуют теоремы `distinction_has_two_elements`, `distinction_has_two_roles`,
> `minimum_two_roles`, доказывающие эти равенства.

**Проверка.** `src/foundation/ERRFromDistinction.v` (17 `Qed`, объявлений `Axiom` и `Parameter` нет):

```coq
Definition err_element_count (D : Distinction) : nat := 2.     (* :51 *)
Definition err_role_count (D : Distinction) : nat := 2.        (* :54 *)
Definition err_rule_count (D : Distinction) : nat := 2.        (* :57 *)
Definition err_elements (D : Distinction) : list Prop := [positive D; negative D].   (* :60 *)

Theorem distinction_has_two_elements : forall D, length (err_elements D) = 2%nat.    (* :64, reflexivity *)
Theorem distinction_has_two_roles : forall D, err_role_count D = 2%nat.              (* :69, reflexivity *)
Theorem minimum_two_roles : forall D, (2 <= err_role_count D)%nat.                   (* :77 *)

Theorem complete_foundation :                                                        (* :158 *)
  (forall P, exists D : Distinction, positive D = P) /\
  (forall D, ~ (positive D /\ negative D) /\ (positive D \/ negative D)) /\
  (forall D, (2 <= err_role_count D)%nat) /\
  (forall l : Level, ~ (l << l)).
```

Три счётчика — постоянные функции, аргумент `D` в них не используется; в других файлах репозитория они не
применяются. `distinction_has_two_roles` после раскрытия определения есть `2 = 2`, `minimum_two_roles` и третий член
`complete_foundation` — `2 <= 2` (`Check.v`: `err_role_count_constant`, `minimum_two_roles_unfolded` — оба
доказаны `reflexivity`). `distinction_has_two_elements` говорит о длине списка из двух членов, а не о
`err_element_count`, и не утверждает, что члены различны. Для `err_rule_count` среди названных в сноске теорем нет
ни одной. Объекта «E/R/R-структура» (с элементами, ролями и правилами) в файле нет; пять теорем
`L1_for_elements` … `L5_err_hierarchy` (:86–:111) повторяют утверждения законов под именами аспектов.

`Print Assumptions complete_foundation`: `Axioms: Distinction.classic`. На аксиоме стоит первый член (построение
записи для любой пропозиции); страница о цене здесь не говорит. Второй член проецирует поля `exclusive` и
`exhaustive`, четвёртый — `level_lt_irrefl`; они пересказаны верно.

**В чём расхождение.** Файл не выводит ни E/R/R-структуру, ни число «два»: число ролей и число правил вписаны
определениями, а названные теоремы раскрывают эти определения. Рассуждение стр. 410–459 (почему элементов, ролей и
правил именно по два) в формализацию не входит.

**(а) Довести формализацию.** Возможно, без допущений: содержание рассуждения главы записывается теоремами о
самой записи. Все перечисленные утверждения проверены (`Check.v`) и закрыты (Closed under the global context).

*Два элемента* («различие одного полюса от себя — не различение»): стороны всякого различения различны; в
доказательстве участвуют оба правила.

```coq
Theorem sides_not_equivalent : forall D : Distinction,
  ~ (positive D <-> negative D).
Proof.
  intros D [H1 H2].
  destruct (exhaustive D) as [p | n].
  - exact (exclusive D (conj p (H1 p))).
  - exact (exclusive D (conj (H2 n) n)).
Qed.

Theorem sides_distinct : forall D : Distinction, positive D <> negative D.
Theorem two_distinct_elements : forall D : Distinction,
  NoDup (err_elements D) /\ length (err_elements D) = 2.
```

*Две роли* («если бы роль была одна, обе стороны занимали бы одну позицию»): при любой разметке сторон позициями
позиция выделенного и позиция фона различны; одной позиции недостаточно, двух достаточно.

```coq
Theorem two_positions_needed :
  forall (D : Distinction) (I : Type) (side : I -> Prop) (i j : I),
    side i = positive D -> side j = negative D -> i <> j.

Corollary one_position_insufficient :
  forall (D : Distinction) (side : unit -> Prop),
    ~ ((exists i, side i = positive D) /\ (exists j, side j = negative D)).

Definition side_of (D : Distinction) (b : bool) : Prop :=
  if b then positive D else negative D.
Theorem side_of_injective : forall D b1 b2, side_of D b1 = side_of D b2 -> b1 = b2.
```

*Два правила* («без `exclusive` стороны могут совпасть… без `exhaustive` появляется третий путь»; «два логически
независимых правила»):

```coq
Theorem without_exclusive_sides_may_coincide : exists P N : Prop, (P \/ N) /\ P = N.
Theorem without_exhaustive_sides_may_coincide : exists P N : Prop, ~ (P /\ N) /\ P = N.
Theorem without_exhaustive_third_way : exists P N : Prop, ~ (P /\ N) /\ ~ P /\ ~ N.
Theorem exclusive_not_from_exhaustive : ~ (forall P N : Prop, P \/ N -> ~ (P /\ N)).
Theorem exhaustive_not_from_exclusive : ~ (forall P N : Prop, ~ (P /\ N) -> P \/ N).
```

*Итог* — `complete_foundation` с содержательным третьим членом:

```coq
Theorem complete_foundation_with_sides :
  (forall P, exists D : Distinction, positive D = P) /\
  (forall D, ~ (positive D /\ negative D) /\ (positive D \/ negative D)) /\
  (forall D, positive D <> negative D /\
             NoDup (err_elements D) /\ length (err_elements D) = 2) /\
  (forall l : Level, ~ (l << l)).
```

Цена: `classic` (первый член). Без первого члена теорема закрыта (`foundation_core_closed`).

Границы: что правил «ровно два» и что «больше двух не нужны» — свойство текста определения записи (в ней два поля
с доказательствами); внутри Rocq это не формулируется. Доказуемы независимость двух правил и необходимость каждого.
Счётчики `err_*_count` можно оставить как обозначения, но ссылаться на них как на результат не следует.

**(б) Поправить слова** (если формализацию не трогать):

> (42–45) …этот файл фиксирует более *узкое* ядро цепи, чем полная архитектурная схема: он размечает запись
> `Distinction` по трём аспектам — список элементов `err_elements` составлен из двух её сторон, число ролей и число
> правил заданы определениями, законы повторены под именами аспектов, — не проводя *отдельной* формальной теоремы
> вида «из $P1$–$P4$ следует E/R/R».
>
> (338–343) …доказывает следующее: из любой пропозиции строится `Distinction` (на аксиоме `classic`); для всякой
> `Distinction` выполнены законы $L2$ и $L3$ — это её поля `exclusive` и `exhaustive`; число ролей, заданное
> определением `err_role_count` как $2$, не меньше двух; и уровневая иерархия иррефлексивна.
>
> (461–462) **Числовая фиксация в формализации.** В Rocq двойственность записана определениями:[^7] для всякой
> $D : \texttt{Distinction}$ положено:
>
> (сноска 7) Соответствующие функции файла `ERRFromDistinction.v` — `err_element_count`, `err_role_count`,
> `err_rule_count`; каждая определена как число $2$ и от $D$ не зависит, так что равенства верны по определению.
> Доказано в файле: список сторон `err_elements` $D$ имеет длину $2$ (`distinction_has_two_elements`); теоремы
> `distinction_has_two_roles` и `minimum_two_roles` раскрывают определение `err_role_count`.

Если теоремы пункта (а) будут добавлены, стр. 461–468 и сноска 7 могут сослаться на них: «стороны всякого
различения различны (`sides_distinct`); позиций не меньше двух (`two_positions_needed`); два правила независимы, и
без каждого стороны могут совпасть».

## Расхождение 8. `FormationRules.v`: суждение `HasType` не зависит от системы; `l4_role_principle` не о ролях (сноска 10)

**Было:**

> Формальный аппарат — в файле `FormationRules.v`, опирающемся на тип `System`, поле `sys_criterion` (конкретный
> критерий системы), отношение `HasType` (типизация системы в контексте). Ключевые леммы — `sys_form` (правило
> формации системы), `p1_check` (проверка иерархии), `l4_role_principle` (проверка обоснованности ролей),
> `wf4_check` (общая проверка хорошей сформированности).

**Проверка.** `src/Judgments.v:150` и `src/FormationRules.v:19–50` (все — Closed under the global context):

```coq
Definition HasType (G : Context) (S : System L) : Prop :=
  ctx_well_formed G /\
  crit_level_witness L (sys_criterion L S) << L.

Lemma sys_form : ctx_well_formed G -> crit_level_witness L (sys_criterion L S) << L -> HasType L G S.
Lemma p1_check : HasType L G S -> crit_level_witness L (sys_criterion L S) << L.
Lemma l4_role_principle : HasType L G S -> P2_valid L (sys_criterion L S).
Lemma wf4_check : HasType L G S ->
  ctx_well_formed G /\ crit_level_witness L (sys_criterion L S) << L.
```

Здесь `ctx_well_formed G := NoDup (map ce_name G)` — в контексте нет повторяющихся имён. Второй член `HasType`
выполнен для всякой системы: это поле `crit_level_valid` её критерия. Проверено (`Check.v`; все — Closed under the
global context):

```coq
Theorem HasType_iff_ctx : forall (L : Level) (G : Context) (S : System L),
  HasType L G S <-> ctx_well_formed G.

Corollary HasType_any_system : forall (L : Level) (G : Context) (S T : System L),
  HasType L G S -> HasType L G T.

Theorem p1_check_without_premise : forall (L : Level) (S : System L),
  crit_level_witness L (sys_criterion L S) << L.

Theorem l4_role_principle_is_p1_check : forall (L : Level) (S : System L),
  P2_valid L (sys_criterion L S) = (crit_level_witness L (sys_criterion L S) << L).     (* reflexivity *)

Theorem wf4_check_is_identity : forall (L : Level) (G : Context) (S : System L),
  HasType L G S = (ctx_well_formed G /\ crit_level_witness L (sys_criterion L S) << L). (* reflexivity *)
```

**В чём расхождение.** Суждение `HasType` равносильно правильности контекста и от системы не зависит: в правильном
контексте «типизирована» любая система. Заключения `p1_check` и `l4_role_principle` верны без посылки и совпадают
между собой по определению; о ролях и о законе $L4$ в `l4_role_principle` ничего нет. Заключение `wf4_check`
совпадает с её посылкой по определению. `sys_form` — правило введения того же определения; её вторая посылка
выполнена всегда.

**(а) Довести формализацию.** При нынешнем определении `HasType` — нельзя: независимость от системы есть теорема о
нём (`HasType_iff_ctx`). Чтобы суждение стало проверкой, в его определение нужно ввести условие, которое система
может не выполнить, — например, что система значится в контексте под своим уровнем (записи `CE_System n L` в типе
`CtxEntry` уже есть, `Judgments.v:41`), или условие на роли. Определения обоснованности ролей в формализации
имеются — `L4_grounded` и `ERR_WellFormed` в `Roles.v` (:64, :290), для типа `StructuredSystem`, — но `HasType` и
леммы `FormationRules.v` на них не опираются. Выбор условия — решение о конструкции; набросок не строился. От
`p1_check` и `l4_role_principle` зависят две леммы `Soundness.v` (:37, :47).

**(б) Поправить слова:**

> Формальный аппарат — в файле `FormationRules.v`, опирающемся на тип `System`, поле `sys_criterion` (конкретный
> критерий системы) и суждение `HasType` из `Judgments.v`: контекст правилен и уровень критерия системы ниже её
> уровня. Второе условие выполнено для всякой системы по построению записи `Criterion`, так что `HasType`
> равносильно правильности контекста. Леммы `sys_form`, `p1_check`, `l4_role_principle`, `wf4_check` раскрывают это
> определение: `sys_form` собирает суждение из двух условий, `p1_check` и `l4_role_principle` извлекают условие об
> уровне критерия (в двух записях), `wf4_check` — оба условия. Проверки обоснованности ролей среди них нет.

## Сомнительные места (не расхождения)

- **Стр. 7–15, 39–41, первое звено.** `five_laws_from_distinction` — теорема вида «для всякой $D$ — пять законов»;
  $L2$ и $L3$ она берёт из полей записи, $L1$ — из `reflexivity`, $L5$ — из порядка на `Level` (от $D$ не
  зависит). Слова главы «несёт в себе… как свои структурные свойства» и «прослеживаются» этому соответствуют;
  подробная сверка — в аудите Главы 3.
- **Стр. 77–79, «уже работает в записи `Distinction`».** Теоремы о принципах записи `Distinction` не упоминают
  (они о `Level`, `Criterion`, `System`, $\mathbb{N} \to \mathbb{Q}$), и файл собирается без `Distinction.v`
  (расхождение 1). Фраза читается как тезис автора, не как утверждение о формализации.
- **Стр. 91–97, `P1_from_L1_L5`.** Блок кода точен, доказательство показано на странице. Утверждение дословно то
  же, что `L5_hierarchy`; $L1$ в нём не участвует (см. расхождение 1, пункт (а)).
- **Стр. 127, «в двух формах».** `P2_from_L5` и `P2_structural` — одно утверждение с точностью до раскрытия
  определения `P2_valid`.
- **Стр. 138–144, «уровень критерия».** Это поле-метка `crit_level_witness` (расхождение 4). Следствие
  конструкции: на уровне `L1` критериев и систем нет — `Criterion L1 -> False`, `System L1 -> False` (`Check.v`,
  `no_criterion_at_L1`, `no_system_at_L1`; Closed). О системах уровня основания глава говорит во второй половине.
- **Стр. 208–221, пример с треугольниками.** В формализации не записан, и глава этого не утверждает. Имеющееся
  формальное разделение — `extensional_not_implies_intensional`, `system_P3_separation` (`IntensionalIdentity.v:195`,
  `:240`) — различает два критерия с одним и тем же предикатом `fun _ => True` по метке уровня (`L1` и `L2`), а не
  по различию оснований. Для двух экстенсионально равных предикатов неравенство критериев как термов в Rocq не
  доказуемо; различить «меру сторон» и «меру углов» можно, только представив критерий синтаксически.
- **Стр. 241–243, `RealProcess`.** Теоремы записаны для `R : nat -> Q`; имя `RealProcess` объявлено в десяти
  файлах одним и тем же определением.
- **Стр. 282–290, «не использует… Аксиомы Выбора».** Определение `RealProcess` закрыто; аксиом бесконечности и
  выбора в репозитории не объявлено. По ведомостям Части IV часть её теорем стоит на `L4_witness`
  (`ProcessBW.v`), а из `L4_witness` функция выбора для любого семейства получается в одну строку (`Check.v`,
  `choice_function_from_L4_witness`; допущение — `L4_witness`). Слово «конструкция» это выдерживает; о теоремах
  Части IV говорят её главы и Глава 6.
- **Стр. 371–373, «зафиксирован прямо».** Зафиксирован комментарием (`ERRFromDistinction.v:26`); сноска 6 это
  называет.
- **Стр. 395–401.** Поля `positive` и `negative` глава относит к Elements — как `err_elements`. Комментарии самой
  записи называют их ролями (`Distinction.v:68–69`, шапка файла :5–:7). Два прочтения разведены во второй половине
  главы («уровень экземпляра» и «уровень схемы»).
- **Стр. 796–798, «по $P1$».** Условие «уровень критерия ниже уровня системы» на стр. 118–144 и в
  `TheoryOfSystems_Core_ERR.v` (`P2_valid`) названо $P2$; в `Judgments.v` и `FormationRules.v` — $P1$
  (`has_type_implies_P1`, `p1_check`). Это одно условие под двумя именами.
- **Сноска 8, «обе фундаментальные аксиомы».** Логических допущений два. Утверждение `classic` объявлено в
  `foundation/Distinction.v:36`, в `settheory/BorelDeterminacy.v:21` и берётся из стандартной библиотеки
  (`ToS_Axioms.v:31`); кроме логических, в репозитории две аксиомы раздела Навье — Стокса.
- **Сноска 11, «обе ситуации формально разделены».** Понятий «автоматический подбор» и «операторный подбор» в
  формализации нет; разделение состоит в том, называет ли `Print Assumptions` теоремы аксиому `L4_witness`.
- **Вне формализации, стр. 855–858.** «Для каждой строки можно алгоритмически проверить, выводится ли она» верно
  для контекстно-свободных и контекстно-зависимых грамматик; для формальных грамматик общего вида задача
  принадлежности неразрешима.
- **Вне формализации, стр. 917–920.** «В группе $\mathbb{Z}_n$ это число $1$ при умножении»: $\mathbb{Z}_n$ по
  умножению группой не является; глава сама оговаривает это на стр. 850–853.

## Вне участка и вне главы

Для сведения (на участке эти строки не цитируются):

- **К второй половине главы (стр. 1037–1083).** Критерий с областью `System L2` не строится ни на каком уровне —
  в том числе `Criterion L3` (`CheckUniv3.v`, universe inconsistency); репозиторий обходит это индексами
  (`SystemL2Index := nat`, `TheoryOfSystems_Core_ERR.v:372`). То есть «элементы системы уровня $n+1$ суть системы
  уровня $n$» в типах формализации не выражено: уровень элементов задаётся меткой.
- `PrinciplesFromLaws.v`: три теоремы с одним утверждением `forall l, ~ (l << l)` (`P1_from_L1_L5`,
  `P1_no_self_membership`, `P1_blocks_russell`); `P1_no_self_membership` объявлена ещё и в
  `TheoryOfSystems_Core_ERR.v:126`. `principles_theorem_count := 22` при 20 `Qed`. Шапка: «P1-P4 DERIVED from L1-L5».
- `ERRFromDistinction.v`: `err_distinction_theorem_count := 22` при 17 `Qed`. `su2_from_distinction` (:128)
  дословно совпадает с `distinction_has_two_roles`; `su2_generators`, `su3_generators` — равенства `2 * 2 - 1 = 3`,
  `3 * 3 - 1 = 8`; комментарий (:140–:142) называет это выводом SU(2) из различения. `foundation_summary` (:204):
  первый член — `exists D : Distinction, True`. `L5_err_hierarchy` (:108) — `L1 << L2 /\ L2 << L3`; аспектов E/R/R
  в утверждении нет. Комментарий :182–:186 («Distinction → L1-L5 (as theorems, not axioms)») расходится со статусом
  $L3$.
- `LawsFromDistinction.v`: `L3_independence` (:172) — посылка в доказательстве отбрасывается (`intros _ P. exact
  (classic P)`); стоит на `classic`.
- `Distinction.v`: `distinction_theorem_count := 22` при 20 `Qed`.
- `Judgments.v`: шапка «STATUS: 20 Qed» при 23; «AXIOMS: classic (inherited…)» — леммы, названные в сноске 10,
  закрыты.
- `TheoryOfSystems_Core_ERR.v`: в теоремах `russell_paradox_blocked` (:248), `cantor_paradox_blocked_v1` (:1255),
  `no_self_level_elements` (:1271), `cantor_no_system_of_all_L2_systems` (:1300) член `crit_domain … = System …` в
  доказательстве не используется; все четыре — `P2_no_circularity` с добавленным неиспользуемым условием. Критерий
  `even_primes_gt_2_crit` (:289) простоты не содержит: его предикат — «чётное и больше двух».

## Дополнительные проверки

- `Print Assumptions` снят для всех теорем `PrinciplesFromLaws.v`, названных на участке, для десяти теорем
  `LawsFromDistinction.v`, тринадцати теорем `ERRFromDistinction.v` и четырёх лемм `FormationRules.v`. Отличны от
  «Closed under the global context»: `Law_of_ExcludedMiddle`, `L3_independence`, `laws_consistent`,
  `complete_foundation`, `foundation_summary` — все на `Distinction.classic`. Других имён в выводе компилятора нет.
- Блоки кода участка (12 объявлений): 10 совпадают с исходником, 2 расходятся (расхождение 6).
- Счёт `Qed` (`grep -c 'Qed\.'`): `Distinction.v` — 20, `LawsFromDistinction.v` — 22, `PrinciplesFromLaws.v` — 20,
  `ERRFromDistinction.v` — 17, `TheoryOfSystems_Core_ERR.v` — 36, `Judgments.v` — 23, `FormationRules.v` — 18.
  На участке эти числа не называются.
- Оговорки главы о масштабе (стр. 38–52, 138–144, 259–267, 337–352) соответствуют содержанию формализации: теоремы
  «из $P1$–$P4$ следует E/R/R» нет (то же говорит шапка `foundation/PrinciplesToERR.v:15–19`); $P2$ есть поле
  записи; теоремы $P4$ говорят о каждой стадии, а не о бесконечных тотальностях.
- Цитата сноски 6 сверена с комментарием `ERRFromDistinction.v:26`; отличается только регистром букв.
