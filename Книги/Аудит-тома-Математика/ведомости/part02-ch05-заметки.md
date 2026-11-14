# Глава II.5 «Структурный путь: число как позиция в системе» — заметки к ведомости (13.11.2026)

Ведомость: `part02-ch05.json` — 59 ручных записей, автоматических нет; `merge --dry` проходит без замечаний, список
«без сверки» пуст. Вердикты: ok — 53, mismatch-statement — 6.

Шесть записей с расхождением относятся к четырём местам (расхождения 1–4), и все четыре лежат в динамической
части главы: § 5.5 (стр. 513–514) и сноски 5–6 к нему. Статическая часть (§ 5.2–5.4, 5.7, сноски 1–4, 7) о
формализации говорит точно: `Position := nat` названа технической записью, а не выводом; частичность
`ss_assignment`, одна сторона единственности в `ss_L5_valid`, отсутствие `pos_number` и предикатов первой позиции
названы прямо, и проверка это подтвердила.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part02/ch05/`: `Check.v` (примеры пустой и разреженной
системы; первая занятая позиция; нумерация с единицы и индукция; `L5_resolve` и `resolve_role`; `process_entity`;
общие свойства `find_primary`), `CheckGen.v` (выбор первого кандидата через `l5_resolve_gen`), `CheckPA.v`
(`Print Assumptions` всех теорем трёх файлов, названных главой, и соседнего `StatusFromERR.v`). Все три
собираются; в них нет `Axiom`, `Parameter`, `Admitted`. Ответ `Print Assumptions` на каждую лемму пробных файлов —
Closed under the global context. В `src` и в собранной копии ничего не менялось.

Глава называет три файла: `src/TheoryOfSystems_Core_ERR.v` (36 `Qed`), `src/Roles.v` (30), `src/foundation/ERRProcess.v`
(12). Для проверки слов главы прочитаны ещё `src/foundation/StatusFromERR.v` (11), `src/L5Resolution.v`,
`src/foundation/LevelNatIso.v`, `src/foundation/L5_NatFromHierarchy.v`, `src/foundation/GroundedOrderedStructure.v`.
Чисел (`Qed`, файлов, аксиом) и слов о цене на странице нет.

## Что проверить не удалось

- Отсылки к другим главам (I.3, I.4, II.1–II.4 и их параграфы) не сверялись; это предмет ведомостей этих глав. Из
  главы II.3 прочитаны только строки о `level_depth` и `level_to_nat` (стр. 537–545), нужные для стр. 340–342.
- Философские тезисы главы (§ 5.1, 5.2, 5.6, 5.8.3–5.8.5: что есть система, четыре пути, один ряд, форма акта
  различения) не оценивались. Проверено только, что ни один из них не подан как доказанный в Rocq: страница сама
  называет итог «доказательством онтологическим», «а не единой машинно проверенной цепочкой теорем»
  (стр. 1037–1041).
- Слова «в текущем коде нет» проверены поиском по `src` и `Architecture_of_Reasoning`: по именам (`Locate`) и по
  словам `position_occupied`, `first_occupied`, `nonempty_structured`, `pos_number`, `L5_resolve`, `resolve_role`.
  Объявление с другим именем и иной формой записи такой поиск мог пропустить.
- Шапки `ERRProcess.v` и `StatusFromERR.v` говорят, что файлы повторяют реализацию на Python (`regulus/core`)
  «EXACTLY»; с ней они не сверялись (она вне `src`, страница о ней не говорит).
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «По весу и решается» — в формализации решают ворота (стр. 513–514)

**Было:**

> …элементу отвечает его *вес*, выраженный натуральным числом, и вес складывается из частных оценок соответствия,
> тоже числовых. По весу и решается, занять элементу роль или нет.

**Проверка.** `src/foundation/ERRProcess.v:194`:

```coq
Definition process_entity (id legacy : nat) (sig : GateSignals)
  (scores : RawScores) : ERREntity :=
  let gate := compute_gate sig in
  let weight := compute_weight scores gate in
  let status := if gate_valid gate then Candidate else Invalid in
  mkEntity id legacy sig scores gate weight status.
```

Статус вычисляется из `gate_valid gate` — конъюнкции четырёх булевых полей ворот; `weight` вычисляется рядом и в
выражение статуса не входит. Связь веса и ворот в файле одна — `zero_gate_law` (`:158`): ворота не пройдены ⇒ вес 0
(Closed under the global context). В пробном файле (`Check.v`, раздел D; все — Closed under the global context):

```coq
Lemma process_entity_status_by_gate : forall id lg sig sc,
  ent_status (process_entity id lg sig sc) =
  (if gate_valid (compute_gate sig) then Candidate else Invalid).          (* reflexivity *)

Lemma process_entity_positive_weight_candidate : forall id lg sig sc,
  0 < ent_weight (process_entity id lg sig sc) ->
  ent_status (process_entity id lg sig sc) = Candidate.

Lemma candidate_with_zero_weight :
  ent_status (process_entity 0 0 valid_signals (mkRS 0 0 0)) = Candidate /\
  ent_weight (process_entity 0 0 valid_signals (mkRS 0 0 0)) = 0.

Lemma status_not_determined_by_weight :
  ent_weight (process_entity 0 0 valid_signals (mkRS 0 0 0)) =
  ent_weight (process_entity 1 1 invalid_signals (mkRS 8 7 3)) /\
  ent_status (process_entity 0 0 valid_signals (mkRS 0 0 0)) <>
  ent_status (process_entity 1 1 invalid_signals (mkRS 8 7 3)).
```

**В чём расхождение.** В формализации допуск элемента (статус `Candidate` или `Invalid`) решают ворота, а не вес:
при равных весах статусы могут быть разными, и элемент с нулевым весом может быть допущен. Сноска 5 той же
страницы говорит это точно («по результату ворот он присваивает элементу один из двух статусов»); расходится с
формализацией фраза основного текста.

**(а) Довести формализацию.** Возможно, без аксиом и без изменения `process_entity`. В файле сказано, что номер
домена принимает значения 1–6 (`rs_current_domain : nat; (* Which domain D1-D6 = 1-6 *)`, `:54`); тип этого не
требует. При этом условии фраза страницы становится теоремой (`Check.v`, Closed under the global context):

```coq
Theorem candidate_iff_positive_weight :
  forall id lg sig sc, 1 <= rs_current_domain sc ->
    (ent_status (process_entity id lg sig sc) = Candidate <->
     0 < ent_weight (process_entity id lg sig sc)).
Proof.
  intros id lg sig sc Hd. split.
  - intro H. rewrite process_entity_status_by_gate in H. simpl. unfold compute_weight.
    destruct (gate_valid (compute_gate sig)); [lia | discriminate H].
  - apply process_entity_positive_weight_candidate.
Qed.
```

то есть при номере домена не меньше единицы элемент допущен тогда и только тогда, когда его вес положителен. Без
условия на домен верна одна сторона (`process_entity_positive_weight_candidate`), а обратная опровергается
примером `candidate_with_zero_weight`. Теорему с двумя вспомогательными леммами можно добавить в конец
`ERRProcess.v`; тогда слова страницы остаются как есть.

**(б) Поправить слова** (если формализацию не трогать):

> …и вес складывается из частных оценок соответствия, тоже числовых. Занять элементу роль или нет, решает
> проверка, и вес несёт её итог: у элемента, проверку не прошедшего, вес равен нулю.

## Расхождение 2. «Подбор элемента под роль описан функцией `process_entity`» — роли среди аргументов нет (сноска 5, стр. 1073)

**Было:**

> Подбор элемента под роль описан функцией `process_entity`: свойства элемента (`GateSignals`) сводятся в *ворота
> согласования* (`compute_gate`) — проверку из четырёх условий, отвечает ли элемент требованию; по воротам
> вычисляется *вес* (`compute_weight`) — натуральное число, мера соответствия, обращаемая в нуль при непройденных
> воротах (теорема `zero_gate_law`).

**Проверка.** Аргументы `process_entity` (`ERRProcess.v:194`) — два номера (`id`, `legacy`), запись сигналов и
запись оценок:

```coq
Record GateSignals := mkGS {
  gs_e_exists : bool;        (* Element present and identifiable *)
  gs_r_exists : bool;        (* Role (functional purpose) defined *)
  gs_rule_exists : bool;     (* Rule (logical connection) specified *)
  gs_s_exists : bool;        (* Status defined *)
  gs_deps_declared : bool;   (* Dependencies on prior domains stated *)
  gs_l1_l3_ok : bool;        (* No hierarchical loops *)
  gs_l5_ok : bool;           (* Domain sequence D1→D6 respected *)
}.

Record RawScores := mkRS {
  rs_struct_points : nat;    (* E/R/R structural completeness, 0-10 *)
  rs_domain_points : nat;    (* Quality within current domain, 0-10 *)
  rs_current_domain : nat;   (* Which domain D1-D6 = 1-6 *)
}.

Definition compute_gate (s : GateSignals) : IntegrityGate :=
  mkIG (gs_e_exists s && gs_r_exists s && gs_rule_exists s && gs_s_exists s)
       (gs_deps_declared s) (gs_l1_l3_ok s) (gs_l5_ok s).

Definition compute_weight (scores : RawScores) (gate : IntegrityGate) : nat :=
  if gate_valid gate then
    (rs_struct_points scores + rs_current_domain scores * 10 + rs_domain_points scores)%nat
  else 0%nat.
```

Роли и её требования среди аргументов нет; объекта «роль с требованием» в файле нет вообще (слово «Roles» в шапке
отнесено к типу статусов `Status`). Семь сигналов и три числа подаются на вход готовыми значениями; четыре
условия ворот — налицо ли элемент, роль, правило и статус; объявлены ли зависимости; нет ли петель уровней;
соблюдён ли порядок доменов — одни для всякого элемента. Требование роли в формализации записано в другом
файле и без числа: `rspec_filter : ElemType -> Prop` в записи `RoleSpec` (`TheoryOfSystems_Core_ERR.v:458`) и поле
`ra_satisfies` записи `RoleAssignment` (`Roles.v:59`). `ERRProcess.v` подключает только стандартную библиотеку.

**В чём расхождение.** Функция описывает проверку целостности одного элемента и подсчёт его веса по поданным
оценкам; соответствие элемента требованию роли в неё не входит, потому что роль в неё не входит. Число условий
ворот (четыре), тип веса (`nat`) и теорема `zero_gate_law` названы верно.

**(а) Довести формализацию.** Возможно, без аксиом — добавлением связки «мера решает, годен ли элемент; среди
годных первый берётся по порядку позиций» поверх уже имеющихся `StructuredSystem` и `resolve_role`. Набросок
проверен (`Check.v`, раздел D; Closed under the global context):

```coq
Section MeasuredRole.
  Variable L : Level.
  Variable S : StructuredSystem L.
  Variable measure : crit_domain L (sys_criterion L (ss_base L S)) -> nat.   (* мера соответствия *)
  Variable threshold : nat.                                                  (* требование роли *)

  Definition fits (e : crit_domain L (sys_criterion L (ss_base L S))) : bool :=
    threshold <=? measure e.

  Theorem measured_role_first :
    forall (positions : list Position) (default : Position),
      (exists p, In p (role_candidates L S fits positions) /\ p <= default) ->
      exists e,
        ss_assignment L S (resolve_role L S fits positions default) = Some e /\
        threshold <= measure e /\
        (forall q e', In q positions -> ss_assignment L S q = Some e' ->
                      threshold <= measure e' ->
                      resolve_role L S fits positions default <= q).
End MeasuredRole.
```

Теорема говорит: выбранная позиция занята элементом, мера которого достигает требования, и она первая среди
таких позиций. Здесь число участвует дважды — как мера и как позиция, — что и утверждает § 5.5. Это новое
определение, а не правка имеющихся; принимать ли его как запись «роли с числовым требованием», решает автор.
Саму `process_entity` до слов сноски довести нельзя, не изменив её аргументы.

**(б) Поправить слова:**

> Обработка одного элемента описана функцией `process_entity`: признаки элемента (`GateSignals`, семь булевых
> сигналов) сводятся в *ворота согласования* (`compute_gate`) — проверку из четырёх условий: налицо ли элемент,
> роль, правило и статус; объявлены ли зависимости; нет ли петель уровней; соблюдён ли порядок; по воротам и по
> трём числовым оценкам элемента вычисляется *вес* (`compute_weight`) — натуральное число, мера соответствия,
> обращаемая в нуль при непройденных воротах (теорема `zero_gate_law`). Сама роль и её требование аргументами в
> `process_entity` не входят: сигналы и оценки подаются на вход готовыми, а четыре условия ворот одни для
> всякого элемента.

## Расхождение 3 (статус). Машина, где вес определяет первого, в формализации есть — `StatusFromERR.v` (сноски 5 и 6, стр. 1073–1074)

**Было:**

> (сноска 5) Более богатая статусная машина — та, где веса *сравниваются* между кандидатами и из них выбирается
> первый, максимальный (статусы `PrimaryMax`, `SecondaryMax`, `HistoricalMax` в типе `Status` объявлены), — в
> текущем `process_entity` ещё не задействована: он различает лишь `Candidate` и `Invalid`. … Полная
> статусно-весовая машина, где вес определяет первого среди кандидатов, потребовала бы связать `ERRProcess.v` с
> `resolve_role` ролевого слоя; сейчас это два отдельных механизма.
>
> (сноска 6) Полная связка «вес определяет первого» требует их соединения; см. сноску выше и итог главы.

**Проверка.** Файл `src/foundation/StatusFromERR.v` внесён тем же коммитом, что и `ERRProcess.v` (5c3c099,
04.04.2026), подключает `foundation.ERRProcess`, стоит в `_CoqProject` и собран:

```coq
Definition compare_entities (e1 e2 : ERREntity) : bool :=                       (* :36 *)
  if (ent_weight e2 <? ent_weight e1)%nat then true
  else if (ent_weight e1 <? ent_weight e2)%nat then false
  else (ent_legacy_idx e1 <=? ent_legacy_idx e2)%nat.

Fixpoint find_primary (entities : list ERREntity) : option ERREntity := …       (* :46 *)

Definition assign_status (e : ERREntity) (primary : option ERREntity) : Status :=   (* :63 *)
  if negb (gate_valid (ent_gate e)) then Invalid
  else match primary with
  | None => Candidate
  | Some p =>
    if (ent_id e =? ent_id p)%nat then PrimaryMax
    else if (ent_weight e =? ent_weight p)%nat then SecondaryMax
    else Candidate
  end.
```

`find_primary` проходит список и оставляет прошедшего ворота с наибольшим весом, при равных весах — с меньшим
`ent_legacy_idx` (порядок создания). `assign_status` присваивает четыре статуса из пяти; `HistoricalMax` не
присваивается ни одной функцией формализации. Теоремы файла (11 `Qed`, все Closed under the global context):
веса и статусы на примере из трёх элементов (`weight_A`…`C_is_invalid`), `uniqueness`, `stability`,
`zero_gate_implies_invalid`, `status_from_err_synthesis`. Общего утверждения о том, что `find_primary` возвращает
элемент наибольшего веса, в файле нет. С `resolve_role` и `Roles.v` файл не связан.

**В чём расхождение.** Страница говорит о сравнении весов и выборе первого как о том, чего в формализации пока
нет и что потребовало бы связать `ERRProcess.v` с `resolve_role`. Такая машина записана — в соседнем файле и без
`resolve_role`; не доказано лишь её общее свойство. О самой `process_entity` страница говорит верно.

**(а) Довести формализацию.** Возможно, без аксиом: дописать в `StatusFromERR.v` общие теоремы о `find_primary`.
Проверены (`Check.v`, раздел E; Closed under the global context):

```coq
Theorem find_primary_spec :
  forall (es : list ERREntity) (p : ERREntity),
    find_primary es = Some p ->
    In p es /\ gate_valid (ent_gate p) = true /\
    (forall e, In e es -> gate_valid (ent_gate e) = true ->
       ent_weight e < ent_weight p \/
       (ent_weight e = ent_weight p /\ ent_legacy_idx p <= ent_legacy_idx e)).

Corollary find_primary_max_weight :
  forall es p, find_primary es = Some p ->
    forall e, In e es -> gate_valid (ent_gate e) = true -> ent_weight e <= ent_weight p.

Lemma find_primary_none :
  forall es, find_primary es = None ->
    forall e, In e es -> gate_valid (ent_gate e) = false.

Theorem find_primary_exists :
  forall es, (exists e, In e es /\ gate_valid (ent_gate e) = true) ->
    exists p, find_primary es = Some p.
```

Первая теорема доказывается индукцией по списку с разбором `compare_entities` (две вспомогательные леммы
`compare_entities_true`, `compare_entities_false`); полный текст — в `Check.v` (около 70 строк). Вместе они
говорят: первый есть, как только есть хотя бы один прошедший ворота; он из списка, прошёл ворота, его вес
наибольший, а среди равных по весу он создан раньше всех. После этого слова «вес определяет первого» имеют
формальную опору. Связывать эту машину с `resolve_role` для этого не требуется.

**(б) Поправить слова.** Сноска 5, от слов «Более богатая статусная машина» до конца:

> Более богатая статусная машина — та, где веса *сравниваются* между кандидатами и из них выбирается первый,
> максимальный, — в самом `process_entity` не задействована: он различает лишь `Candidate` и `Invalid`. Она
> записана в соседнем файле `StatusFromERR.v`: функция `find_primary` берёт среди прошедших ворота элемент с
> наибольшим весом, а при равных весах — созданный раньше; функция `assign_status` присваивает статусы
> `PrimaryMax`, `SecondaryMax`, `Candidate`, `Invalid` (статус `HistoricalMax` в типе `Status` объявлен, но пока
> не присваивается). Общее свойство этого выбора в файле проверено на примере из трёх элементов. Разрешение же
> по кандидатам … [фраза о `resolve_role` — см. расхождение 4] … С весовой машиной `StatusFromERR.v` ролевой
> слой `Roles.v` не связан: выбор по весу и выбор по позиции — сейчас два отдельных механизма. Здесь и далее
> имена файлов репозитория приводятся для справки.

Сноска 6:

> В текущей формализации эти части разнесены по файлам: вычисление веса и присвоение статуса `Candidate` /
> `Invalid` — в `ERRProcess.v`, сравнение весов и выбор первого по весу — в `StatusFromERR.v`, выбор по
> минимальной позиции среди кандидатов — в `Roles.v` (`resolve_role`). Выбор по весу и выбор по позиции между
> собой не связаны; см. сноску выше и итог главы.

Если теоремы пункта (а) будут добавлены, фразу «Общее свойство этого выбора в файле проверено на примере из трёх
элементов» следует заменить на «Общее свойство этого выбора доказано теоремой `find_primary_spec`».

## Расхождение 4. `resolve_role`: «выбор одного из подходящих» — доказана одна сторона (сноски 5 и 6, стр. 1073–1074)

**Было:**

> (сноска 5) Разрешение же по кандидатам — выбор одного из многих подходящих — формализовано в отдельном файле
> `Roles.v` механизмом `resolve_role` (через `L5_resolve`), и работает оно по *позициям*-кандидатам, не по весам
> `ERRProcess.v`.
>
> (сноска 6) …выбор первого из кандидатов по минимальной позиции — в `Roles.v` (`resolve_role`).

**Проверка.** `src/TheoryOfSystems_Core_ERR.v:633` и `src/Roles.v:196–229`:

```coq
Definition L5_resolve (candidates : list Position) (default : Position) : Position :=
  fold_right Nat.min default candidates.

Definition resolve_role (S : StructuredSystem L)
    (decide : crit_domain L (sys_criterion L (ss_base L S)) -> bool)
    (positions : list Position) (default : Position) : Position :=
  L5_resolve (role_candidates S decide positions) default.

Lemma resolve_role_deterministic :
  forall S decide positions default,
    resolve_role S decide positions default = resolve_role S decide positions default.

Lemma resolve_role_le_all_candidates :
  forall S decide positions default p,
    In p (role_candidates S decide positions) ->
    role_candidates S decide positions <> [] ->
    (resolve_role S decide positions default <= p)%nat.
```

Итог есть наименьшее из позиций-кандидатов *и позиции по умолчанию*. О `resolve_role` в формализации доказаны
два утверждения: `x = x` (первая лемма, `reflexivity`) и оценка сверху (вторая; Closed under the global
context). Того, что итог есть один из кандидатов, нет ни в `Roles.v`, ни в `TheoryOfSystems_Core_ERR.v`
(`L5_resolve_le_all`, `L5_resolve_le_default` — тоже оценки). Без условия на умолчание это неверно (`Check.v`,
раздел C; Closed under the global context):

```coq
Lemma L5_resolve_may_miss : L5_resolve [5; 7] 0 = 0 /\ ~ In 0 [5; 7].

Lemma resolve_role_may_miss :
  resolve_role L2 sparse_ss (fun _ => true) [5] 0 = 0 /\
  role_candidates L2 sparse_ss (fun _ => true) [5] = [5] /\
  ~ position_occupied sparse_ss 0.
```

Во втором примере единственный кандидат — позиция 5, а `resolve_role` возвращает позицию 0, которая в системе
пуста.

Для другой функции — `l5_resolve_gen` (`src/L5Resolution.v:76`, без умолчания, итог в `option`) — обе стороны
доказаны: `l5_resolve_gen_in` (`:176`) и `l5_resolve_gen_minimal` (`:188`). `resolve_role` определена не через неё.
Одноимённая `L5_resolve` в `foundation/L5_ResolutionGeneral.v:17` — третья функция (голова списка); к `Roles.v`
она отношения не имеет.

**В чём расхождение.** «Выбор одного из подходящих» предполагает, что выбранное — из подходящих. Доказано
только, что итог не больше всякого кандидата; при позиции по умолчанию, меньшей всех кандидатов, итогом
оказывается сама эта позиция. Слова «через `L5_resolve`», «по позициям-кандидатам, не по весам» и размещение
по файлам названы верно.

**(а) Довести формализацию.** Возможно, без аксиом, двумя способами; оба проверены.

Первый — добавить недостающую сторону с условием на умолчание (`Check.v`; Closed under the global context):

```coq
Lemma L5_resolve_in_or_default :
  forall (cs : list Position) (d : Position),
    In (L5_resolve cs d) cs \/ L5_resolve cs d = d.
Proof.
  intros cs d. unfold L5_resolve. induction cs as [ | a cs IH]; simpl.
  - right. reflexivity.
  - destruct (Nat.min_dec a (fold_right Nat.min d cs)) as [H | H]; rewrite H.
    + left. left. reflexivity.
    + destruct IH as [IH | IH].
      * left. right. exact IH.
      * right. exact IH.
Qed.

Lemma L5_resolve_in :
  forall (cs : list Position) (d : Position),
    (exists p, In p cs /\ p <= d) -> In (L5_resolve cs d) cs.
Proof.
  intros cs d [p [Hin Hle]].
  destruct (L5_resolve_in_or_default cs d) as [H | H]; [exact H | ].
  assert (Hne : cs <> nil) by (intro E; subst cs; exact Hin).
  pose proof (L5_resolve_le_all cs d Hne p Hin) as Hmin.
  assert (Heq : L5_resolve cs d = p) by lia.
  rewrite Heq. exact Hin.
Qed.

Theorem resolve_role_first_candidate :
  forall (L : Level) (S : StructuredSystem L)
         (decide : crit_domain L (sys_criterion L (ss_base L S)) -> bool)
         (positions : list Position) (default : Position),
    (exists p, In p (role_candidates L S decide positions) /\ p <= default) ->
    In (resolve_role L S decide positions default) positions /\
    (exists e, ss_assignment L S (resolve_role L S decide positions default) = Some e
               /\ decide e = true) /\
    (forall q, In q (role_candidates L S decide positions) ->
               resolve_role L S decide positions default <= q).

Corollary resolve_role_default_candidate :
  forall (L : Level) (S : StructuredSystem L) decide positions default,
    In default (role_candidates L S decide positions) ->
    In (resolve_role L S decide positions default) (role_candidates L S decide positions).
```

Теорема говорит: при умолчании, не меньшем хотя бы одного кандидата, выбранная позиция взята из списка, занята
элементом, прошедшим проверку, и не больше всякого другого кандидата. Первые две леммы — в
`TheoryOfSystems_Core_ERR.v` после `L5_resolve_le_default` (добавление; имеющиеся объявления не меняются),
теорема и следствие — в `Roles.v`.

Второй — рядом с `resolve_role` дать вариант без умолчания через уже доказанную `l5_resolve_gen` (`CheckGen.v`;
Closed under the global context):

```coq
Definition resolve_role_opt (L : Level) (S : StructuredSystem L)
    (decide : crit_domain L (sys_criterion L (ss_base L S)) -> bool)
    (positions : list Position) : option Position :=
  l5_resolve_gen (role_candidates L S decide positions).

Theorem resolve_role_opt_first :
  forall (L : Level) (S : StructuredSystem L) decide positions r,
    resolve_role_opt L S decide positions = Some r ->
    In r (role_candidates L S decide positions) /\
    (exists e, ss_assignment L S r = Some e /\ decide e = true) /\
    (forall q, In q (role_candidates L S decide positions) -> r <= q).

Theorem resolve_role_opt_none_iff : … resolve_role_opt L S decide positions = None <->
                                       role_candidates L S decide positions = [].

Theorem resolve_role_opt_agrees : … resolve_role_opt L S decide positions = Some r ->
                                     resolve_role L S decide positions r = r.
```

Здесь условие на умолчание не нужно: нет кандидатов — нет выбора (`None`), есть — выбран первый из них.
`L5Resolution.v` подключает только `TheoryOfSystems_Core_ERR.v` и стандартную библиотеку и стоит в `_CoqProject`
раньше `Roles.v`, так что вариант можно поместить в `Roles.v` (подключив `L5Resolution`) или в отдельный файл;
цикла зависимостей не возникает.

**(б) Поправить слова.** Сноска 5:

> Разрешение же по кандидатам формализовано в отдельном файле `Roles.v` механизмом `resolve_role` (через
> `L5_resolve`): он возвращает наименьшую из позиций-кандидатов и позиции, заданной по умолчанию, так что итог
> не больше всякого кандидата; и работает оно по *позициям*-кандидатам, не по весам `ERRProcess.v`.

Сноска 6 — в редакции расхождения 3 («выбор по минимальной позиции среди кандидатов — в `Roles.v`
(`resolve_role`)»); если нужна полная точность, добавить: «(итог — наименьшая из позиций-кандидатов и позиции по
умолчанию)».

Если принят пункт (а), слова «выбор одного из многих подходящих» и «выбор первого из кандидатов» остаются, с
оговоркой для первого способа: «при позиции по умолчанию, не меньшей хотя бы одного кандидата».

## Сомнительные места (не расхождения)

1. **Стр. 119–120, «Это — то, что $L4$ *доказывает*: всякое занятое место имеет ролевое обоснование».** Rocq
   здесь не назван; слово читается как слово о законе. Для сведения: в формализации ролевая обоснованность —
   условие, а не теорема. `L4_grounded` (`Roles.v:64`) — предикат на системе со списком назначений;
   `L4_grounded_implies_no_orphans` (`:71`) повторяет его определение; в запись `StructuredSystem` это условие
   не входит (всякая непустая система с пустым списком назначений его не выполняет — `CheckPA.v`,
   `sparse_not_grounded_by_nil`, Closed). То же для `wf_L4` в `ERR_WellFormed` (`Roles.v:295`).
2. **Стр. 843–844 против стр. 121–128.** Итог главы: «по закону $L4$ места системы различимы — у каждого своя
   роль»; § 5.2 той же главы: «Чего $L4$ сам по себе *не* даёт — так это того, что у *разных* мест роли
   непременно *разные*». В формализации различность ролей у разных мест не требуется (`L4_grounded` просит хотя
   бы одно назначение на занятую позицию). Какая из двух формул остаётся, решает автор.
3. **Стр. 330–333, «она требует, чтобы система была непустой, а её занятые позиции образовывали упорядоченный
   начальный ряд».** Для существования первой занятой позиции достаточно одной непустоты
   (`nonempty_has_first_position`, `first_position_iff_nonempty` — `Check.v`, Closed under the global context);
   начальный отрезок нужен для другого — чтобы первая занятая позиция имела индекс 0, то есть номер 1
   (`normalized_first_number_one`; у разреженной `sparse_ss` первая занятая позиция — 5, номер 6:
   `sparse_first_is_5`). Стр. 878 той же главы говорит точно: «первая позиция требует непустоты».
4. **Сноска 2 (стр. 1070), «предмет синхронизации репозитория».** Оба предиката определяются через имеющийся
   `position_occupied` (`TheoryOfSystems_Core_ERR.v:587`), и теорема о первой позиции доказывается без аксиом,
   потому что занятость позиции разрешима (значение `option`). Проверено (`Check.v`, раздел B):

   ```coq
   Definition nonempty_structured {L : Level} (S : StructuredSystem L) : Prop :=
     exists p, position_occupied S p.
   Definition first_occupied_position {L : Level} (S : StructuredSystem L) (p : Position) : Prop :=
     position_occupied S p /\ forall q, position_occupied S q -> p <= q.
   Definition normalized {L : Level} (S : StructuredSystem L) : Prop :=
     forall p q, q <= p -> position_occupied S p -> position_occupied S q.
   Definition pos_number (p : Position) : nat := S p.

   Theorem nonempty_has_first_position : forall (L : Level) (S : StructuredSystem L),
     nonempty_structured S -> exists p, first_occupied_position S p.
   Theorem first_occupied_position_unique : forall (L : Level) (S : StructuredSystem L) p q,
     first_occupied_position S p -> first_occupied_position S q -> p = q.
   Theorem normalized_first_number_one : forall (L : Level) (S : StructuredSystem L),
     normalized S -> nonempty_structured S ->
     exists p, first_occupied_position S p /\ pos_number p = 1.
   Lemma number_ind_from_one : forall P : nat -> Prop,
     P 1 -> (forall n, 1 <= n -> P n -> P (S n)) -> forall n, 1 <= n -> P n.
   ```

   Добавление этих объявлений (в `Roles.v` или отдельным файлом; `TheoryOfSystems_Core_ERR.v` при этом не
   меняется) закрыло бы сноски 2 и 3 и дало бы формальную опору словам стр. 313–315 и 340–350. Тип `nat` при
   этом по-прежнему берётся готовым; оценка главы на стр. 248–267 остаётся в силе.
5. **Стр. 340–342, `level_to_nat`.** Объявлений два: на отдельном типе `LBase`/`LSucc`
   (`foundation/L5_NatFromHierarchy.v:17`, его называет Глава II.3) и на основном типе `Level`
   (`foundation/LevelNatIso.v:37`). Во втором файле сдвиг на единицу доказан: `level_depth_eq : forall l,
   level_depth l = S (level_to_nat l)` (`:121`, Closed under the global context) — точный образец для
   `pos_number p := S p`; на него можно сослаться.
6. **Стр. 511–513, «вес складывается из частных оценок соответствия».** Формула в `compute_weight`:
   `rs_struct_points + rs_current_domain * 10 + rs_domain_points`. Два слагаемых — оценки (0–10 по комментарию),
   третье — номер домена с множителем 10. Комментарий над определением даёт другую формулу
   («W = G_total × (S_struct + S_domain)»).
7. **Стр. 887–889 и таблица, стр. 911: «ворота → вес → статус», «под роли подбираются элементы (по весу)».**
   Порядок повторяет комментарий `ERRProcess.v` («properties → gate → weight → status»). В `process_entity`
   статус зависит от ворот, а не от веса (расхождение 1); выбор по весу есть в `StatusFromERR.v`
   (расхождение 3). Оговорка стр. 879–880 это частично учитывает.
8. **Стр. 394–396, 636–638, 643–644: «одна операция следования `S`, взятая в четырёх видах», «тождественному
   ряду».** Теоремы, связывающей четыре пути, в формализации нет; на структурном пути позиция есть `nat` по
   определению, на иерархическом есть биекция уровней с `nat` (`LevelNatIso.v`). Страница подаёт совпадение как
   довод и на стр. 1037–1041 прямо говорит, что это не машинно проверенная цепочка; расхождения нет.
9. **Сноска 3 (стр. 1071), «См. итог главы».** В § 5.8 `pos_number` не упоминается (имя стоит на стр. 349, 350,
   769 и в самой сноске).
10. **Стр. 1061–1062, «целым и рациональным числам, а затем отрезку и числам действительным — посвящена
    Часть III».** На сайте Часть III — «От натуральных к рациональным» (целые, рациональные, счётность, «От
    позиции к процессу»); действительным числам посвящена Часть IV «Процессные действительные числа».
11. **Стр. 1050, «тип `nat` Rocq-репозитория».** `nat` — тип стандартной библиотеки Rocq
    (`Corelib.Init.Datatypes.nat`); в репозитории он не объявляется. Точнее: «стандартный тип `nat` Rocq».
12. **Стр. 919–921, «Соблюдён $P1$: … порядок строг (нет места прежде себя)».** Для позиций это свойство порядка
    `nat`; теоремы о $P1$ для `StructuredSystem` в формализации нет, и страница её не называет.

## Вне главы: шапки и состав файлов

Для сведения (в главе эти строки не цитируются):

- `ERRProcess.v:5` — «STATUS: 15 Qed»; действительный счёт — 12. Шапка (`:20`) ссылается на
  `ZeroGateFormalized.v`; такого файла в `src` нет.
- `StatusFromERR.v:5` — «12 Qed»; действительный счёт — 11. Теорема `uniqueness` (`:119`) верна и без двух своих
  посылок — `find_primary entities = Some p` и `In e entities` в доказательстве не используются
  (`uniqueness_without_premises`, `Check.v`, Closed). Она говорит: элемент с другим `ent_id` не получает
  `PrimaryMax`; единственности `ent_id` в списке ничто не требует, так что слова шапки «at most one PrimaryMax»
  шире доказанного. Четвёртый конъюнкт `status_from_err_synthesis` подписан «Uniqueness», а повторяет
  `stability`.
- `Roles.v` — шапка: «30 Qed, 0 axioms» (счёт верен: 30); итоговый комментарий (`:681`) — «PROVEN (28 Qed)»;
  строка `:730` — «AXIOMS: classic (from Classical, inherited via Core_ERR)», тогда как все 30 теорем файла —
  Closed under the global context. `resolve_role_deterministic` (`:212`), `status_deterministic` (`:256`),
  `status_assignment_deterministic` (`:477`) — утверждения вида `x = x`; `well_formed_no_paradox` (`:665`)
  заключает `True`; поле `wf4_cond3 : True` (`:573`).
- `TheoryOfSystems_Core_ERR.v:579–580` — комментарии «L5 ensures: no element "floats" without position» под
  записью `StructuredSystem`; запись этого не требует (элемент области может не стоять ни на одной позиции).

## Дополнительные проверки

- Файлы `TheoryOfSystems_Core_ERR.v`, `Roles.v`, `foundation/ERRProcess.v`, `foundation/StatusFromERR.v` в
  репозитории и в собранной копии совпадают побайтно.
- `Print Assumptions` для всех 53 теорем и лемм файлов `Roles.v`, `ERRProcess.v`, `StatusFromERR.v` и для
  `L5_resolve_le_all` — Closed under the global context (`CheckPA.v`). Имён `Classical_Prop.classic` и
  `ToS_Axioms.L4_witness` в ответах нет; третьих имён нет. (Для сравнения: `L4_equiv_Difference` из
  `TheoryOfSystems_Core_ERR.v`, которую глава не называет, — `Classical_Prop.classic`.)
- Блоков кода на странице нет; сверять с исходником нечего.
- Сноски 1–7 отнесены к местам текста: [^1] — стр. 222, [^2] — стр. 338, [^3] — стр. 350, [^4] — стр. 443,
  [^5] — стр. 506, [^6] — стр. 516, [^7] — стр. 875; все записаны.
- Внутренние отсылки главы (§ 5.3.2 в сноске 4, § 5.4.1, § 5.4.2, § 5.5.3, § 5.7, § 5.8.2–5.8.4) ведут на
  существующие разделы с названным содержанием; исключение — «итог главы» в сноске 3 (см. «Сомнительные
  места», п. 9).
- Имя `Candidate` инструмент `tom-status` отнёс к записи `ethics/EthicsEgoism.v:198`; в главе это конструктор
  типа `Status` (`ERRProcess.v:65`), в ведомости файл указан явно.
