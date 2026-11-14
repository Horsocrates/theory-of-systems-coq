// Часть II, шаг 6, страницы (2026-11-14, слово автора «Вноси, А»): 7 правок главы II.5 и сноска 5 в варианте А
// (запись «роли с числовым требованием» оставлена и названа) внесены.
// Формализация — новый src/foundation/StructuralPath.v; Core_ERR, Roles, ERRProcess, StatusFromERR не менялись.
// Запуск: node patch-p02-step-06-pages.cjs  (затем relocate + merge по part02-ch05). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть II, шаг 6, слово автора)';
const F = 'src/foundation/';
const SP = F + 'StructuralPath.v';
const EP = F + 'ERRProcess.v';
const SF = F + 'StatusFromERR.v';
const RO = 'src/Roles.v';
const CORE = 'src/TheoryOfSystems_Core_ERR.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  const fix = (prefix, th, fields) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (!hit.length) return;                                   // уже внесено
    if (hit.length !== 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, add, save };
}

// --- новые цитаты страницы
const S1 = 'Обработка одного элемента описана функцией `process_entity`: признаки элемента (`GateSignals`, семь булевых сигналов) сводятся в *ворота согласования* (`compute_gate`) — проверку из четырёх условий (налицо ли элемент, роль, правило и статус; объявлены ли зависимости; нет ли петель уровней; соблюдён ли порядок);';
const S2 = 'по воротам и по числовым оценкам элемента вычисляется *вес* (`compute_weight`) — натуральное число, мера соответствия, обращаемая в нуль при непройденных воротах (теорема `zero_gate_law`).';
const S3 = 'По результату ворот `process_entity` присваивает элементу один из двух статусов — `Candidate` (ворота пройдены) или `Invalid` (не пройдены);';
const S4 = 'при номере домена не меньше единицы (в файле домены нумеруются от $1$ до $6$) допуск равносилен положительному весу — теорема `candidate_iff_positive_weight` (файл `StructuralPath.v`), и в этом смысле по весу и решается.';
const S5 = 'Сама роль и её требование аргументами в `process_entity` не входят; подбор элемента под роль с числовым требованием записан отдельно (там же, теорема `measured_role_first`): заданы мера соответствия и порог роли, и выбранная позиция занята элементом, мера которого достигает порога, причём она первая среди таких.';
const S6 = 'Более богатая статусная машина — та, где веса *сравниваются* между кандидатами и из них выбирается первый, максимальный, — записана в соседнем файле `StatusFromERR.v`: функция `find_primary` берёт среди прошедших ворота элемент с наибольшим весом, а при равных весах — созданный раньше (в общем виде это доказано теоремой `find_primary_spec`, файл `StructuralPath.v`);';
const S7 = 'функция `assign_status` присваивает статусы `PrimaryMax`, `SecondaryMax`, `Candidate`, `Invalid` (статус `HistoricalMax` в типе `Status` объявлен, но пока не присваивается).';
const S8 = 'Разрешение же по кандидатам — выбор одного из многих подходящих — формализовано в отдельном файле `Roles.v` механизмом `resolve_role` (через `L5_resolve`), и работает оно по *позициям*-кандидатам, не по весам `ERRProcess.v`: итог есть наименьшая из позиций-кандидатов и позиции по умолчанию, а при позиции по умолчанию, не меньшей хотя бы одного кандидата, — первый из кандидатов (`resolve_role_first_candidate`, файл `StructuralPath.v`; вариант без умолчания — `resolve_role_opt`).';
const S9 = 'Выбор по весу (`StatusFromERR.v`) и выбор по позиции (`Roles.v`) остаются двумя отдельными механизмами.';
const T1 = 'В текущей формализации эти части разнесены по файлам: вычисление веса и присвоение статуса `Candidate` / `Invalid` — в `ERRProcess.v`, сравнение весов и выбор первого по весу — в `StatusFromERR.v`, выбор первого из кандидатов по минимальной позиции — в `Roles.v` (`resolve_role`); общие теоремы о них — в `StructuralPath.v`.';
const T2 = 'Выбор по весу и выбор по позиции между собой не связаны; см. сноску выше и итог главы.';
const U1 = 'Эта синхронизация внесена (файл `StructuralPath.v`): предикаты `nonempty_structured` (существует занятая позиция), `first_occupied_position` (занятая позиция, не большая всякой другой занятой) и `normalized` (занятые позиции образуют начальный отрезок).';
const U2 = 'Доказано: первая занятая позиция есть в точности у непустой системы, и она одна (`first_position_iff_nonempty`, `first_occupied_position_unique`);';
const U3 = 'в нормализованной непустой системе она несёт номер $1$ (`normalized_first_number_one`);';
const U4 = 'без нормализации номер может быть иным (пример `sparse_first_is_5`:';
const U5 = 'В самом `TheoryOfSystems_Core_ERR.v` этих предикатов по-прежнему нет: они заданы поверх него.';
const V1 = 'Функция `pos_number p := S p` определена в файле `StructuralPath.v` как способ согласовать `Position := nat` с ToS-нумерацией позиций с единицы.';
const V2 = 'Там же доказано, что номера позиций суть в точности положительные числа (`pos_number_positive`, `pos_number_onto_positive`, `pos_number_injective`) и что индукция по номеру с базой $1$ следует из индукции по позициям (`number_ind_from_one`).';
const W1 = 'Поэтому «первая позиция» не следует из `StructuredSystem` автоматически — она требует, чтобы система была непустой; а чтобы первая занятая позиция несла номер $1$ — чтобы занятые позиции образовывали упорядоченный начальный ряд.';
const W2 = 'Оговорка о статусе: «система» здесь — содержательная интерпретация (`StructuredSystem` с частичным назначением мест); `ss_L5_valid` фиксирует лишь одну сторону единственности, первая позиция требует непустоты (§ 5.3–5.4), а `process_entity` сейчас присваивает только `Candidate`/`Invalid` (§ 5.5); общие теоремы о первой позиции, о выборе первого кандидата и о выборе по весу — в файле `StructuralPath.v`.';
const W3 = 'стандартный же тип `nat` Rocq включает $0$ как конструктор, и там, где о нём идёт речь, это оговаривается особо.';

{
  const { fix, add, save } = open('part02-ch05');

  // --- основной текст
  fix('По весу и решается, занять элементу роль или нет.', 'process_entity', {
    theorem: 'candidate_iff_positive_weight', file: SP,
    note: DONE + ' (формализацией): слова страницы получили теорему. candidate_iff_positive_weight : forall id lg sig sc, 1 <= rs_current_domain sc -> (ent_status (process_entity id lg sig sc) = Candidate <-> 0 < ent_weight (process_entity id lg sig sc)). ' + CL + '. Условие (номер домена не меньше единицы) названо в сноске 5; без него обратная сторона неверна (candidate_with_zero_weight).' });
  fix('Поэтому «первая позиция» не следует из `StructuredSystem` автоматически', 'StructuredSystem', {
    claim: W1,
    note: DONE + ': разведено, что нужно для первой позиции (непустота — first_position_iff_nonempty), а что — для номера 1 (начальный отрезок — normalized_first_number_one; без него sparse_first_is_5). ' + SP + ', ' + CL + '.' });
  fix('Оговорка о статусе: «система» здесь — содержательная интерпретация', 'ss_L5_valid', { claim: W2,
    note: 'ss_L5_valid — единственность позиции элемента (TheoryOfSystems_Core_ERR.v:573). «Первая позиция требует непустоты» — first_position_iff_nonempty (' + SP + '), ' + CL + '.' });
  fix('Оговорка о статусе: «система» здесь — содержательная интерпретация', 'process_entity', { claim: W2,
    note: 'process_entity (ERRProcess.v:194): статус — Candidate или Invalid (process_entity_two_statuses, ' + SP + '). Общие теоремы — в названном файле; ' + CL + '.' });
  fix('стандартный же тип `nat` Rocq-репозитория включает $0$ как конструктор', 'nat', { claim: W3,
    note: DONE + ': было «Rocq-репозитория». nat — тип стандартной библиотеки Rocq (Corelib.Init.Datatypes), конструктор O есть.' });

  // --- сноска 2
  fix('Формально это потребовало бы предиката вроде `nonempty_structured`', 'nonempty_structured', { file: SP, claim: U1,
    note: DONE + ' (формализацией): Definition nonempty_structured {L} (S : StructuredSystem L) : Prop := exists p, position_occupied S p (' + SP + ').' });
  fix('Формально это потребовало бы предиката вроде `nonempty_structured`', 'first_occupied_position', { file: SP, claim: U1,
    note: DONE + ' (формализацией): Definition first_occupied_position S p := position_occupied S p ' + AND + ' forall q, position_occupied S q -> p <= q (' + SP + ').' });
  add({ theorem: 'normalized', file: SP, claim: U1,
    note: 'Definition normalized S := forall p q, q <= p -> position_occupied S p -> position_occupied S q.' });
  add({ theorem: 'first_position_iff_nonempty', file: SP, claim: U2,
    note: 'first_position_iff_nonempty : nonempty_structured S <-> exists p, first_occupied_position S p. ' + CL + '.' });
  add({ theorem: 'first_occupied_position_unique', file: SP, claim: U2,
    note: 'first_occupied_position_unique : first_occupied_position S p -> first_occupied_position S q -> p = q. ' + CL + '.' });
  add({ theorem: 'normalized_first_number_one', file: SP, claim: U3,
    note: 'normalized_first_number_one : normalized S -> nonempty_structured S -> exists p, first_occupied_position S p ' + AND + ' pos_number p = 1. ' + CL + '.' });
  add({ theorem: 'sparse_first_is_5', file: SP, claim: U4,
    note: 'sparse_first_is_5 : first_occupied_position sparse_ss 5 ' + AND + ' pos_number 5 = 6 — занята одна позиция с техническим индексом 5, её номер 6. ' + CL + '.' });
  add({ theorem: 'position_occupied', file: CORE, claim: U5,
    note: 'Верно: в TheoryOfSystems_Core_ERR.v есть position_occupied (:587); новые предикаты определены через него в ' + SP + ', основной файл не менялся.' });

  // --- сноска 3
  fix('Функции `pos_number` в текущем коде нет', 'pos_number', { file: SP, claim: V1,
    note: DONE + ' (формализацией): Definition pos_number (p : Position) : nat := S p (' + SP + ').' });
  for (const th of ['pos_number_positive', 'pos_number_onto_positive', 'pos_number_injective', 'number_ind_from_one'])
    add({ theorem: th, file: SP, claim: V2, note: th + ' — ' + SP + ', § 2; ' + CL + '.' });

  // --- сноска 5
  fix('Подбор элемента под роль описан функцией `process_entity`', 'process_entity', { claim: S1,
    note: DONE + ': было «подбор элемента под роль… отвечает ли элемент требованию». process_entity (id legacy : nat) (sig : GateSignals) (scores : RawScores) — обработка одного элемента; роли среди аргументов нет (страница теперь говорит это прямо).' });
  fix('Подбор элемента под роль описан функцией `process_entity`', 'GateSignals', { claim: S1,
    note: 'Record GateSignals (ERRProcess.v:40) — семь булевых полей.' });
  fix('Подбор элемента под роль описан функцией `process_entity`', 'compute_gate', { claim: S1,
    note: 'compute_gate (ERRProcess.v:81) сводит семь сигналов в четыре условия: ig_err (элемент, роль, правило, статус налицо), ig_deps, ig_levels, ig_order — как перечислено на странице.' });
  fix('по воротам вычисляется *вес* (`compute_weight`)', 'compute_weight', { claim: S2,
    note: 'compute_weight : RawScores -> IntegrityGate -> nat (ERRProcess.v:96): по воротам и трём поданным числам. ' + CL + '.' });
  fix('по воротам вычисляется *вес* (`compute_weight`)', 'zero_gate_law', { claim: S2,
    note: 'zero_gate_law : gate_valid gate = false -> compute_weight scores gate = 0 (ERRProcess.v:158). ' + CL + '.' });
  fix('Нужно, однако, оговорить точно, что `process_entity` делает *сейчас*', 'Candidate', { claim: S3,
    note: 'Candidate — конструктор Status (ERRProcess.v:65). process_entity_status_by_gate (' + SP + '): статус = if gate_valid (compute_gate sig) then Candidate else Invalid.' });
  fix('Нужно, однако, оговорить точно, что `process_entity` делает *сейчас*', 'Invalid', { claim: S3,
    note: 'Invalid — конструктор Status (ERRProcess.v:66); process_entity_two_statuses (' + SP + '), ' + CL + '.' });
  add({ theorem: 'candidate_iff_positive_weight', file: SP, claim: S4,
    note: 'Условие названо на странице: 1 <= rs_current_domain sc (комментарий ERRProcess.v:54 — «D1-D6 = 1-6»). ' + CL + '.' });
  add({ theorem: 'measured_role_first', file: SP, claim: S5,
    note: DONE + ' (развилка — А): запись «роли с числовым требованием» оставлена. measured_role_first (раздел MeasuredRole: measure, threshold, fits e := threshold <=? measure e): при умолчании, не меньшем хотя бы одного кандидата, выбранная resolve_role позиция занята элементом e с threshold <= measure e и не больше всякой позиции с таким элементом. ' + CL + '.' });
  fix('Более богатая статусная машина — та, где веса *сравниваются* между кандидатами', 'Status', { claim: S7,
    note: 'Inductive Status := PrimaryMax | SecondaryMax | HistoricalMax | Candidate | Invalid (ERRProcess.v:61).' });
  fix('Более богатая статусная машина — та, где веса *сравниваются* между кандидатами', 'PrimaryMax', { claim: S7,
    note: 'Конструктор Status; присваивается assign_status (StatusFromERR.v:63) элементу, чей ent_id совпал с найденным первым.' });
  fix('Более богатая статусная машина — та, где веса *сравниваются* между кандидатами', 'SecondaryMax', { claim: S7,
    note: 'Конструктор Status; присваивается assign_status при весе, равном весу первого.' });
  fix('Более богатая статусная машина — та, где веса *сравниваются* между кандидатами', 'HistoricalMax', { claim: S7,
    note: 'Конструктор Status; ни одной функцией формализации не присваивается — страница говорит это.' });
  add({ theorem: 'assign_status', file: SF, claim: S7,
    note: 'assign_status (StatusFromERR.v:63) присваивает Invalid, PrimaryMax, SecondaryMax, Candidate — четыре статуса из пяти.' });
  fix('Полная статусно-весовая машина, где вес определяет первого среди кандидатов', 'find_primary', { claim: S6,
    note: DONE + ': было «потребовала бы связать ERRProcess.v с resolve_role». Машина записана в StatusFromERR.v: find_primary (:46) — допущенный воротами элемент наибольшего веса, при равных весах — с меньшим ent_legacy_idx.' });
  add({ theorem: 'find_primary_spec', file: SP, claim: S6,
    note: 'find_primary_spec : find_primary es = Some p -> In p es ' + AND + ' gate_valid (ent_gate p) = true ' + AND + ' (forall e, In e es -> gate_valid (ent_gate e) = true -> ent_weight e < ent_weight p ' + BS + '/ (ent_weight e = ent_weight p ' + AND + ' ent_legacy_idx p <= ent_legacy_idx e)). ' + CL + '. Существование — find_primary_exists.' });
  fix('Разрешение же по кандидатам — выбор одного из многих подходящих', 'resolve_role', { claim: S8,
    note: DONE + ' (формализацией): «выбор одного из подходящих» теперь доказан при названном условии — resolve_role_first_candidate (' + SP + '): позиция из списка, занята элементом, прошедшим проверку, не больше всякого кандидата. Без условия итог может не быть кандидатом (resolve_role_may_miss). ' + CL + '.' });
  fix('Разрешение же по кандидатам — выбор одного из многих подходящих', 'L5_resolve', { claim: S8,
    note: 'Definition L5_resolve candidates default := fold_right Nat.min default candidates (TheoryOfSystems_Core_ERR.v:633) — наименьшее из кандидатов и умолчания, как сказано на странице.' });
  add({ theorem: 'resolve_role_first_candidate', file: SP, claim: S8,
    note: 'resolve_role_first_candidate : (exists p, In p (role_candidates L S decide positions) ' + AND + ' p <= default) -> In (resolve_role …) positions ' + AND + ' (exists e, ss_assignment L S (resolve_role …) = Some e ' + AND + ' decide e = true) ' + AND + ' (forall q, In q (role_candidates …) -> resolve_role … <= q). ' + CL + '.' });
  add({ theorem: 'resolve_role_opt', file: SP, claim: S8,
    note: 'resolve_role_opt := l5_resolve_gen (role_candidates L S decide positions) : option Position; resolve_role_opt_first, resolve_role_opt_none_iff, resolve_role_opt_agrees — ' + CL + '.' });
  add({ theorem: 'resolve_role', file: RO, claim: S9,
    note: 'Верно: Roles.v не подключает ERRProcess.v и StatusFromERR.v; StatusFromERR.v не подключает Roles.v. Запись measured_role_first соединяет меру с разрешением по позиции отдельно, эти два файла не меняя.' });

  // --- сноска 6
  fix('В текущей формализации эти две части разнесены по файлам', 'resolve_role', { claim: T1,
    note: DONE + ': размещение по файлам дополнено (StatusFromERR.v, StructuralPath.v). «Выбор первого из кандидатов» — resolve_role_first_candidate.' });
  fix('Полная связка «вес определяет первого» требует их соединения', 'find_primary', { claim: T1,
    note: DONE + ': было «требует их соединения». Выбор первого по весу — find_primary (StatusFromERR.v:46); общий закон — find_primary_spec (' + SP + ').' });
  add({ theorem: 'resolve_role', file: RO, claim: T2,
    note: 'Верно: два механизма — find_primary (по весу) и resolve_role (по позиции) — в формализации не связаны.' });
  save();
}
