// Часть I, шаг 7, страницы (2026-11-13, слово автора «Вноси»): 12 правок главы I.4 (места 12–22) внесены;
// формализация — src/foundation/ERRStratification.v.
// Запуск: node patch-p01-step-07-pages.cjs   (затем relocate + merge по part01-ch04)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 7, слово автора)';
const ST = 'src/foundation/ERRStratification.v';
const CL = 'Closed under the global context';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const a = open('part01-ch04.json');
const many = (names, claim, price) => { for (const [th, note] of names) a.add({ theorem: th, file: ST, page_price: price || '', claim, note: (note ? note + ' ' : '') + CL + '.' }); };

// ---- место 12
a.fix('теорема `self_application_not_self_membership` разделяет два смысла', 'self_application_not_self_membership', {
  theorem: 'self_application_vs_self_membership', file: ST,
  claim: 'теорема `self_application_vs_self_membership` (файл `ERRStratification.v`) разделяет два смысла «E/R/R применяется к себе».',
  note: DONE + ': было `self_application_not_self_membership` — два вычисления над двумя таблицами. self_application_vs_self_membership : stratified err_meta_system /\\ (forall k, ~ clos_trans nat (ref_rel err_meta_system) k k) /\\ ~ stratified russell_system /\\ ref_rel russell_system 0 0. ' + CL + '.' });
const C2 = 'Разделяет она их свойством, а не двумя вычислениями: таблица самоприменения *стратифицирована* — все ссылки идут строго вниз, от правил к ролям и от ролей к элементам, — и потому не имеет ни прямой, ни опосредованной самореференции; таблица Рассела содержит компонент, ссылающийся на себя, и стратифицированной быть не может (`stratified_no_reference_cycle`, `paradox_tables_not_stratified`).';
many([['stratified_no_reference_cycle', 'forall E, stratified E -> forall k, ~ clos_trans nat (ref_rel E) k k.'],
      ['paradox_tables_not_stratified', 'forall p : ParadoxType, ~ stratified (paradox_system p).']], C2, 'без аксиом');

// ---- место 13
const C3 = 'Самосогласованность E/R/R доказана Rocq-теоремами, без аксиом; таблица, записанная по содержательному разбору ниже — три элемента, три роли, три правила, — стратифицирована тоже (`err_self_application_stratified`).';
a.fix('Самосогласованность E/R/R доказана отдельной Rocq-теоремой, без аксиом; содержательный разбор', 'err_self_well_formed', {
  claim: C3, page_price: 'без аксиом',
  note: DONE + ': было «содержательный разбор ниже разворачивает то, что эта теорема фиксирует» — теорема err_self_well_formed говорит о таблице из трёх компонентов, разбор — о девяти. Таблица по разбору теперь записана и стратифицирована. err_self_well_formed — ' + CL + '.' });
many([['err_self_application_stratified', 'Таблица из девяти компонентов (три элемента, три роли, три правила) стратифицирована.']], C3, 'без аксиом');
const C4 = 'Самосогласованность E/R/R доказана машинно — и для краткой таблицы из трёх компонентов (`err_self_well_formed`, `PrinciplesToERR.v`; см. замечание выше), и для таблицы из девяти, записанной по приведённому разбору (`err_self_application_stratified`, `ERRStratification.v`); содержательная проверка с ней согласна:';
a.fix('Самосогласованность E/R/R доказана машинно (`err_self_well_formed`, `PrinciplesToERR.v`; см. замечание выше); содержательная', 'err_self_well_formed', {
  claim: C4, note: DONE + ': названы обе таблицы — краткая из трёх компонентов и записанная по разбору из девяти.' });
a.fix('самоприменение E/R/R *не обнаруживает структурного нарушения* по тем же признакам', 'is_well_formed', {
  note: 'закрыто 13.11 (Часть I, шаг 7): фраза автора не менялась. Признак «самореференция» проверяется стратификацией (нет цикла ссылок никакой длины); признак «смешение категорий» теперь выразим — запись ERRSystemM, every_ERRSystem_unmixed, russell_mixed_is_mixed (ERRStratification.v).' });

// ---- место 14
a.fix('зафиксирован критерий: система *хорошо сформирована*, если каждый её компонент', 'is_well_formed', {
  theorem: 'is_well_formed_spec', file: ST,
  claim: 'зафиксирован критерий: система *хорошо сформирована*, если ни один её компонент не ссылается на себя и ни одно правило не ссылается на правило (`is_well_formed_spec`); категория у компонента одна по устройству записи.[^17]',
  note: DONE + ': было «каждый её компонент относится ровно к одной E/R/R-категории и нет самореференции через категории». is_well_formed_spec : is_well_formed E = true <-> (forall k < n, refs k k = false) /\\ (правило не ссылается на правило). ' + CL + '.' });
const C5 = 'Более сильное условие — *стратификация*: всякая ссылка идёт строго вниз по рангу категории; оно влечёт критерий и исключает *самореференцию* через категории любой длины (`stratified_well_formed`, `stratified_no_reference_cycle`).';
many([['stratified_well_formed', 'forall E, stratified E -> is_well_formed E = true.'], ['stratified_no_reference_cycle', '']], C5, '');
const FN17 = 'Первая проверяет, что ни один компонент не ссылается на себя; вторая — что ни одно правило не ссылается на правило (ссылку элемента на правило она допускает).';
const N17 = 'закрыто 13.11 (Часть I, шаг 7): формулировки двух проверок теперь приведены в самой сноске и сведены теоремой is_well_formed_spec.';
a.fix('Точные формулировки `no_self_reference` и `rules_above_elements` разбираются', 'no_self_reference', { note: N17 });
a.fix('Точные формулировки `no_self_reference` и `rules_above_elements` разбираются', 'rules_above_elements', { note: N17 });
a.add({ theorem: null, claim: FN17, note: 'no_self_reference и rules_above_elements — ERRWellFormedness.v:61, :72; их совместное содержание — is_well_formed_spec.' });
const C6 = 'Вместе они и составляют критерий (`is_well_formed_spec`, файл `ERRStratification.v`); взаимную ссылку двух компонентов критерий принимает, стратификация — исключает (`two_cycle_well_formed`, `two_cycle_not_stratified`).';
many([['is_well_formed_spec', ''], ['two_cycle_well_formed', 'is_well_formed two_cycle_system = true.'], ['two_cycle_not_stratified', '~ stratified two_cycle_system.']], C6, '');

// ---- место 16
a.fix('Парадоксы — именно те конструкции, для которых такой разбор *невозможен*', 'is_well_formed', {
  note: 'закрыто 13.11 (Часть I, шаг 7): фраза автора не менялась; следом сказано, что в записи ERRSystem категория у компонента одна и проверяется ссылка на себя, а совмещение категорий записано отдельной структурой.' });
const C7 = 'В записи `ERRSystem` категория у компонента одна, и проверяется в ней другое — ссылка компонента на себя; совмещение категорий записано отдельной структурой, где компонент может выступать в нескольких категориях: там «Element = Rule» Рассела есть смешение, а ни одна таблица `ERRSystem` смешения не содержит (`russell_mixed_is_mixed`, `every_ERRSystem_unmixed`).';
many([['russell_mixed_is_mixed', '~ unmixed russell_mixed (запись ERRSystemM: компонент может выступать в нескольких категориях).'],
      ['every_ERRSystem_unmixed', 'forall E : ERRSystem, unmixed (as_multi E).']], C7, '');

// ---- место 17 (сноска 18)
a.fix('Главная теорема `all_paradoxes_ill_formed` устанавливает, что все классические парадоксы', 'all_paradoxes_ill_formed', {
  claim: 'Теорема `all_paradoxes_ill_formed` устанавливает, что таблицы пяти названных парадоксов (Рассел, Лжец, Грелинг, Кантор, Бурали-Форти) критерий не проходят; записей при этом три — таблицы Кантора и Бурали-Форти повторяют таблицы Рассела и Грелинга.',
  note: DONE + ': было «все классические парадоксы — структурно ill-formed». all_paradoxes_ill_formed : forall p : ParadoxType, is_well_formed (paradox_system p) = false. ' + CL + '.' });

// ---- место 19 (сноска 23)
a.fix('Полный синтез — в теореме `paradox_diagnosis_synthesis`, объединяющей:', 'paradox_diagnosis_synthesis', {
  claim: 'Полный синтез — в теореме `paradox_diagnosis_synthesis`, объединяющей: (1) ill-formed-статус всех парадоксов; (2) контрапозитив `well_formed_paradox_free`; (3) три равенства о виде нарушения, приписанном парадоксу таблицей `paradox_violation` (Рассел, Лжец, Грелинг).',
  note: DONE + ': было «(3) точную классификацию нарушений для каждого парадокса». Третий член — три равенства reflexivity на определении-таблице paradox_violation. ' + CL + '.' });

// ---- место 20
a.fix('Это зафиксировано теоремой `well_formed_paradox_free`: хорошая сформированность *исключает*', 'well_formed_paradox_free', {
  claim: 'Это зафиксировано теоремой `well_formed_paradox_free`: хорошо сформированная таблица не совпадает ни с одной из таблиц парадоксов.',
  note: DONE + ': было «хорошая сформированность исключает парадоксальность». well_formed_paradox_free : is_well_formed S = true -> forall p, S <> paradox_system p. ' + CL + '.' });
const C8 = 'Общее утверждение даёт стратификация: в стратифицированной таблице нет самореференции никакой длины, а у каждой таблицы парадокса есть компонент, ссылающийся на себя (`stratified_no_reference_cycle`, `paradox_tables_self_referential`, `stratified_excludes_paradox_tables`).';
many([['stratified_no_reference_cycle', ''], ['paradox_tables_self_referential', 'forall p, ref_rel (paradox_system p) 0 0.'],
      ['stratified_excludes_paradox_tables', 'forall E, stratified E -> forall p, E <> paradox_system p.']], C8, '');

// ---- место 21 (сноски 24 и 25)
a.fix('Это зафиксировано в `ERRWellFormedness.v` теоремой `nat_well_formed`', 'nat_well_formed', {
  note: 'закрыто 13.11 (Часть I, шаг 7): фраза не менялась; следом сказано, что в той таблице ссылок нет и что таблица со ссылками стратифицирована. nat_well_formed — ' + CL + '.' });
const C9 = 'В той таблице ссылок между компонентами нет, а таблица без ссылок проходит проверку при любых категориях (`no_references_well_formed`). Таблица натуральных чисел со ссылками — правило «преемник» ссылается на элемент и на роль, роль на элемент — стратифицирована (`nat_system_refs_stratified`, файл `ERRStratification.v`).';
many([['no_references_well_formed', 'forall n cat, is_well_formed (mkERRSys n cat (fun _ _ => false)) = true.'],
      ['nat_system_refs_stratified', 'stratified nat_system_refs.']], C9, '');
a.fix('Теорема `chess_well_formed`.', 'chess_well_formed', {
  claim: 'Теорема `chess_well_formed`; таблица шахмат записана без ссылок между компонентами (см. предыдущую сноску).',
  note: DONE + ': добавлено, что таблица шахмат записана без ссылок. chess_well_formed — ' + CL + '.' });

// ---- место 22
a.fix('E/R/R-диагностика отличает парадоксы от хорошо сформированных систем точно и формально.', 'is_well_formed', {
  claim: 'E/R/R-диагностика отличает разобранные парадоксы от разобранных хорошо сформированных систем формально.',
  note: DONE + ': было «точно и формально». Равносильности «парадокс ⟺ не проходит критерий» нет: контрпримеры в обе стороны названы следом.' });
const C10 = 'Сам критерий `is_well_formed` слабее и точной границы не даёт: он принимает взаимную ссылку двух компонентов и отклоняет таблицу без самореференции, в которой правило ссылается на другое правило (`two_cycle_well_formed`, `rule_refers_other_rule_ill_formed`).';
many([['two_cycle_well_formed', ''], ['rule_refers_other_rule_ill_formed', 'no_self_reference rule_refers_other_rule = true /\\ is_well_formed rule_refers_other_rule = false.']], C10, '');
a.save();
