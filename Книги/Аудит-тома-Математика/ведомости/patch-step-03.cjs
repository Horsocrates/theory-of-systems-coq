// Шаг 3 (2026-11-12, слово автора «А — делаем аудит настоящим»): записи ведомостей глав IV.1 и IV.6
// о файле ProcessAxiomAudit.v приводятся к новому тексту страниц и новому содержанию файла.
// Запуск: node patch-step-03.cjs   (затем tom-links.cjs relocate + merge по обеим ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 3, слово автора)';

function patch(file, edits, inserts) {
  const p = path.join(__dirname, file);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0;
  for (const e of edits) {
    const hit = j.records.filter((r) => (r.claim || '').startsWith(e.was));
    if (hit.length !== 1) throw new Error(file + ': ожидалась одна запись «' + e.was + '», найдено ' + hit.length);
    Object.assign(hit[0], e.set); n++;
  }
  for (const ins of inserts || []) {
    const i = j.records.findIndex((r) => (r.claim || '').startsWith(ins.after));
    if (i < 0) throw new Error(file + ': нет записи «' + ins.after + '»');
    if (!j.records.some((r) => r.claim === ins.rec.claim)) { j.records.splice(i + 1, 0, ins.rec); n++; }
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(file + ': записей изменено или добавлено ' + n + ', всего ' + j.records.length);
}

const SWEEP = 'сплошной прогон Print Assumptions после правок 2026-11-12';

patch('part04-ch01.json', [
  { was: 'Сам файл указывает, что опирается на результаты команды', set: {
      note: 'шапка ProcessAxiomAudit.v после шага 3: «Part II gathers the six key results into one proof object and runs Print Assumptions on it at every build; the statement about the whole formalization rests on a full Print Assumptions sweep (run separately)»' } },
  { was: 'Его теорема `axiom_minimal`', set: {
      theorem: 'key_results_hold',
      claim: 'Его определение `key_results_hold` собирает шесть ключевых результатов в один объект доказательства, и команда `Print Assumptions`, стоящая в файле сразу за ним, отвечает: «Closed under the global context» — ни один из шести не опирается ни на одно допущение.',
      page_price: 'без допущений', verdict: 'ok',
      note: DONE + ': было «Его теорема axiom_minimal — формализованная документация вывода…»; теоремы-вывески axiom_minimal, l4_witness_localized, classic_is_L3 и определение uses_classic из файла удалены (утверждали «L3 влечёт L3», нигде больше не использовались); key_results_hold — конъюнкция pauli_exclusion, spectral_gap_beta_1, weinberg_physical, trace_gauge_invariant_concrete, regge_equation_uniform, sm_anomaly_cancels; команда Print Assumptions стоит в файле и при сборке отвечает «Closed under the global context»' } },
  { was: 'результаты процессной части формализации зависят только от', set: {
      claim: 'В процессной части почти все объявления допущений не имеют вовсе; `classic` входит в несколько десятков теорем, а `classic` вместе с $L4$ — в одну группу, процессную теорему Больцано–Вейерштрасса (`ProcessBW.v`).',
      file: 'src/process/ProcessBW.v',
      page_price: 'почти все без допущений; classic — несколько десятков теорем; classic + L4 — одна группа (ProcessBW.v)', verdict: 'ok',
      note: DONE + ': было «зависят только от classic, и лишь изредка — от L4, причём L4 локализован в одном файле, посвящённом вариационному принципу»; ' + SWEEP + ', src/process: 4429 теорем и лемм, 4376 без допущений, 48 на classic (19 файлов), из них 7 ещё и на L4_witness — все в ProcessBW.v (process_BW и шесть лемм вокруг)' } },
  { was: 'процессная часть действительно обходится одним', set: {
      claim: 'процессная часть почти целиком обходится без допущений, $L3$ входит в немногие её теоремы, а $L4$ — в одну группу.',
      page_price: 'почти целиком без допущений; L3 — немногие теоремы; L4 — одна группа', verdict: 'ok',
      note: DONE + ': было «процессная часть действительно обходится одним L3, тогда как L4 … почти не востребован»; ' + SWEEP + ', src/process: 4376 из 4429 теорем и лемм без допущений (98,8 %), 48 на classic, 7 из них ещё и на L4_witness (ProcessBW.v)' } },
  { was: 'проверено четырьмя файлами `P4_Eliminates_*` и подтверждено аудитом', set: {
      claim: 'проверено четырьмя файлами `P4_Eliminates_*`: в выводе `Print Assumptions` для их теорем нет ни аксиомы бесконечности, ни аксиомы выбора.',
      file: 'src/foundation/P4_Eliminates_Infinity.v',
      page_price: 'ни аксиомы бесконечности, ни аксиомы выбора', verdict: 'ok',
      note: DONE + ': было «и подтверждено аудитом ProcessAxiomAudit.v»; ' + SWEEP + ': в P4_Eliminates_Infinity.v, P4_Eliminates_AC.v, P4_Eliminates_ATR.v все объявления замкнуты; в P4_Eliminates_Pi11.v 16 объявлений стоят на параметре eval_program (абстрактная функция вычисления программ — не аксиома бесконечности и не аксиома выбора), лемма pi11_negation — ещё и на classic' } },
  { was: 'Фундаментальных логических аксиом у ToS две', set: {
      note: 'после правок 2026-11-12 функциональной экстенсиональности в допущениях нет (прогон: 0); аксиом бесконечности и выбора в формализации нет; «мета-аудит» (ProcessAxiomAudit.v) записывает это комментарием, а проверяет сплошной прогон Print Assumptions' } },
  { was: '`ProcessAxiomAudit.v` (каталог `src/process/`), 13 доказанных утверждений.', set: {
      claim: '`ProcessAxiomAudit.v` (каталог `src/process/`), 10 доказанных утверждений.',
      note: DONE + ': было 13; после удаления трёх лемм-вывесок в файле 10 Qed' } },
], [
  { after: 'Его определение `key_results_hold`', rec: {
      line: 356, theorem: null, file: 'src/process/ProcessAxiomAudit.v',
      claim: 'Вывод обо всей формализации файл записывает комментарием, а проверяется он сплошным прогоном `Print Assumptions`: аксиом бесконечности, выбора, унивалентности и функциональной экстенсиональности нет; логических допущений в действии два — `classic` и `L4_witness`.',
      page_price: 'логических допущений два: classic и L4_witness; бесконечности, выбора, унивалентности, функциональной экстенсиональности нет', verdict: 'ok',
      note: DONE + ': ' + SWEEP + ' — functional_extensionality_dep: 0; не замкнутые теоремы стоят на Classical_Prop.classic (и трёх одноимённых объявлениях того же утверждения), ToS_Axioms.L4_witness, а в двух предметных местах — на модельных аксиомах Навье — Стокса (C_B_positive, B_coeff_bounded, параметры C_B, B_raw) и параметре eval_program; это не логические допущения; модулей выбора и унивалентности в импортах нет' } },
]);

patch('part04-ch06.json', [
  { was: 'Это *документированный* мета-аудит: разметка силы внесена автором', set: {
      verdict: 'ok',
      note: 'после шага 3 (12.11) расхождения записи файла с компилятором нет: вместо «Expected results» в комментарии Part II стоят действительные ответы компилятора, а о шести ключевых результатах в файле стоит сама команда Print Assumptions; разметка силы (FullyDerived и др.) остаётся оценкой автора — Print Assumptions показывает допущения, а не силу вывода' } },
  { was: 'Его теорема `axiom_minimal` утверждает содержательно', set: {
      theorem: 'key_results_hold',
      claim: 'Шесть ключевых результатов собраны в нём в один объект доказательства — `key_results_hold`, — и команда `Print Assumptions` при каждой сборке отвечает о нём: «Closed under the global context», допущений нет.',
      page_price: 'без допущений', verdict: 'ok',
      note: DONE + ': было «Его теорема axiom_minimal утверждает содержательно: ключевые результаты зависят только от classic»; теорема-вывеска удалена; key_results_hold — конъюнкция шести теорем, Print Assumptions стоит в файле и отвечает «Closed under the global context»' } },
  { was: 'зависят только от `classic` — то есть от $L3$', set: {
      claim: 'логических допущений в действии два — `classic`, то есть $L3$',
      note: 'classic в формализации — аксиома стандартной библиотеки Classical_Prop.classic, которую ToS_Axioms.v переэкспортирует (строка 31); одноимённые аксиомы объявлены ещё в foundation/Distinction.v:36, EVT_idx.v:338, settheory/BorelDeterminacy.v:21; ' + DONE + ': было «зависят только от classic — то есть от L3»' } },
  { was: 'закон достаточного основания `L4_witness` локализован', set: {
      theorem: null, file: 'src/ToS_Axioms.v',
      claim: '`L4_witness`, закон достаточного основания, входящий в теоремы девяти файлов, не считая файла аксиом',
      page_price: 'L4_witness — в теоремах девяти файлов', verdict: 'ok',
      note: DONE + ': было «локализован и появляется лишь в отдельных файлах (лемма l4_witness_localized)»; лемма-вывеска удалена; ' + SWEEP + ': от ToS_Axioms.L4_witness зависят объявления девяти файлов помимо ToS_Axioms.v — ProcessContinuumHypothesis.v, SchroederBernstein_ERR.v, analysis/BolzanoWeierstrass.v, process/ProcessBW.v, physics/SpectralDichotomy.v, physics/MeasurementProcess.v, physics/Entanglement.v, settheory/CardinalityWithoutChoice.v, zeta/ZeroStructure.v; напрямую аксиома применена в ProcessContinuumHypothesis.v:78 и в двух леммах ToS_Axioms.v, остальные наследуют' } },
  { was: 'Аксиомы выбора, бесконечности, унивалентности, функциональной экстенсиональности не используются.', set: {
      claim: 'аксиомы выбора, бесконечности, унивалентности, функциональной экстенсиональности не используются.',
      verdict: 'ok',
      note: 'после правок 2026-11-12 верно: ' + SWEEP + ' — functional_extensionality_dep: 0 (было 9 лемм в 5 файлах); модулей выбора (ClassicalChoice, Epsilon, IndefiniteDescription) и унивалентности в импортах нет' } },
  { was: 'Это *документированное* утверждение об аудите, опертое на', set: {
      claim: 'Это *документированное* утверждение об аудите; проверяет его сплошной прогон `Print Assumptions` по всем теоремам, а не сам файл.',
      note: DONE + ': было «опертое на Print Assumptions, а не машинная проверка всего репозитория одной командой»; статус назван честно — запись в комментарии файла, проверка — прогон (tools/tom-pa-all.cjs)' } },
  { was: 'Тип `DerivationStrength` и его применения — в файле', set: {
      note: 'файл на месте: src/process/ProcessAxiomAudit.v, 10 Qed (после шага 3), 0 Admitted, аксиом не объявляет; все объявления замкнуты' } },
]);
