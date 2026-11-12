// Шаг 13 (2026-11-12, слово автора «Да — вносим»): пять фактических правок глав IV.5 и IV.6.
// Запуск: node patch-step-13.cjs   (затем tom-links.cjs relocate + merge по обеим ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 13, слово автора)';

function run(file, edits) {
  const p = path.join(__dirname, file);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0;
  for (const e of edits) {
    const hit = j.records.filter((r) => (r.claim || '').startsWith(e.was));
    if (hit.length !== 1) { if (e.optional && hit.length === 0) { console.log('  нет записи (необязательная): ' + e.was); continue; } throw new Error(file + ': ожидалась одна запись «' + e.was + '», найдено ' + hit.length); }
    Object.assign(hit[0], e.set); n++;
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(file + ': записей изменено ' + n + ', всего ' + j.records.length);
}

run('part04-ch05.json', [
  { was: 'Бинарная — проще и конструктивнее', set: {
      claim: 'Бинарная — проще и прозрачнее',
      page_price: '', verdict: 'ok',
      note: DONE + ': было «проще и конструктивнее» — остаток контраста, снятого 12.11; binary_processes_not_enumerable (ProcessDiagonal.v:108) и unit_interval_uncountable_trisect_v2 (ShrinkingIntervals_ERR.v:3569) обе «Closed under the global context»' } },
  { was: 'Имя файла `no_intermediate_process_', set: {
      claim: 'Второе имя теоремы — `no_intermediate_process_type` — называет суть точнее заглавного',
      verdict: 'ok',
      note: DONE + ': было «Имя файла `no_intermediate_process_ type`»; это второе имя теоремы (ProcessContinuumHypothesis.v:642), файла с таким именем нет; имя теперь стоит на одной строке' } },
  { was: 'Центральная теорема названа в файле `process_continuum_', optional: true, set: {
      claim: 'Центральная теорема названа в файле `process_continuum_hypothesis` — «процессная континуум-гипотеза».',
      verdict: 'ok',
      note: DONE + ': имя было разорвано переносом строки и на странице читалось с пробелом; теперь на одной строке (ProcessContinuumHypothesis.v:619)' } },
]);

run('part04-ch06.json', [
  { was: 'Ядро тома стоит на нуле аксиом, два результата Части IV', set: {
      claim: 'Ядро тома стоит на нуле аксиом — включая несчётность процессов отрезка; дихотомия Части IV — на $L3+L4$',
      page_price: 'несчётность — 0 аксиом; дихотомия — L3 + L4', verdict: 'ok',
      note: DONE + ': было «два результата Части IV — на L3 и на L3+L4» — место, пропущенное при правке 12.11; unit_interval_uncountable_trisect_v2 и process_uncountable — «Closed under the global context»; на classic + L4_witness в Части IV один результат — process_continuum_hypothesis' } },
  { was: '*элементы — результаты и их классификации; роли — мета-уровневая значимость', set: {
      claim: '*элементы — шкала силы вывода и классификации аксиом; роли — мета-уровневый анализ, честная оценка; правила — классифицировать каждый результат по силе*',
      verdict: 'ok',
      note: DONE + ': пересказ приведён к шапке ProcessAxiomAudit.v — «Elements: DerivationStrength, axiom classifications; Roles: meta-level analysis, honest assessment; Rules: classify each result by derivation strength»; у ProcessDerivedVsConsistent.v шапка своя (IFStrength, DerivationRecord; Forced/Natural/Chosen)' } },
]);
