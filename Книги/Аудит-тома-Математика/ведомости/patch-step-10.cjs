// Шаг 10 (2026-11-12, слово автора «Да — вносим»): пять фактических правок глав IV.3 и IV.4.
// Запуск: node patch-step-10.cjs   (затем tom-links.cjs relocate + merge по обеим ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 10, слово автора)';

function run(file, edits) {
  const p = path.join(__dirname, file);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0;
  for (const e of edits) {
    const hit = j.records.filter((r) => (r.claim || '').startsWith(e.was));
    if (hit.length !== 1) { if (e.optional && hit.length === 0) continue; throw new Error(file + ': ожидалась одна запись «' + e.was + '», найдено ' + hit.length); }
    Object.assign(hit[0], e.set); n++;
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(file + ': записей изменено ' + n + ', всего ' + j.records.length);
}

run('part04-ch03.json', [
  { was: 'для всякого перечисления процессов найдётся процесс Коши', set: {
      claim: 'для всякого *регулярного* перечисления процессов отрезка $[0,1]$ найдётся процесс Коши (лежащий в том же отрезке), *не эквивалентный* ни одному элементу перечисления.',
      verdict: 'ok',
      note: DONE + ': добавлено условие теоремы — process_uncountable (ProcessUncountable.v:88) доказана при valid_regular_enumeration E: каждый член перечисления есть регулярный процесс Коши со значениями в [0,1] (ShrinkingIntervals_ERR.v:1089); было «для всякого перечисления процессов»' } },
  { was: 'Иначе говоря, никакое перечисление представителей не покрывает', set: {
      claim: 'Иначе говоря, никакое регулярное перечисление представителей не покрывает все классы эквивалентности отрезка — всегда есть класс, в перечислении не представленный.',
      verdict: 'ok',
      note: DONE + ': вывод приведён к доказанному — регулярные перечисления процессов отрезка [0,1]; было «никакое перечисление представителей»' } },
  { was: '| совместимость (`add_compat`)', optional: true, set: {
      theorem: 'cauchy_add_compat',
      claim: '| совместимость (`cauchy_add_compat`); мост репрезентаций | согласованность | Rule (конкр.) |',
      verdict: 'ok', note: DONE + ': было сокращение `add_compat`; полное имя — cauchy_add_compat (CauchyReal.v:180)' } },
  { was: 'совместимость (`add_compat`)', optional: true, set: {
      theorem: 'cauchy_add_compat',
      claim: 'совместимость (`cauchy_add_compat`); мост репрезентаций',
      verdict: 'ok', note: DONE + ': было сокращение `add_compat`; полное имя — cauchy_add_compat (CauchyReal.v:180)' } },
]);

run('part04-ch04.json', [
  { was: 'Theorem process_uncountable : forall E : Enumeration', set: {
      claim: 'Theorem process_uncountable : forall E : ShrinkingIntervals_ERR.Enumeration, ShrinkingIntervals_ERR.valid_regular_enumeration E -> exists D : RealProcess, ProcessCore.is_Cauchy D /\\ (forall m, 0 <= D m /\\ D m <= 1) /\\ (forall n, ~ ProcessCore.process_equiv D (E n)).',
      verdict: 'ok',
      note: DONE + ': блок кода приведён дословно, с приставками модулей (process/ProcessUncountable.v:88–94); было без приставок' } },
  { was: 'Условие допустимости — *регулярность* перечисления (`valid_regular`)', set: {
      theorem: 'valid_regular_enumeration', file: 'src/ShrinkingIntervals_ERR.v',
      claim: 'Условие допустимости — *регулярность* перечисления (`valid_regular_enumeration`), управляемый доступ к каждому процессу (§ 4.4).',
      verdict: 'ok',
      note: DONE + ': было `valid_regular` — такого имени нет; определение — valid_regular_enumeration (ShrinkingIntervals_ERR.v:1089)' } },
  { was: 'а *правило* о процессах: ни один процесс-нумератор не охватывает', set: {
      claim: 'а *правило* о процессах: ни один *регулярный* процесс-нумератор не охватывает все классы-роли.',
      note: DONE + ': добавлено слово «регулярный» — теорема доказана для valid_regular_enumeration; ниже в том же разборе глава сама пишет «любой регулярный процесс-нумератор»' } },
]);
