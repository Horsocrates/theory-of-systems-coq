// Шаг 7 (2026-11-12, слово автора «Да — вносим»): четыре фактические правки главы IV.2.
// Запуск: node patch-step-07.cjs   (затем tom-links.cjs relocate + merge)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 7, слово автора)';
const p = path.join(__dirname, 'part04-ch02.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
set('Файл `ProcessGeneral.v` проводит между ними мост', {
  theorem: 'is_Cauchy_iff_is_cauchy', file: 'src/CauchyProcessBridge.v',
  claim: 'Мост между ними проводит файл `CauchyProcessBridge.v` — к нему § 2.5 и вернётся.',
  verdict: 'ok',
  note: DONE + ': было «Файл `ProcessGeneral.v` проводит между ними мост»; в ProcessGeneral.v нет is_Cauchy; мост is_Cauchy ↔ is_cauchy — лемма is_Cauchy_iff_is_cauchy (CauchyProcessBridge.v:47), как глава и пишет в § 2.5' });
set('(лемма `cauchy_Q_equiv` сводит свойство Коши второй линии к общему случаю третьей), но первая и вторая линии', {
  theorem: 'is_Cauchy_iff_is_cauchy',
  claim: '(лемма `cauchy_Q_equiv` сводит свойство Коши второй линии к общему случаю третьей; лемма `is_Cauchy_iff_is_cauchy` связывает первую линию со второй)',
  verdict: 'ok',
  note: DONE + ': было «…, но первая и вторая линии не отождествлены машинно как единый терм» — оговорка, которую § 2.5.4 той же главы объявляет снятой; мосты is_Cauchy_iff_is_cauchy (CauchyProcessBridge.v:47) и process_equiv_iff_cauchy_equiv (:58) доказаны' });
set('`ProcessArithmetic.v` Rocq-репозитория ToS (каталог `src/process/`), 13 доказанных утверждений', {
  claim: '`ProcessArithmetic.v` Rocq-репозитория ToS (каталог `src/process/`), 17 доказанных утверждений, 0 `Admitted`.',
  verdict: 'ok',
  note: DONE + ': было 13; в файле 17 Qed (4 Theorem + 13 Lemma), 0 Admitted; шапка файла исправлена тем же шагом (13 → 17, два места)' });
set('`CauchyReal.v` Rocq-репозитория ToS (каталог `src/`), 18 доказанных утверждений', {
  claim: '`CauchyReal.v` Rocq-репозитория ToS (каталог `src/`), 21 доказанное утверждение, 0 `Admitted`, 0 аксиом.',
  verdict: 'ok',
  note: DONE + ': было 18; после шага 6 в файле 21 Qed (4 Theorem + 17 Lemma), 0 Admitted, 0 Axiom; название шапки приведено верно' });
set('Имя `mass_gap` стоит читать как *технический термин*', {
  theorem: 'has_process_mass_gap', file: 'src/process/ProcessBounds.v',
  claim: 'Имя `has_process_mass_gap` стоит читать как *технический термин* процессной формализации',
  note: DONE + ': было «Имя `mass_gap`» — часть имени; структура в файле называется has_process_mass_gap (ProcessBounds.v:39); оговорка «не физический массовый зазор» — чтение главы' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part04-ch02.json: записей изменено ' + n + ', всего ' + j.records.length);
