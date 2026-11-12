// Шаг 5 (2026-11-12, слово автора «Да — вносим»): фактические правки главы IV.1 -- приписка несовместимости,
// числа в сносках 8, 11, 13, 14, 15, слова сноски 15 о выборе.
// Запуск: node patch-step-05.cjs   (затем tom-links.cjs relocate + merge)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 5, слово автора)';
const p = path.join(__dirname, 'part04-ch01.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
set('Слой несовместимости добавляет: при точном определении завершённого бесконечного объекта', {
  theorem: 'completed_inf_contradicts_P4', file: 'src/foundation/P4CompletedInfinity.v',
  claim: 'Слой несовместимости добавляет: при точном определении завершённого бесконечного объекта он с $P4$ несовместим (`P4CompletedInfinity.v`, теорема `completed_inf_contradicts_P4`; `nat` при этом — правило индукции, не готовое множество)',
  verdict: 'ok',
  note: DONE + ': было «(`P4_Eliminates_Infinity`: `nat` — правило индукции, не готовое множество)» — это файл слоя ненужности; теорема несовместимости — completed_inf_contradicts_P4 (P4CompletedInfinity.v:64), для nat — nat_not_completed_under_P4 (:146)' });
set('`P4_Eliminates_Infinity.v` (каталог `src/foundation/`), 12 доказанных утверждений', {
  claim: '`P4_Eliminates_Infinity.v` (каталог `src/foundation/`), 10 доказанных утверждений, 0 `Admitted`, 0 новых аксиом.',
  verdict: 'ok', note: DONE + ': было 12; в файле 10 Qed (9 лемм и 1 теорема); шапка файла исправлена тем же шагом (12 → 10)' });
set('`P4_Eliminates_ATR.v` (каталог `src/foundation/`), 15 доказанных утверждений', {
  claim: '`P4_Eliminates_ATR.v` (каталог `src/foundation/`), 17 доказанных утверждений, 0 `Admitted`, 0 новых аксиом.',
  verdict: 'ok', note: DONE + ': было 15; в файле 17 Qed (16 лемм и 1 теорема); шапка файла исправлена тем же шагом (15 → 17)' });
set('`P4CompletedInfinity.v` (каталог `src/foundation/`), 12 доказанных утверждений', {
  claim: '`P4CompletedInfinity.v` (каталог `src/foundation/`), 9 доказанных утверждений, 0 `Admitted`, 0 новых аксиом. Это ядро, на которое опираются файлы `P4ProhibitsAC.v` и `P4ProhibitsImpredicative.v`.',
  verdict: 'ok', note: DONE + ': было 12; в файле 9 Qed (4 леммы и 5 теорем); шапка файла исправлена тем же шагом (12 → 9); оба названных файла импортируют P4CompletedInfinity' });
set('`P4ProhibitsAC.v` (каталог `src/foundation/`), 10 доказанных утверждений', {
  claim: '`P4ProhibitsAC.v` (каталог `src/foundation/`), 12 доказанных утверждений, 0 `Admitted`, 0 новых аксиом; опирается на `P4CompletedInfinity.v`.',
  verdict: 'ok', note: DONE + ': было 10; после шага 4 в файле 12 Qed (7 лемм и 5 теорем), 0 аксиом' });
set('`P4ProhibitionSynthesis.v` (каталог `src/foundation/`), 8 доказанных утверждений', {
  claim: '`P4ProhibitionSynthesis.v` (каталог `src/foundation/`), 6 доказанных утверждений, 0 `Admitted`.',
  verdict: 'ok', note: DONE + ': было 8; в файле 6 Qed (5 теорем и 1 лемма); шапка файла исправлена шагом 4' });
set('Файл доказывает `P4_prohibits_three`', {
  claim: 'Файл доказывает `P4_prohibits_three` (несовместимость с тремя вещами: завершёнными множествами, функцией выбора, взятой как завершённый график, [[Парадокс Рассела|парадоксом Рассела]])',
  note: DONE + ': было «полной аксиомой выбора»; три конъюнкта (:30) — условная несовместимость завершённого множества; AC_gives_completed_graph (функция выбора с графиком из выбранных пар, содержащим пару на всяком индексе); противоречивость множества Рассела. Сомнительным остаётся третье: в противоречивости множества Рассела P4 не участвует (лемма названа russell_contradiction_without_P1)' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part04-ch01.json: записей изменено ' + n + ', всего ' + j.records.length);
