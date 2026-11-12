// Часть V, шаг 7, страницы (2026-11-12, слово автора «Да — вносим девять мест»): глава V.1.
// Запуск: node patch-p5-step-07-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.1)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 7, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch01.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const RM = 'src/RealPointMetric.v', MS = 'src/stdlib/MetricSpace.v';
set('`MetricSpace.v` несёт восемнадцать проверенных лемм', {
  claim: '`MetricSpace.v` несёт двадцать четыре проверенные леммы и не использует ни одной аксиомы; из них к абстрактной секции относятся девять',
  verdict: 'ok',
  note: DONE + ': было «восемнадцать … семь»; после шага 7 в файле 24 Qed, в секции MetricSpaces девять лемм (прежние семь, const_limit_metric, const_cauchy_metric). Все — Closed under the global context.' });
set('Лемма именно такого вида — «процесс расстояний двух Коши-процессов есть Коши»', {
  theorem: 'cauchy_dist_is_cauchy', file: RM,
  claim: 'Лемма именно такого вида — «процесс расстояний двух Коши-процессов есть Коши» — теперь доказана: это `cauchy_dist_is_cauchy` из файла `RealPointMetric.v`, а сама оценка записана леммой `dist_of_dists_le`.',
  verdict: 'ok',
  note: DONE + ': было — названа cauchy_abs_is_cauchy, лемма о модуле ОДНОГО процесса. Добавлена cauchy_dist_is_cauchy : forall a b : CauchySeq, is_cauchy (fun n => Qabs (cs_seq a n - cs_seq b n)) и pointwise_dist_is_cauchy — то же для голых процессов. Closed under the global context.' });
set('поточечное расхождение на каждом уровне (понятие главы; отдельного', {
  claim: 'поточечное расхождение на каждом уровне (понятие главы; в семи опорных файлах имени нет, вне их — `rp_dist`, § 1.8.2)',
  verdict: 'ok',
  note: DONE + ': было «отдельного имени в коде нет» — имя есть: rp_dist (RealPointMetric.v), cs_rp_dist: n-й член равен Qabs (cs_seq a n - cs_seq b n). Слова приведены к сказанному на стр. 501–503 и в § 1.8.2.' });
set('Файл `CauchyReal.v` содержит лемму `cauchy_complete_ self`', {
  claim: 'Файл `CauchyReal.v` содержит лемму `cauchy_complete_self` и родственные ей — свойства *самих Коши-представителей*' });
set('Извлечение модуля как вычислимого объекта требует *информативного* варианта', {
  claim: 'Извлечение модуля как вычислимого объекта требует *информативного* варианта свойства — например, регулярного Коши-условия (`is_Regular_Cauchy` из `ProcessCore.v`) или явно приложенного модуля.' });
set('ToS не случайно *различает* `is_Cauchy` и `is_Regular_ Cauchy`', {
  claim: 'ToS не случайно *различает* `is_Cauchy` и `is_Regular_Cauchy`' });
set('Абстрактная метрическая рамка: метрическое пространство как параметрическая `Section`', {
  verdict: 'ok',
  note: DONE + ': число на странице приведено к файлу — «двадцать четыре проверенных результата» (было «восемнадцать»).' });
// у этой записи цитата — вся строка итога: заменить в ней число
{
  const r = j.records.find((x) => norm(x.claim).startsWith('Абстрактная метрическая рамка: метрическое пространство как параметрическая `Section`'));
  r.claim = r.claim.replace('восемнадцать проверенных результатов', 'двадцать четыре проверенных результата');
}
set('процесс расстояний есть Коши (`cauchy_abs_is_cauchy` — та', {
  theorem: 'cauchy_dist_is_cauchy', file: RM,
  claim: 'процесс расстояний есть Коши (`cauchy_dist_is_cauchy` — та оценка-набросок из § 1.4.2, ставшая теоремой)',
  verdict: 'ok',
  note: DONE + ': было — названа cauchy_abs_is_cauchy (лемма об одном процессе; она остаётся шагом построения rp_dist). Теперь названа лемма о двух процессах.' });
add({ theorem: 'dist_of_dists_le', file: RM,
  claim: 'а сама оценка записана леммой `dist_of_dists_le`.',
  note: 'Новая лемма шага 7: Qabs (Qabs (pm - qm) - Qabs (pn - qn)) <= Qabs (pm - pn) + Qabs (qm - qn) — дословно оценка, выписанная в главе формулой. Closed under the global context.' });
add({ theorem: 'QVec_dist_nonneg', file: MS,
  claim: 'с доказанными для него четырьмя свойствами метрики (`QVec_dist_nonneg`, `QVec_dist_zero`, `QVec_dist_sym`, `QVec_dist_triangle`).',
  note: 'Новая лемма шага 7: 0 <= QVec_dist v1 v2. Closed under the global context.' });
add({ theorem: 'QVec_dist_zero', file: MS,
  claim: '(`QVec_dist_nonneg`, `QVec_dist_zero`, `QVec_dist_sym`, `QVec_dist_triangle`)',
  note: 'Новая лемма шага 7: QVec_dist v v == 0. Closed under the global context.' });
add({ theorem: 'QVec_dist_sym', file: MS,
  claim: '`QVec_dist_sym`, `QVec_dist_triangle`).',
  note: 'Новая лемма шага 7: QVec_dist v1 v2 == QVec_dist v2 v1. Closed under the global context.' });
add({ theorem: 'QVec_dist_triangle', file: MS,
  claim: '`QVec_dist_triangle`). В настоящей главе',
  note: 'Новая лемма шага 7: QVec_dist v1 v3 <= QVec_dist v1 v2 + QVec_dist v2 v3 для v1 v2 v3 : QVec n — без условия на длины (у списков оно есть и необходимо). Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch01.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
