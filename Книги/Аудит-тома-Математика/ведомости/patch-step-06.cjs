// Шаг 6 (2026-11-12, слово автора «А — дописываем вторую сторону»): глава IV.2, теорема о сходимости «к себе».
// Запуск: node patch-step-06.cjs   (затем tom-links.cjs relocate + merge)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 6, слово автора «А»)';
const p = path.join(__dirname, 'part04-ch02.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
set('процесс Коши сходится «к себе»: его хвост укладывается', {
  theorem: 'cauchy_complete_self_two_sided',
  claim: 'И теорему `cauchy_complete_self` с её двусторонней формой `cauchy_complete_self_two_sided` — процесс Коши сходится «к себе»: его хвост укладывается в любую наперёд заданную точность вокруг любого достаточно далёкого приближения.',
  verdict: 'ok',
  note: DONE + ' — правка формализации: в CauchyReal.v добавлены cauchy_complete_self_lower (нижняя сторона: cauchy_le (cauchy_sub (cauchy_const (a n)) a) (cauchy_const eps)) и cauchy_complete_self_two_sided (обе стороны при одном N); прежняя cauchy_complete_self давала только верхнюю оценку; на странице добавлено имя двусторонней теоремы; Print Assumptions: Closed under the global context' });
set('И этот базовый результат доказан без завершённой бесконечности', {
  note: 'cauchy_rational_approx, cauchy_complete_self и добавленные шагом 6 cauchy_complete_self_lower, cauchy_complete_self_two_sided — «Closed under the global context», как и остальные леммы файла.' });
set('`CauchyReal.v` Rocq-репозитория ToS (каталог `src/`), 18 доказанных утверждений', {
  note: 'после шага 6 (12.11) в файле 21 Qed (4 Theorem + 17 Lemma), 0 Admitted, 0 Axiom; до шага было 19; число 18 на странице неверно и до, и после — правится шагом о фактических правках главы IV.2 (строка 12 таблицы); шапка файла исправлена шагом 6 (18 → 21); название шапки приведено верно.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part04-ch02.json: записей изменено ' + n + ', всего ' + j.records.length);
