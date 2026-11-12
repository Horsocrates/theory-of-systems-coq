// Часть V, шаг 8 (2026-11-12, слово автора «идём к шагу 8»): глава V.2 — записи, слова которых стали верны после
// доведения формализации (строка 1 таблицы главы V.2; строка 1 таблицы главы V.3 — равносильность двух описаний
// непрерывности). Записи, зависящие от правки слов, правит patch-p5-step-08-pages.cjs.
// Запуск: node patch-p5-step-08.cjs   (затем tom-links.cjs merge по затронутым ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 8, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function patch(name, edits) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  for (const [prefix, fields] of edits) {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
    if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
    Object.assign(hit[0], fields);
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(name + ': записей изменено ' + edits.length + ', всего ' + j.records.length);
}
const CL = ' Определение is_cluster_point заменено сильным: forall eps > 0, exists M0, forall M >= M0, forall N, exists k >= N, |cs_seq L M - s k| < eps — близость ко ВСЕМ далёким членам процесса, то есть к точке; прежняя запись сохранена как is_cluster_point_weak (следует из новой: cluster_point_implies_weak). Добавлена cluster_point_invariant: свойство не зависит от представителя (у прежней записи зависело — пример в пробном файле). bolzano_weierstrass передоказана для новой записи той же бисекцией; допущения прежние — classic и L4_witness.';
patch('part05-ch02.json', [
  ['всякая ограниченная последовательность рациональных чисел имеет *точку сгущения*', {
    verdict: 'ok', note: DONE + ' — слова те же, доведена формализация.' + CL }],
  ['Предикат `is_cluster_point` определён Коши-совместимо', {
    verdict: 'ok', note: DONE + ' — слова те же, доведена формализация.' + CL }],
]);
const CO = ' В stdlib/Topology.v добавлены open_preimage_implies_continuous и continuous_iff_open_preimage : continuous f <-> (forall S, is_open S -> is_open (fun x => S (f x))); до шага 8 была доказана одна сторона (continuous_preserves_open_preimage). Closed under the global context.';
patch('part05-ch03.json', [
  ['И его ToS не постулирует отдельно, а *выводит* из', { verdict: 'ok', note: DONE + ' (шаг главы V.2) — слова те же, доведена формализация.' + CO }],
  ['Сама непрерывность есть *конституция* — в двух равносильных формах', { verdict: 'ok', note: DONE + ' (шаг главы V.2) — слова те же, доведена формализация.' + CO }],
  ['| непрерывность ($\\delta$-$\\varepsilon$ $\\equiv$ прообраз открытого открыт)', { verdict: 'ok', note: DONE + ' (шаг главы V.2) — слова те же, доведена формализация.' + CO }],
]);
