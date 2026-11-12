// Часть V, шаг 5, страницы (2026-11-12, слово автора «Да — вносим четыре места»): записи, зависевшие от правки слов.
// Запуск: node patch-p5-step-05-pages.cjs   (затем tom-links.cjs relocate + merge по ведомостям глав V.2, V.3, V.5, V.6)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 5, слово автора)';
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
patch('part05-ch02.json', [
  ['Аксиомного основания процессная обёртка не меняет: она ничего не', {
    claim: 'Саму теорему на язык процессов переносит `process_BW`: существует процесс Коши в $[a,b]$, к каждой далёкой стадии которого сколь угодно близко подходят члены последовательности со сколь угодно большими номерами.',
    page_price: 'те же L3 и L4',
    verdict: 'ok',
    note: DONE + ': было «она ничего не добавляет и не убавляет, перенося на язык процессов теорему, как она есть» — process_BW заключала лишь «существует процесс Коши». Теперь: exists L, is_Cauchy L /\\ in_interval a b L /\\ forall eps > 0, exists M0, forall M >= M0, forall N, exists k >= N, |L M - s k| < eps (свидетель — процесс левых концов бисекции). Это сильнее записи is_cluster_point базовой теоремы (строка 1 таблицы главы — отдельный шаг). Допущения: classic и L4_witness.' }],
]);
patch('part05-ch03.json', [
  ['Третий файл — `ProcessEVT.v` (133 строки)', {
    claim: 'Третий файл — `ProcessEVT.v` (158 строк)',
    verdict: 'ok',
    note: DONE + ': было «133 строки» при 137; после шага 5 в файле 158 строк, Qed — 9.' }],
  ['играет ту же роль, что `ProcessIVT.v` для теоремы о промежуточном значении', {
    claim: '`process_EVT` — она несёт всё содержание `EVT_complete`: процесс значений Коши, процесс точек отрезка, в которых эти значения достигаются, и мажорирующее свойство',
    verdict: 'ok',
    note: DONE + ': было — заключение process_EVT не упоминало функцию. Теперь: exists M c, is_Cauchy M /\\ in_interval a b c /\\ (forall n, f (c n) == M n) /\\ (forall x из отрезка, forall eps > 0, exists N, forall n >= N, f x <= M n + eps) — перенос EVT_complete в типы ProcessCore. Слова «тонкая обёртка, переносящая результат» стали верны. Closed under the global context.' }],
  ['Мосты Cauchy-совместимости (`evt_cauchy_ compat`),', {
    claim: 'В нём мосты Cauchy-совместимости (`evt_cauchy_compat`),',
    verdict: 'ok',
    note: DONE + ': имя на странице было разорвано переносом строки («evt_cauchy_ compat»); собрано на одной строке. ProcessEVT.v: EVT_ERR.is_Cauchy R <-> ProcessCore.is_Cauchy R; Closed under the global context.' }],
  ['`sup_process_cauchy`, `process_EVT`;', {
    claim: '`sup_process_cauchy` и `process_EVT`',
    note: 'ProcessEVT.v: a < b -> EVT_ERR.uniformly_continuous_on f a b -> ProcessCore.is_Cauchy (sup_process f a b) — содержательный перенос sup_process_is_Cauchy. После шага 1 Части V — Closed under the global context.' }],
  ['`ProcessEVT.v` оборачивает именно слой `EVT_ERR.v`', {
    assumptions: 'все девять утверждений файла: Closed under the global context',
    note: 'ProcessEVT.v:29: From ToS Require Import EVT_ERR. После шагов 1 и 5 Части V все девять утверждений файла — Closed under the global context; строка шапки о цене приведена к этому («none (EVT_ERR itself needs no classic since Nov 2026)»).' }],
]);
patch('part05-ch05.json', [
  ['Теорема `integral_is_process_construction`, предъявляющая процесс', {
    claim: 'Теорема `integral_is_process_construction` предъявляет процесс сумм как конструкцию — стадия есть сумма по $n+1$ ячейке, шаг положителен, ячейки покрывают отрезок в точности, шаг стремится к нулю, — но это *не* теорема интегрируемости, и выдавать одно за другое не следует.',
    note: DONE + ' — слова уточнены по новой формулировке: a < b -> (стадия n есть riemann_sum f a (integral_step a b n) (S n)) /\\ (0 < integral_step a b n) /\\ ((n+1) * integral_step a b n == b - a) /\\ (forall delta > 0, exists N, forall n >= N, integral_step a b n < delta). Было: «предъявляющая процесс сумм как конструкцию» — одно определение под «существует». Closed under the global context.' }],
]);
patch('part05-ch06.json', [
  ['Теорема `ftc_is_process_construction` предъявляет этот процесс ошибки', {
    claim: 'Теорема `ftc_is_process_construction` предъявляет этот процесс ошибки как конструкцию (E/R/R-форма) и собирает доказанное о нём: процесс сумм есть процесс Коши, а процесс ошибки называет нуль — при условиях теоремы сходимости, о которой ниже.',
    note: DONE + ' — слова уточнены по новой формулировке: Proper f -> udiff_on f f\' a b -> (стадия процесса ошибки) /\\ is_Cauchy (integral_process f\' a b) /\\ process_equiv (integral_process f\' a b) (const_process (f b - f a)) /\\ process_equiv (ftc_error_process f f\' a b) (const_process 0). Closed under the global context.' }],
]);
