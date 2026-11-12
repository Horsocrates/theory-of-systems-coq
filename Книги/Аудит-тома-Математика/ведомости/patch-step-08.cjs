// Шаг 8 (2026-11-12, слово автора «А — делаем схему кодом»): 0,999… = 1 на линии CauchySeq.
// Запуск: node patch-step-08.cjs   (затем tom-links.cjs relocate + merge по обеим ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 8, слово автора «А»)';
const F = 'src/process/ProcessNinePoint.v';

function load(file) { const p = path.join(__dirname, file); return { p, j: JSON.parse(fs.readFileSync(p, 'utf8')) }; }
function save(x, file, n) { fs.writeFileSync(x.p, JSON.stringify(x.j, null, 1) + '\n'); console.log(file + ': записей изменено или добавлено ' + n + ', всего ' + x.j.records.length); }
function one(j, prefix) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  return hit[0];
}

{ // глава IV.2
  const x = load('part04-ch02.json'); const j = x.j; let n = 0;
  Object.assign(one(j, 'определение конкретного представителя для $0{,}999…$'), {
    theorem: 'nine_process_equiv_one', file: F,
    claim: 'Точная форма — определение конкретного представителя для $0{,}999…$, постоянного представителя для единицы и доказательство их эквивалентности по `cauchy_equiv`; в файле `process/ProcessNinePoint.v` она записана так:',
    verdict: 'ok',
    note: DONE + ': схема стала кодом — в ProcessNinePoint.v добавлены nine_process, one_process, nine_process_lt_one_stagewise и Theorem nine_process_equiv_one : cauchy_equiv nine_process one_process (доказательство — теорема первой линии nine_equiv_one, линии совпадают по CauchyProcessBridge); Closed under the global context' }); n++;
  const rec = one(j, 'Definition nine_process : CauchySeq :=');
  Object.assign(rec, {
    theorem: 'nine_process', file: F,
    claim: 'Definition nine_process : CauchySeq := to_CauchySeq nine_raw nine_raw_is_Cauchy.',
    verdict: 'ok',
    note: DONE + ': имя теперь есть в формализации (ProcessNinePoint.v), блок страницы совпадает с исходником' }); n++;
  const i = j.records.indexOf(rec);
  const add = [
    { line: rec.line + 1, theorem: 'one_process', file: F, claim: 'Definition one_process  : CauchySeq := cauchy_const 1.', page_price: '', verdict: 'ok',
      note: DONE + ': определение добавлено в ProcessNinePoint.v; блок страницы совпадает с исходником' },
    { line: rec.line + 5, theorem: 'nine_equiv_one', file: F, claim: 'ту же теорему для голых процессов (`nine_equiv_one`) разбирает Глава 4.3.', page_price: '', verdict: 'ok',
      note: 'nine_equiv_one : nine_raw ~~ const_process 1 (ProcessNinePoint.v:84), первая линия; Closed under the global context' },
  ].filter((a) => !j.records.some((r) => r.claim === a.claim));
  j.records.splice(i + 1, 0, ...add); n += add.length;
  save(x, 'part04-ch02.json', n);
}
{ // глава IV.3
  const x = load('part04-ch03.json'); const j = x.j; let n = 0;
  const claim = 'перенос на упакованную линию `CauchySeq` выполнен в том же файле (`nine_process_equiv_one`, через `nine_raw_is_Cauchy` и мост)';
  if (!j.records.some((r) => r.claim === claim)) {
    // вставить по порядку строк
    let i = j.records.findIndex((r) => r.line > 727); if (i < 0) i = j.records.length;
    j.records.splice(i, 0, { line: 727, theorem: 'nine_process_equiv_one', file: F, claim, page_price: '', verdict: 'ok',
      note: DONE + ': было «доступен через `nine_raw_is_Cauchy` и мост»; перенос выполнен — Theorem nine_process_equiv_one : cauchy_equiv nine_process one_process; Closed under the global context' });
    n++;
  }
  save(x, 'part04-ch03.json', n);
}
