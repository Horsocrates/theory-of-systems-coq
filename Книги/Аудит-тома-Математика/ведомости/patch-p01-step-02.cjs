// Часть I, шаг 2, формализация (2026-11-13): в src/foundation/LawsFromDistinction.v теорема laws_consistent
// получила прямой свидетель (стороны True / False) и больше не опирается на classic; шапка файла говорит, что в нём
// дано и что выведено. Страница I.3 этим скриптом не затрагивается (её правки — patch-p01-step-02-pages.cjs).
// Запуск: node patch-p01-step-02.cjs   (затем merge по ведомостям part01-ch01…ch06: файл .v изменился)
const fs = require('fs');
const path = require('path');
const p = path.join(__dirname, 'part01-ch03.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
const TAG = 'С 13.11 (Часть I, шаг 2)';
let n = 0;
for (const r of j.records) {
  if (r.theorem !== 'laws_consistent' || (r.note || '').includes(TAG)) continue;
  r.note = (r.note || '').replace(/\s*Свидетель — `distinction_of True`\./, '')
    .replace(/, свидетель `distinction_of True`\. Print Assumptions: `Distinction\.classic`[^.]*\./, '.') +
    ' ' + TAG + ' свидетель предъявлен прямо — `mkDistinction True False …`; Print Assumptions: Closed under the global context (прежде свидетелем было `distinction_of True`, цена — `Distinction.classic`).';
  n++;
}
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part01-ch03.json: записей о laws_consistent обновлено ' + n);
