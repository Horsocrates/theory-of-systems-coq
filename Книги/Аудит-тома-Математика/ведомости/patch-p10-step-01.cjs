// Часть X, шаг 1, формализация (2026-11-12): SchroederBernstein_ERR.v перестроен на две посылки
// (исключённое третье и извлечение единственного свидетеля), CardinalityWithoutChoice.v дополнен.
// Здесь — только записи, чьи пояснения устарели от самой правки .v; вердикты расхождений меняет
// patch-p10-step-01-pages.cjs после внесения страниц.
// Запуск: node patch-p10-step-01.cjs   (затем tom-links.cjs relocate + merge по ведомостям, называющим эти файлы)
const fs = require('fs');
const path = require('path');
const p = path.join(__dirname, 'part10-ch03.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
for (const r of j.records) {
  if (r.theorem === 'h_injective' && r.file === 'src/SchroederBernstein_ERR.v') {
    r.note = 'h_injective, h_surjective (SchroederBernstein_ERR.v). После шага 1 Части X обе леммы доказаны внутри раздела с двумя посылками (исключённое третье EM и извлечение единственного свидетеля DD) и допущений не имеют: Closed under the global context.';
    n++;
  }
  if (r.theorem === 'classic' && r.external && !r.file) { r.file = 'src/ToS_Axioms.v'; n++; }
}
if (n !== 2) throw new Error('ожидалось две записи, изменено ' + n);
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part10-ch03.json: изменено ' + n);
