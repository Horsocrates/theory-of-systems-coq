// 2026-11-13 (Часть I, шаг 8): объявление classic в проекте одно — Classical_Prop.classic стандартной библиотеки
// (местные `Axiom classic` в foundation/Distinction.v и settheory/BorelDeterminacy.v сняты по слову автора).
// Во всех ведомостях записи с теоремой `classic`, привязанные к одному из двух файлов, переводятся на внешнее
// объявление. Скрипт повторяем. Запуск: node patch-classic-one-declaration.cjs  (затем merge всех ведомостей)
const fs = require('fs');
const path = require('path');
const TAG = 'С 13.11.2026 объявление одно — `Classical_Prop.classic` стандартной библиотеки';
function walk(d) { let out = []; for (const e of fs.readdirSync(d, { withFileTypes: true })) { const p = path.join(d, e.name); if (e.isDirectory()) { if (e.name !== 'половины') out = out.concat(walk(p)); } else if (e.name.endsWith('.json')) out.push(p); } return out; }
let files = 0, recs = 0;
for (const p of walk(__dirname)) {
  let j; try { j = JSON.parse(fs.readFileSync(p, 'utf8')); } catch (e) { continue; }
  if (!j || !Array.isArray(j.records)) continue;
  let n = 0;
  for (const r of j.records) {
    if (r.theorem !== 'classic') continue;
    const f = r.file || '';
    if (!(f.endsWith('Distinction.v') || f.endsWith('BorelDeterminacy.v') || (!f && !r.external))) continue;
    const was = f ? path.basename(f) : '';
    delete r.file; r.external = true;
    if (!(r.note || '').includes(TAG)) r.note = ((r.note || '') + ' ' + TAG + (was ? ' (местное объявление в ' + was + ' снято; файл подключает библиотечное).' : '.')).trim();
    n++;
  }
  if (n) { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); files++; recs += n; console.log(path.relative(__dirname, p) + ': записей ' + n); }
}
console.log('ведомостей изменено ' + files + ', записей ' + recs);
