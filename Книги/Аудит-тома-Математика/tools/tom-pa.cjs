// tom-pa.cjs -- утверждение и Print Assumptions для отдельных имён.
//
//   node tom-pa.cjs <имя> [<имя> …] [--in <файл или его базовое имя>]
//
// Без --in берутся все объявления с таким именем. Нужна собранная папка (tom-build.cjs).
const path = require('path');
const L = require('./tom-lib.cjs');
const args = process.argv.slice(2); const at = args.indexOf('--in');
const where = at >= 0 ? args[at + 1].replace(/\\/g, '/') : null;
const names = args.filter((a, i) => a !== '--in' && (at < 0 || i !== at + 1));
const idx = L.buildIndex(); const SKIP = new Set(['Ltac', 'Notation', 'Abbreviation', 'Let', 'Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Scheme']);
const picked = [];
for (const n of names) {
  let c = idx.byName.get(n) || [];
  if (where) c = c.filter((d) => d.file === where || d.file.endsWith('/' + where) || path.basename(d.file) === path.basename(where));
  if (!c.length) console.log(`${n}: объявление не найдено` + (where ? ' в ' + where : ''));
  picked.push(...c);
}
const pa = L.printAssumptions(picked.filter((d) => !SKIP.has(d.kind)).map((d) => ({ file: d.file, name: d.name, mod: d.mod })));
for (const d of picked) {
  console.log(`\n${d.name} — ${d.kind}, ${d.file}:${d.line}`);
  console.log('  утверждение: ' + d.stmt);
  console.log('  допущения:   ' + (SKIP.has(d.kind) ? 'не применимо' : pa.get(d.file + '|' + (d.mod ? d.mod + '.' : '') + d.name)));
}
