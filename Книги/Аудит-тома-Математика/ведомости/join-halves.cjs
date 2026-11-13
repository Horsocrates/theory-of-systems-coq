// Слияние двух половин ведомости одной главы в одну ведомость.
// Нужно потому, что `tom-links.cjs merge` заменяет записи того же batch и той же главы:
// половины, внесённые по очереди, затёрли бы друг друга.
// Запуск (из папки аудита): node ведомости/join-halves.cjs part01-ch04   [--keep]
//   читает ведомости/part01-ch04a.json и part01-ch04b.json, пишет ведомости/part01-ch04.json;
//   половины переносит в ведомости/половины/ (чтобы их нельзя было внести по ошибке); --keep — не переносить.
const fs = require('fs');
const path = require('path');
const dir = __dirname;
const base = process.argv[2];
const keep = process.argv.includes('--keep');
if (!base) { console.error('нужно имя ведомости без буквы половины, например part01-ch04'); process.exit(2); }
const fa = path.join(dir, base + 'a.json');
const fb = path.join(dir, base + 'b.json');
const a = JSON.parse(fs.readFileSync(fa, 'utf8'));
const b = JSON.parse(fs.readFileSync(fb, 'utf8'));
for (const k of ['batch', 'chapter']) {
  if (a[k] !== b[k]) throw new Error('половины расходятся в поле ' + k + ': ' + a[k] + ' / ' + b[k]);
}
const records = a.records.concat(b.records).sort((x, y) => (x.line || 0) - (y.line || 0));
// одинаковые записи (та же строка, то же имя, та же цитата) из двух половин — оставить одну
const seen = new Set();
const out = [];
let dup = 0;
for (const r of records) {
  const key = [r.line, r.theorem || '', r.claim].join('\u0001');
  if (seen.has(key)) { dup++; continue; }
  seen.add(key);
  out.push(r);
}
const sheet = Object.assign({}, a, { records: out });
fs.writeFileSync(path.join(dir, base + '.json'), JSON.stringify(sheet, null, 2) + '\n');
const cnt = {};
for (const r of out) cnt[r.verdict] = (cnt[r.verdict] || 0) + 1;
console.log(base + '.json: записей ' + out.length + ' (' + a.records.length + ' + ' + b.records.length +
  ', повторов снято ' + dup + ') — ' + JSON.stringify(cnt));
if (!keep) {
  const hd = path.join(dir, 'половины');
  if (!fs.existsSync(hd)) fs.mkdirSync(hd);
  fs.renameSync(fa, path.join(hd, base + 'a.json'));
  fs.renameSync(fb, path.join(hd, base + 'b.json'));
  console.log('половины перенесены в ведомости/половины/');
}
