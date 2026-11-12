// tom-links-generate.cjs -- виды базы связей «том <-> формализация» на Markdown.
// Usage:  node docs/database/tom-links-generate.cjs
// Читает tom-links.json (источник истины), пишет tom-links-by-chapter.md и tom-links-by-file.md.
// Виды руками не правятся: правится JSON (через Книги/Аудит-тома-Математика/tools/tom-links.cjs merge).
const fs = require('fs'); const path = require('path');
const dir = __dirname;
const db = JSON.parse(fs.readFileSync(path.join(dir, 'tom-links.json'), 'utf8'));

const cell = (s) => (s === null || s === undefined ? '' : String(s)).replace(/\|/g, '\\|').replace(/[\r\n]+/g, ' ');
const cut = (s, n) => { s = cell(s); return s.length > n ? s.slice(0, n - 1) + '…' : s; };
const ROMAN = ['0', 'I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII', 'IX', 'X', 'XI', 'XII', 'XIII', 'XIV', 'XV', 'XVI', 'XVII', 'XVIII', 'XIX', 'XX'];
function label(r) {
  if (r.root === 'library') return r.chapter.replace(/\.md$/, '');
  const m = r.chapter.match(/^(\d+) [^/]*\/(\d+) (.*)\.md$/);
  return m ? `${ROMAN[+m[1]] || m[1]}.${+m[2]} ${m[3]}` : r.chapter.replace(/\.md$/, '');
}
const VERDICT = { 'ok': 'верно', 'mismatch-price': 'расходится цена', 'mismatch-statement': 'расходится формулировка', 'missing-name': 'имени нет', 'wrong-number': 'неверное число', 'not-checked': 'не проверено' };
const counts = (list) => { const by = {}; for (const r of list) by[r.verdict] = (by[r.verdict] || 0) + 1; return Object.keys(VERDICT).filter((k) => by[k]).map((k) => `${VERDICT[k]} — ${by[k]}`).join('; '); };
const where = (r) => r.file ? '`' + r.file.replace(/^src\//, '') + (r.file_line ? ':' + r.file_line : '') + '`' : '';
const today = db.reduce((a, r) => (r.checked && r.checked > a ? r.checked : a), '');

// ---- по главам -----------------------------------------------------------
const chapters = []; const seen = new Map();
for (const r of db) { const k = (r.root || '') + '|' + r.chapter; if (!seen.has(k)) { seen.set(k, []); chapters.push(k); } seen.get(k).push(r); }
chapters.sort((a, b) => a.localeCompare(b, 'ru'));
const md = [];
md.push('# База связей «том ↔ формализация» — по главам');
md.push('');
md.push('_Сгенерировано из `tom-links.json` скриптом `tom-links-generate.cjs`; руками не править — правится JSON._');
md.push('');
md.push(`**Записей: ${db.length}; страниц: ${chapters.length}; последняя проверка: ${today}.** ${counts(db)}.`);
md.push('');
md.push('Одна запись — одна связь «место в томе ↔ теорема ↔ файл». Вердикты: верно · расходится цена · расходится формулировка · имени нет · неверное число · не проверено. Допущения — вывод `Print Assumptions` дословно.');
md.push('');
const bad = db.filter((r) => r.verdict !== 'ok');
md.push(`## Расхождения и непроверенное (${bad.length})`);
md.push('');
if (bad.length) {
  md.push('| глава | строка | теорема или файл | вердикт | пометка |');
  md.push('|---|---|---|---|---|');
  for (const r of bad.slice().sort((a, b) => a.chapter.localeCompare(b.chapter, 'ru') || a.line - b.line)) md.push(`| ${cell(label(r))} | ${r.line} | ${r.theorem ? '`' + cell(r.theorem) + '`' : where(r)} | ${VERDICT[r.verdict] || r.verdict} | ${cell(r.note)} |`);
  md.push('');
} else { md.push('Нет.'); md.push(''); }
for (const k of chapters) {
  const list = seen.get(k).slice().sort((a, b) => a.line - b.line);
  md.push('---');
  md.push('');
  md.push(`## ${label(list[0])}`);
  md.push('');
  md.push(`\`${list[0].chapter}\` — записей ${list.length}: ${counts(list)}.`);
  md.push('');
  const hand = list.filter((r) => !r.auto); const auto = list.filter((r) => r.auto);
  if (hand.length) {
    md.push('| строка | что сказано в главе | теорема | файл | утверждение в Rocq | допущения | цена по главе | вердикт | пометка |');
    md.push('|---|---|---|---|---|---|---|---|---|');
    for (const r of hand) md.push(`| ${r.line} | ${cut(r.claim, 260)} | ${r.theorem ? '`' + cell(r.theorem) + '`' : ''} | ${where(r)} | ${r.statement ? '`' + cut(r.statement, 220).replace(/`/g, "'") + '`' : ''} | ${cell(r.assumptions)} | ${cell(r.page_price)} | ${VERDICT[r.verdict] || r.verdict} | ${cell(r.note)} |`);
    md.push('');
  }
  if (auto.length) {
    md.push(`**Упоминания имён и файлов без отдельного утверждения (${auto.length}):**`);
    md.push('');
    md.push('| строки | имя | вид | файл | допущения | вердикт | пометка |');
    md.push('|---|---|---|---|---|---|---|');
    for (const r of auto) md.push(`| ${(r.lines || [r.line]).slice(0, 10).join(', ')}${(r.lines || []).length > 10 ? ', …' : ''} | ${r.theorem ? '`' + cell(r.theorem) + '`' : ''} | ${cell(r.kind)} | ${where(r)} | ${cell(r.assumptions === 'not-checked' ? '' : r.assumptions)} | ${VERDICT[r.verdict] || r.verdict} | ${cell(r.note)} |`);
    md.push('');
  }
}
fs.writeFileSync(path.join(dir, 'tom-links-by-chapter.md'), md.join('\n') + '\n');
console.log(`wrote tom-links-by-chapter.md (${db.length} records, ${chapters.length} pages)`);

// ---- по файлам -----------------------------------------------------------
const files = new Map();
for (const r of db) { if (!r.file) continue; (files.get(r.file) || files.set(r.file, []).get(r.file)).push(r); }
const fl = [...files.keys()].sort((a, b) => a.localeCompare(b));
const mf = [];
mf.push('# База связей «том ↔ формализация» — по файлам');
mf.push('');
mf.push('_Сгенерировано из `tom-links.json` скриптом `tom-links-generate.cjs`; руками не править — правится JSON._');
mf.push('');
mf.push(`**Файлов формализации, названных в проверенных главах: ${fl.length}; записей с файлом: ${db.filter((r) => r.file).length}.**`);
mf.push('');
mf.push('| # | файл | записей | глав | расхождений |');
mf.push('|---|---|---|---|---|');
for (const f of fl) { const list = files.get(f); mf.push(`| ${list[0].file_num || '—'} | \`${f}\` | ${list.length} | ${new Set(list.map((r) => r.chapter)).size} | ${list.filter((r) => r.verdict !== 'ok').length} |`); }
mf.push('');
for (const f of fl) {
  const list = files.get(f).slice().sort((a, b) => (a.file_line || 0) - (b.file_line || 0) || a.chapter.localeCompare(b.chapter, 'ru') || a.line - b.line);
  mf.push('---');
  mf.push('');
  mf.push(`## #${list[0].file_num || '—'} — \`${f}\``);
  mf.push('');
  mf.push('| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |');
  mf.push('|---|---|---|---|---|---|');
  for (const r of list) mf.push(`| ${r.theorem ? '`' + cell(r.theorem) + '`' + (r.file_line ? ' (' + r.file_line + ')' : '') : '_файл целиком_'} | ${cell(r.kind)} | ${cell(r.assumptions === 'not-checked' ? '' : r.assumptions)} | ${cell(label(r))}, стр. ${(r.lines && r.lines.length ? r.lines : [r.line]).slice(0, 8).join(', ')} | ${VERDICT[r.verdict] || r.verdict} | ${cell(r.note)} |`);
  mf.push('');
}
fs.writeFileSync(path.join(dir, 'tom-links-by-file.md'), mf.join('\n') + '\n');
console.log(`wrote tom-links-by-file.md (${fl.length} files)`);
