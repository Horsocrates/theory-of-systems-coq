// tom-links.cjs -- ведение базы связей «том <-> формализация» (docs/database/tom-links.json).
//
//   node tom-links.cjs merge <ведомость.json> [--dry]   внести ведомость проверки главы в базу
//   node tom-links.cjs stats                            счёт записей по вердиктам
//
// Ведомость (пишется при проверке главы, лежит в ../ведомости/):
//   { "batch": "audit-part-04", "chapter": "<путь главы от «Том Математика»>", "checked": "2026-11-12",
//     "auto": true,
//     "records": [ { "line": 544, "theorem": "имя" | null, "file": "src/…v" (необязательно),
//                    "claim": "цитата главы дословно", "page_price": "что глава говорит о цене",
//                    "verdict": "ok|mismatch-price|mismatch-statement|missing-name|wrong-number|not-checked",
//                    "note": "одна фраза" } ] }
// Механические поля (file, file_line, file_num, statement, assumptions, file_sha, lines) инструмент заполняет сам
// по индексу объявлений и Print Assumptions. При "auto": true все остальные ссылки главы в обратных кавычках
// получают записи автоматически: имя не найдено -> missing-name; теорема без ручной записи -> not-checked;
// определение, тип, файл -> ok с пометкой «упоминание; проверено существование».
// Повторный merge той же ведомости заменяет записи с тем же (batch, chapter): ведомость -- полный ввод по главе.
const fs = require('fs'); const path = require('path');
const L = require('./tom-lib.cjs');
const DB = L.REPO + '/docs/database/tom-links.json';
const VERDICTS = new Set(['ok', 'mismatch-price', 'mismatch-statement', 'missing-name', 'wrong-number', 'not-checked']);
const SKIP_PA = new Set(['Ltac', 'Notation', 'Abbreviation', 'Let', 'Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Scheme']);

function loadDb() { try { return JSON.parse(fs.readFileSync(DB, 'utf8')); } catch (e) { return []; } }
function saveDb(db) { fs.writeFileSync(DB, JSON.stringify(db, null, 1) + '\n'); }

function pickDecl(idx, name, fileWanted, chapterPaths) {
  const cands = idx.byName.get(name) || [];
  if (!cands.length) return null;
  if (fileWanted) return cands.find((c) => c.file === fileWanted) || cands.find((c) => path.basename(c.file) === path.basename(fileWanted)) || null;
  return cands.find((c) => chapterPaths.has(c.file)) || cands[0];
}

function merge(reviewFile, dry) {
  const rv = JSON.parse(fs.readFileSync(reviewFile, 'utf8'));
  const idx = L.buildIndex(); const nums = L.fileNums();
  // страница: в томе или (для сводных страниц) от «Библиотека»
  const pagePath = rv.root === 'library' ? path.dirname(path.dirname(path.dirname(L.TOM))) + '/' + rv.chapter : L.TOM + '/' + rv.chapter;
  if (!fs.existsSync(pagePath)) throw new Error('страница не найдена: ' + pagePath);
  const { lines, refs } = L.chapterRefs(pagePath);
  const pageText = lines.join('\n').replace(/\s+/g, ' ');
  const chapterPaths = new Set();
  for (const r of refs) { const b = r.type === 'file' ? path.basename(r.raw) : r.fileHint; if (b) for (const p of idx.byBase.get(b) || []) chapterPaths.add(p); }
  const out = []; const problems = []; const covered = new Set();
  const raw = lines.join('\n');
  const lineOf = (claim) => { const m = raw.match(new RegExp(claim.trim().replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\s+/g, '\\s+'))); return m ? raw.slice(0, m.index).split('\n').length : null; };
  for (const r of rv.records) {
    if (!r.line && r.claim) r.line = lineOf(r.claim) || 0; // строку можно не указывать: берётся первое вхождение цитаты
    if (!VERDICTS.has(r.verdict)) problems.push(`строка ${r.line}: неизвестный вердикт ${r.verdict}`);
    if (r.claim && !pageText.includes(r.claim.replace(/\s+/g, ' ').trim())) problems.push(`строка ${r.line}: цитата не найдена на странице: «${r.claim.slice(0, 80)}…»`);
    const rec = { batch: rv.batch, chapter: rv.chapter, line: r.line, claim: r.claim || '', theorem: r.theorem || null, file: r.file || null, file_line: null, file_num: null, kind: null, statement: null, assumptions: 'not-checked', page_price: r.page_price || '', verdict: r.verdict, checked: r.checked || rv.checked, note: r.note || '' };
    if (rv.root) rec.root = rv.root;
    if (r.theorem) {
      covered.add(r.theorem);
      const d = pickDecl(idx, r.theorem, r.file, chapterPaths);
      if (d) { rec.file = d.file; rec.file_line = d.line; rec.kind = d.kind; rec.statement = d.stmt; rec._decl = d; }
      else if (r.external) rec.kind = 'внешнее';
      else if (r.verdict !== 'missing-name' && !r.external) problems.push(`строка ${r.line}: объявление ${r.theorem} не найдено` + (r.file ? ' в ' + r.file : ''));
      rec.lines = refs.filter((x) => x.name === r.theorem && (x.type === 'ident' || x.type === 'qualified')).map((x) => x.line);
    }
    if (rec.file && idx.files[rec.file]) { rec.file_num = nums.get(rec.file) || null; rec.file_sha = idx.files[rec.file].sha; }
    else if (rec.file && r.verdict !== 'missing-name') problems.push(`строка ${r.line}: файл не найден: ${rec.file}`);
    if (r.assumptions) rec.assumptions = r.assumptions; // дословно из ручной проверки (например, для имён стандартной библиотеки)
    out.push(rec);
  }
  if (rv.auto) {
    const seen = new Map();
    for (const x of refs) {
      if (x.type === 'ident' || x.type === 'qualified') {
        if (covered.has(x.name)) continue;
        const e = seen.get('n:' + x.name) || seen.set('n:' + x.name, { name: x.name, lines: [], hint: x.fileHint }).get('n:' + x.name);
        e.lines.push(x.line);
      } else if (x.type === 'file') {
        const b = path.basename(x.raw); const e = seen.get('f:' + b) || seen.set('f:' + b, { base: b, raw: x.raw, lines: [] }).get('f:' + b);
        e.lines.push(x.line);
      }
    }
    const fileCovered = new Set(out.filter((r) => !r.theorem && r.file).map((r) => path.basename(r.file)));
    const nameEntries = [...seen.values()].filter((e) => !e.base);
    const resolved = L.resolveNames(idx, nameEntries.map((e) => ({ name: e.name, hint: e.hint })), chapterPaths);
    for (const e of seen.values()) {
      const line = e.lines[0]; const claim = lines[line - 1].trim().slice(0, 260);
      const rec = { batch: rv.batch, chapter: rv.chapter, line, claim, theorem: null, file: null, file_line: null, file_num: null, kind: null, statement: null, assumptions: 'not-checked', page_price: '', verdict: 'ok', checked: rv.checked, note: '', lines: e.lines, auto: true };
      if (e.base) {
        if (fileCovered.has(e.base)) continue;
        const hits = idx.byBase.get(e.base) || [];
        const withDir = e.raw.includes('/') ? hits.filter((p) => p.endsWith('/' + e.raw)) : [];
        const p = (withDir[0] || hits[0]);
        if (!p) { rec.file = e.raw; rec.verdict = 'missing-name'; rec.note = 'файл с таким именем в src не найден'; }
        else { rec.file = p; rec.file_num = nums.get(p) || null; rec.file_sha = idx.files[p].sha; rec.kind = 'файл'; rec.note = 'упоминание файла; проверено существование' + (hits.length > 1 ? `; имя неоднозначно (${hits.length} файлов)` : ''); }
      } else {
        rec.theorem = e.name; const r = resolved.get(e.name); const d = r.decl;
        if (d) {
          rec.file = d.file; rec.file_line = d.line; rec.kind = d.kind; rec.statement = d.stmt; rec._decl = d; rec.file_num = nums.get(d.file) || null; rec.file_sha = idx.files[d.file].sha;
          if (L.PROOFY.has(d.kind)) { rec.verdict = 'not-checked'; rec.note = 'теорема без ручной сверки формулировки'; }
          else rec.note = 'упоминание имени (' + d.kind + '); проверено существование' + (r.candidates > 1 ? `; объявлений с таким именем ${r.candidates} (${r.how})` : '');
        } else if (r.type === 'module') { rec.file = r.moduleFile; rec.kind = 'модуль'; rec.note = 'имя модуля; файл существует'; rec.file_num = nums.get(rec.file) || null; }
        else if (r.type === 'external') { rec.kind = 'внешнее'; rec.statement = (r.locate || '').slice(0, 200); rec.note = 'имя не объявлено на верхнем уровне формализации; найдено командой Locate (конструктор, поле записи или стандартная библиотека)'; }
        else if (r.type === 'keyword') { rec.kind = 'ключевое слово'; rec.note = 'ключевое слово Rocq, не имя'; }
        else { rec.verdict = 'missing-name'; rec.note = 'имени нет ни в названных файлах, ни в стандартной библиотеке (Locate: ' + (r.locate || 'нет ответа') + ')'; }
      }
      out.push(rec);
    }
  }
  // Print Assumptions для всех записей с объявлением
  const items = out.filter((r) => r._decl && !SKIP_PA.has(r._decl.kind)).map((r) => ({ file: r._decl.file, name: r._decl.name, mod: r._decl.mod }));
  const pa = L.printAssumptions(items);
  for (const r of out) {
    if (r._decl) { if (r.assumptions === 'not-checked') r.assumptions = SKIP_PA.has(r._decl.kind) ? 'не применимо (' + r._decl.kind + ')' : (pa.get(r._decl.file + '|' + (r._decl.mod ? r._decl.mod + '.' : '') + r._decl.name) || 'not-checked'); delete r._decl; }
  }
  out.sort((a, b) => a.line - b.line || String(a.theorem).localeCompare(String(b.theorem)));
  for (const p of problems) console.log('ЗАМЕЧАНИЕ: ' + p);
  const by = {}; for (const r of out) by[r.verdict] = (by[r.verdict] || 0) + 1;
  console.log(`${rv.chapter}: записей ${out.length} (ручных ${rv.records.length}); ` + Object.entries(by).map(([k, v]) => k + ' ' + v).join(', '));
  const nc = out.filter((r) => r.verdict === 'not-checked'); if (nc.length) console.log('  без сверки: ' + nc.map((r) => r.theorem + '@' + r.line).join(', '));
  if (dry) return;
  const db = loadDb().filter((r) => !(r.batch === rv.batch && r.chapter === rv.chapter));
  saveDb(db.concat(out));
}

function stats() {
  const db = loadDb(); const by = {}; const byCh = {};
  for (const r of db) { by[r.verdict] = (by[r.verdict] || 0) + 1; (byCh[r.chapter] ||= {})[r.verdict] = ((byCh[r.chapter] || {})[r.verdict] || 0) + 1; }
  console.log('записей: ' + db.length + ' | ' + Object.entries(by).map(([k, v]) => k + ' ' + v).join(', '));
  for (const [c, v] of Object.entries(byCh)) console.log('  ' + c + ': ' + Object.entries(v).map(([k, n]) => k + ' ' + n).join(', '));
}

// После правки страницы номера строк съезжают: relocate пересчитывает поле line каждой ручной записи ведомости
// по её цитате (берётся вхождение, ближайшее к прежнему номеру) и переписывает ведомость.
function relocate(reviewFile) {
  const rv = JSON.parse(fs.readFileSync(reviewFile, 'utf8'));
  const pagePath = rv.root === 'library' ? path.dirname(path.dirname(path.dirname(L.TOM))) + '/' + rv.chapter : L.TOM + '/' + rv.chapter;
  const raw = fs.readFileSync(pagePath, 'utf8').replace(/\r\n/g, '\n'); let moved = 0; const lost = [];
  for (const r of rv.records) {
    if (!r.claim) continue;
    const re = new RegExp(r.claim.trim().replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\s+/g, '\\s+'), 'g');
    const at = [...raw.matchAll(re)].map((m) => raw.slice(0, m.index).split('\n').length);
    if (!at.length) { lost.push(r.line + ': «' + r.claim.replace(/\s+/g, ' ').slice(0, 70) + '…»'); continue; }
    const best = at.reduce((a, b) => (Math.abs(b - r.line) < Math.abs(a - r.line) ? b : a));
    if (best !== r.line) { r.line = best; moved++; }
  }
  fs.writeFileSync(reviewFile, JSON.stringify(rv, null, 1) + '\n');
  console.log(`${rv.chapter}: строк пересчитано ${moved}; цитат не найдено ${lost.length}`);
  for (const x of lost) console.log('  не найдена: ' + x);
}

const cmd = process.argv[2];
if (cmd === 'relocate') relocate(process.argv[3]);
else if (cmd === 'merge') merge(process.argv[3], process.argv.includes('--dry'));
else if (cmd === 'stats') stats();
else console.log('usage: node tom-links.cjs merge <ведомость.json> [--dry] | stats');
