// tom-status.cjs -- что глава тома называет в формализации и что об этом говорит компилятор.
//
//   node tom-status.cjs chapter "<глава>" [--json файл] [--brief]
//   node tom-status.cjs part <NN> [--json файл] [--brief]
//   node tom-status.cjs check            сторож: записи базы docs/database/tom-links.json против компилятора и страниц
//
// <глава> -- путь от «Том Математика» или сокращение «04/05» (часть/глава по номерам).
// Для каждой ссылки в обратных кавычках: есть ли имя (файл:строка), утверждение из .v, вывод Print Assumptions;
// для блоков кода -- совпадает ли процитированное объявление с исходником.
// Нужна собранная папка (tom-build.cjs). Репозиторий и страницы только читаются.
const fs = require('fs'); const path = require('path');
const L = require('./tom-lib.cjs');

function resolveChapters(arg, wholePart) {
  const parts = fs.readdirSync(L.TOM, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => e.name).sort();
  const norm = arg.replace(/\\/g, '/');
  const [pp, cc] = norm.split('/');
  const part = parts.find((p) => p === pp) || parts.find((p) => p.startsWith(pp.padStart(2, '0') + ' '));
  if (!part) throw new Error('часть не найдена: ' + arg);
  const chs = fs.readdirSync(L.TOM + '/' + part).filter((f) => f.endsWith('.md') && f !== 'index.md').sort();
  if (wholePart || !cc) return chs.map((c) => part + '/' + c);
  const ch = chs.find((c) => c === cc) || chs.find((c) => c.startsWith(cc.padStart(2, '0') + ' '));
  if (!ch) throw new Error('глава не найдена: ' + arg);
  return [part + '/' + ch];
}

const normStmt = (s) => s.replace(/\s+/g, ' ').replace(/\s*([(){}\[\],:;])\s*/g, '$1').trim();
// то же без имён модулей перед идентификаторами (ShrinkingIntervals_ERR.is_Cauchy -> is_Cauchy)
const normUnq = (s) => normStmt(s).replace(/\b[A-Z][A-Za-z0-9_]*\.(?=[A-Za-z_])/g, '');
const SKIP_PA = new Set(['Ltac', 'Notation', 'Abbreviation', 'Let', 'Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Scheme']);

function analyse(chapterRel, idx, nums) {
  const { lines, refs } = L.chapterRefs(L.TOM + '/' + chapterRel);
  // файлы, названные в главе: базовое имя -> строки
  const fileRefs = new Map();
  for (const r of refs) {
    const b = r.type === 'file' ? path.basename(r.raw) : r.fileHint;
    if (b) (fileRefs.get(b) || fileRefs.set(b, []).get(b)).push(r.line);
  }
  const files = [];
  for (const [b, ls] of fileRefs) {
    const hits = idx.byBase.get(b) || [];
    const raws = refs.filter((r) => r.type === 'file' && path.basename(r.raw) === b).map((r) => r.raw);
    let pick = hits; const withDir = raws.find((x) => x.includes('/'));
    if (withDir && hits.length > 1) { const h = hits.filter((p) => p.endsWith('/' + withDir)); if (h.length) pick = h; }
    files.push({ base: b, lines: ls, paths: pick, found: hits.length > 0,
      info: pick.map((p) => ({ path: p, num: nums.get(p) || null, qed: idx.files[p].qed, admitted: idx.files[p].admitted, axioms: idx.files[p].axioms, params: idx.files[p].params, sha: idx.files[p].sha })) });
  }
  const chapterPaths = new Set(files.flatMap((f) => f.paths));
  // имена
  const names = new Map(); // name -> {lines, hint}
  for (const r of refs) {
    if (r.type !== 'ident' && r.type !== 'qualified') continue;
    const e = names.get(r.name) || names.set(r.name, { name: r.name, lines: [], hints: new Set(), raws: new Set() }).get(r.name);
    e.lines.push(r.line); if (r.fileHint) e.hints.add(r.fileHint); e.raws.add(r.raw);
  }
  const rawCache = new Map();
  const rawOf = (p) => rawCache.get(p) || rawCache.set(p, fs.readFileSync(L.REPO + '/' + p, 'utf8')).get(p);
  const out = [];
  const resolved = L.resolveNames(idx, [...names.values()].map((e) => ({ name: e.name, hint: [...e.hints][0] || null })), chapterPaths);
  for (const e of names.values()) {
    const r = resolved.get(e.name);
    let seen = null;
    if (!r.decl) {
      const re = new RegExp('(^|[^A-Za-z0-9_\'])' + e.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '($|[^A-Za-z0-9_\'])');
      for (const p of chapterPaths) { const ls = rawOf(p).split(/\r?\n/); const i = ls.findIndex((x) => re.test(x)); if (i >= 0) { seen = p + ':' + (i + 1); break; } }
    }
    out.push({ name: e.name, lines: e.lines, raws: [...e.raws], candidates: r.candidates, otherFiles: r.others.slice(0, 8), chosen: r.decl ? [Object.assign({}, r.decl)] : [], how: r.how, seenInFile: seen,
      moduleOf: r.type === 'module' ? r.moduleFile : undefined, locate: r.locate || undefined, broken: refs.some((x) => x.name === e.name && x.broken) });
  }
  // Print Assumptions
  const items = [];
  for (const o of out) for (const c of o.chosen) if (!SKIP_PA.has(c.kind)) items.push({ file: c.file, name: c.name, mod: c.mod });
  const pa = L.printAssumptions(items);
  for (const o of out) for (const c of o.chosen) c.assumptions = SKIP_PA.has(c.kind) ? 'не применимо (' + c.kind + ')' : pa.get(c.file + '|' + (c.mod ? c.mod + '.' : '') + c.name);
  // блоки кода: объявления внутри ``` ... ``` сверяются с исходником
  const blocks = []; let inside = false; let start = 0; let buf = [];
  for (let i = 0; i < lines.length; i++) {
    if (/^\s*```/.test(lines[i])) {
      if (!inside) { inside = true; start = i + 1; buf = []; }
      else {
        inside = false; const text = L.stripComments(buf.join('\n')); const bl = text.split('\n');
        for (let j = 0; j < bl.length; j++) {
          const m = bl[j].match(/^\s*(?:(?:Local|Global|Program)\s+)*(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Structure|Class|Instance|Axiom|Parameter|Example|Notation)\s+([A-Za-z_][A-Za-z0-9_']*)/);
          if (!m) continue;
          let stmt = ''; for (let k = j; k < bl.length; k++) { stmt += ' ' + bl[k]; const q = stmt.search(/\.(\s|$)/); if (q >= 0) { stmt = stmt.slice(0, q + 1); break; } }
          const cands = idx.byName.get(m[2]) || [];
          let same = cands.filter((c) => normStmt(c.stmt) === normStmt(stmt)); let upTo = false;
          if (!same.length) { same = cands.filter((c) => normUnq(c.stmt) === normUnq(stmt)); upTo = same.length > 0; }
          const pref = cands.filter((c) => chapterPaths.has(c.file));
          blocks.push({ line: start + j + 1, name: m[2], kind: m[1], quoted: stmt.replace(/\s+/g, ' ').trim(),
            verdict: !cands.length ? 'нет такого объявления' : same.length ? (upTo ? 'совпадает с точностью до имён модулей' : 'совпадает') : 'отличается',
            matchFile: same.length ? (same.find((c) => chapterPaths.has(c.file)) || same[0]).file + ':' + (same.find((c) => chapterPaths.has(c.file)) || same[0]).line : null,
            source: !same.length && cands.length ? (pref[0] || cands[0]).file + ':' + (pref[0] || cands[0]).line + ' ' + (pref[0] || cands[0]).stmt : null });
        }
      }
      continue;
    }
    if (inside) buf.push(lines[i]);
  }
  return { chapter: chapterRel, files, names: out, blocks, counts: { refs: refs.length, files: files.length, names: out.length, other: refs.filter((r) => r.type === 'other').length } };
}

function print(res, brief) {
  console.log('\n=== ' + res.chapter);
  console.log(`ссылок в обратных кавычках: ${res.counts.refs}; файлов: ${res.counts.files}; имён: ${res.counts.names}; прочих фрагментов кода: ${res.counts.other}`);
  console.log('\nФАЙЛЫ');
  for (const f of res.files.sort((a, b) => a.base.localeCompare(b.base))) {
    if (!f.found) { console.log(`  НЕ НАЙДЕН  ${f.base}  [стр. ${f.lines.join(', ')}]`); continue; }
    for (const i of f.info) console.log(`  ${i.path}  #${i.num || '—'}  Qed ${i.qed}, Admitted ${i.admitted}, Axiom ${i.axioms}, Parameter ${i.params}` + (f.info.length > 1 ? '  (имя неоднозначно)' : '') + `  [стр. ${f.lines.slice(0, 12).join(', ')}${f.lines.length > 12 ? ', …' : ''}]`);
  }
  console.log('\nИМЕНА');
  const miss = res.names.filter((n) => !n.chosen.length);
  for (const n of res.names.filter((x) => x.chosen.length).sort((a, b) => a.lines[0] - b.lines[0])) {
    for (const c of n.chosen) {
      console.log(`  стр. ${n.lines.slice(0, 8).join(', ')}${n.lines.length > 8 ? ', …' : ''}  ${n.name}  — ${c.kind}, ${c.file}:${c.line}` + (n.chosen.length > 1 || n.candidates > 1 ? `  (объявлений всего ${n.candidates}; ${n.how}; ещё: ${n.otherFiles.join(', ')})` : ''));
      if (!brief) console.log('      утверждение: ' + c.stmt.slice(0, 300));
      console.log('      допущения: ' + c.assumptions);
    }
  }
  console.log('\nИМЕНА БЕЗ ОБЪЯВЛЕНИЯ В ФОРМАЛИЗАЦИИ: ' + miss.length);
  for (const n of miss.sort((a, b) => a.lines[0] - b.lines[0])) console.log(`  стр. ${n.lines.slice(0, 8).join(', ')}  ${n.name}` + (n.moduleOf ? `  — имя модуля: ${n.moduleOf}` : `  — Locate: ${(n.locate || '').slice(0, 150)}` + (n.seenInFile ? `  (слово встречается: ${n.seenInFile})` : '')));
  console.log('\nБЛОКИ КОДА: объявлений ' + res.blocks.length + ', из них отличаются от исходника ' + res.blocks.filter((b) => !b.verdict.startsWith('совпадает')).length);
  for (const b of res.blocks) {
    if (b.verdict.startsWith('совпадает')) { if (!brief) console.log(`  стр. ${b.line}  ${b.name}  ${b.verdict}  (${b.matchFile})`); continue; }
    console.log(`  стр. ${b.line}  ${b.name}  ${b.verdict.toUpperCase()}`);
    console.log('      в главе:   ' + b.quoted.slice(0, 400));
    if (b.source) console.log('      в файле:   ' + b.source.slice(0, 400));
  }
}

function check() {
  const dbFile = L.REPO + '/docs/database/tom-links.json';
  const db = JSON.parse(fs.readFileSync(dbFile, 'utf8'));
  const idx = L.buildIndex(); const problems = []; const items = [];
  for (const r of db) {
    if (!r.theorem || !r.file || !r.file_line || r.kind === 'внешнее' || r.assumptions === 'not-checked' || !r.assumptions || /^не применимо/.test(r.assumptions)) continue;
    const c = (idx.byName.get(r.theorem) || []).find((x) => x.file === r.file);
    if (!c) { problems.push(`${r.chapter}:${r.line}  ${r.theorem}: объявление исчезло из ${r.file}`); continue; }
    items.push({ file: c.file, name: c.name, mod: c.mod, rec: r });
  }
  const pa = L.printAssumptions(items);
  for (const it of items) {
    const now = pa.get(it.file + '|' + (it.mod ? it.mod + '.' : '') + it.name); const r = it.rec;
    if (now && now.startsWith('не собрано')) { problems.push(`${r.chapter}:${r.line}  ${r.theorem}: ${now}`); continue; }
    if (now !== r.assumptions) problems.push(`${r.chapter}:${r.line}  ${r.theorem}: допущения изменились\n      в базе:  ${r.assumptions}\n      сейчас:  ${now}`);
  }
  let moved = 0, stale = 0;
  for (const r of db) {
    if (r.file && r.file_sha && idx.files[r.file] && idx.files[r.file].sha !== r.file_sha) stale++;
    if (!r.claim || !r.chapter) continue;
    const p = (r.root === 'library' ? path.dirname(path.dirname(path.dirname(L.TOM))) : L.TOM) + '/' + r.chapter; if (!fs.existsSync(p)) { problems.push(`${r.chapter}: страница не найдена`); continue; }
    const text = fs.readFileSync(p, 'utf8').replace(/\r\n/g, '\n').replace(/\s+/g, ' ');
    if (!text.includes(r.claim.replace(/\s+/g, ' ').trim())) moved++;
  }
  console.log(`записей в базе: ${db.length}; проверено по компилятору: ${items.length}`);
  console.log(`файл .v изменился после проверки (записи стоит пересмотреть): ${stale}`);
  console.log(`цитата больше не находится на странице (страница правилась): ${moved}`);
  console.log(`расхождений с компилятором: ${problems.length}`);
  for (const p of problems) console.log('  ' + p);
  const open = db.filter((r) => r.verdict && r.verdict !== 'ok');
  console.log(`записей с вердиктом, отличным от ok: ${open.length}`);
  process.exit(problems.length ? 1 : 0);
}

const cmd = process.argv[2]; const args = process.argv.slice(3);
if (cmd === 'check') check();
else if (cmd === 'chapter' || cmd === 'part') {
  const jsonAt = args.indexOf('--json'); const brief = args.includes('--brief');
  const chapters = resolveChapters(args[0], cmd === 'part');
  const idx = L.buildIndex(); const nums = L.fileNums(); const all = [];
  for (const ch of chapters) { const res = analyse(ch, idx, nums); all.push(res); print(res, brief); }
  if (jsonAt >= 0) fs.writeFileSync(args[jsonAt + 1], JSON.stringify(all, null, 1));
} else console.log('usage: node tom-status.cjs chapter "<часть/глава>" | part <NN> | check   [--json файл] [--brief]');
