// tom-lib.cjs -- общая часть инструментов аудита: индекс объявлений формализации и Print Assumptions.
const fs = require('fs'); const path = require('path'); const cp = require('child_process'); const crypto = require('crypto');

const REPO = 'C:/Users/abary/OneDrive/Desktop/theory-of-systems-coq';
const BUILD = process.env.TOS_BUILD || 'C:/Users/abary/tos-audit-build';
const TOM = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/Направления/Математика/Том Математика';
const ROCQ = 'C:/Programs/Rocq-Platform~9.0~2025.08';
const ENV = Object.assign({}, process.env, { ROCQLIB: ROCQ.replace(/\//g, '\\') + '\\lib\\coq' });
const QFLAGS = ['-Q', 'src', 'ToS', '-Q', 'Architecture_of_Reasoning', 'ToS_Arch'];

const sha1 = (buf) => crypto.createHash('sha1').update(buf).digest('hex');
function writeAtomic(file, text) {
  // запись через переименование; в Windows переименование поверх файла, открытого другим запуском, даёт EPERM -- повторить
  const tmp = file + '.' + process.pid + '.tmp'; fs.writeFileSync(tmp, text);
  for (let i = 0; i < 8; i++) {
    try { fs.renameSync(tmp, file); return; } catch (e) { if (e.code !== 'EPERM' && e.code !== 'EBUSY' && e.code !== 'EACCES') throw e; Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 150); }
  }
  fs.writeFileSync(file, text); try { fs.unlinkSync(tmp); } catch (e) { /* не страшно */ }
}
function walk(dir, ext, out) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const f = dir + '/' + e.name;
    if (e.isDirectory()) walk(f, ext, out); else if (e.name.endsWith(ext)) out.push(f);
  }
  return out;
}

// --- комментарии Rocq вырезаются с сохранением переводов строк (вложенные (* *), строки в кавычках) ---
function stripComments(s) {
  let out = ''; let depth = 0; let inStr = false;
  for (let i = 0; i < s.length; i++) {
    const c = s[i], d = s[i + 1];
    if (depth === 0 && inStr) { out += c; if (c === '"') inStr = false; continue; }
    if (depth === 0 && c === '"') { inStr = true; out += c; continue; }
    if (c === '(' && d === '*') { depth++; i++; out += '  '; continue; }
    if (depth > 0 && c === '*' && d === ')') { depth--; i++; out += '  '; continue; }
    if (depth > 0) { out += c === '\n' ? '\n' : ' '; continue; }
    out += c;
  }
  return out;
}

const KW = 'Theorem|Lemma|Corollary|Proposition|Fact|Remark|Property|Definition|Fixpoint|CoFixpoint|Function|Inductive|CoInductive|Variant|Record|Structure|Class|Instance|Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|Hypotheses|Variable|Variables|Example|Let|Ltac|Notation|Abbreviation|Scheme|Coercion';
const DECL = new RegExp('^\\s*(?:(?:Local|Global|Program|Polymorphic|Monomorphic|#\\[[^\\]]*\\])\\s+)*(' + KW + ')\\s+([A-Za-z_][A-Za-z0-9_\']*)');
const PROOFY = new Set(['Theorem', 'Lemma', 'Corollary', 'Proposition', 'Fact', 'Remark', 'Property', 'Example']);

// Индекс: имя -> [{file, line, kind, mod, stmt}], по всем .v репозитория. Кэш в папке сборки.
function buildIndex() {
  const cacheFile = BUILD + '/decl-index.json';
  const files = [...walk(REPO + '/src', '.v', []), ...walk(REPO + '/Architecture_of_Reasoning', '.v', [])];
  let cache = {}; try { cache = JSON.parse(fs.readFileSync(cacheFile, 'utf8')); } catch (e) { /* нет кэша */ }
  const next = {}; let parsed = 0;
  for (const f of files) {
    const rel = f.slice(REPO.length + 1); const st = fs.statSync(f); const key = st.mtimeMs + ':' + st.size;
    if (cache[rel] && cache[rel].key === key) { next[rel] = cache[rel]; continue; }
    parsed++;
    const raw = fs.readFileSync(f, 'utf8'); const text = stripComments(raw); const lines = text.split(/\r?\n/);
    const decls = []; const mods = [];
    for (let i = 0; i < lines.length; i++) {
      const L = lines[i];
      let m = L.match(/^\s*Module\s+(?!Type\b)(?:Import\s+|Export\s+)?([A-Za-z_][A-Za-z0-9_']*)\s*\.\s*$/);
      if (m) { mods.push(m[1]); continue; }
      m = L.match(/^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\./);
      if (m && mods.length && mods[mods.length - 1] === m[1]) { mods.pop(); continue; }
      m = L.match(DECL);
      if (!m) continue;
      // утверждение: от объявления до первой точки, за которой пробел или конец строки
      let stmt = ''; for (let j = i; j < Math.min(lines.length, i + 40); j++) { stmt += ' ' + lines[j]; const k = stmt.search(/\.(\s|$)/); if (k >= 0) { stmt = stmt.slice(0, k + 1); break; } }
      stmt = stmt.replace(/\s+/g, ' ').trim();
      decls.push({ name: m[2], kind: m[1], line: i + 1, mod: mods.join('.'), stmt: stmt.slice(0, 700) });
    }
    next[rel] = { key, sha: sha1(fs.readFileSync(f)), qed: (text.match(/\bQed\./g) || []).length, admitted: (text.match(/\bAdmitted\./g) || []).length, axioms: decls.filter((d) => /^(Axiom|Axioms|Conjecture)$/.test(d.kind)).length, params: decls.filter((d) => /^Parameters?$/.test(d.kind)).length, lines: lines.length, decls };
  }
  if (parsed) writeAtomic(cacheFile, JSON.stringify(next));
  const byName = new Map(); const byBase = new Map();
  for (const [rel, rec] of Object.entries(next)) {
    const b = path.basename(rel); (byBase.get(b) || byBase.set(b, []).get(b)).push(rel);
    for (const d of rec.decls) (byName.get(d.name) || byName.set(d.name, []).get(d.name)).push(Object.assign({ file: rel }, d));
  }
  return { files: next, byName, byBase };
}

// Номера файлов базы docs/database/_files.tsv
function fileNums() {
  const m = new Map();
  for (const line of fs.readFileSync(REPO + '/docs/database/_files.tsv', 'utf8').split(/\r?\n/).slice(1)) { const [n, p] = line.split('\t'); if (p) m.set(p.trim(), +n); }
  return m;
}

const modOf = (rel) => rel.startsWith('src/') ? 'ToS.' + rel.slice(4, -2).replace(/\//g, '.') : 'ToS_Arch.' + rel.slice('Architecture_of_Reasoning/'.length, -2).replace(/\//g, '.');

// Print Assumptions для списка [{file, name, mod}] -> Map 'file|name' -> текст. Нужна собранная папка BUILD.
function printAssumptions(items) {
  const cacheFile = BUILD + '/pa-cache.json';
  let cache = {}; try { cache = JSON.parse(fs.readFileSync(cacheFile, 'utf8')); } catch (e) { /* нет кэша */ }
  const res = new Map(); const todo = new Map(); // file -> [item]
  for (const it of items) {
    const id = it.file + '|' + (it.mod ? it.mod + '.' : '') + it.name; const vo = BUILD + '/' + it.file + 'o';
    if (!fs.existsSync(vo)) { res.set(id, 'не собрано: нет ' + it.file + 'o'); continue; }
    const stamp = fs.statSync(vo).mtimeMs;
    if (cache[id] && cache[id].stamp === stamp) { res.set(id, cache[id].out); continue; }
    (todo.get(it.file) || todo.set(it.file, []).get(it.file)).push(Object.assign({ id, stamp }, it));
  }
  fs.mkdirSync(BUILD + '/_pa', { recursive: true });
  for (const [file, list0] of todo) {
    let list = list0.slice(); const base = '_pa/pa_' + sha1(file).slice(0, 10) + '_' + process.pid;
    for (let guard = 0; guard < 400 && list.length; guard++) {
      const src = ['Require ' + modOf(file) + '.'];
      for (const it of list) { src.push('Goal True. idtac "@@PA ' + it.id + '". Abort.'); src.push('Print Assumptions ' + modOf(file) + '.' + (it.mod ? it.mod + '.' : '') + it.name + '.'); }
      fs.writeFileSync(BUILD + '/' + base + '.v', src.join('\n') + '\n');
      const r = cp.spawnSync(ROCQ + '/bin/coqc.exe', [...QFLAGS, base + '.v'], { cwd: BUILD, env: ENV, encoding: 'utf8', maxBuffer: 1 << 28 });
      const parts = (r.stdout || '').split(/^@@PA /m).slice(1);
      const got = new Set();
      for (const p of parts) {
        const nl = p.indexOf('\n'); const id = p.slice(0, nl).trim(); const out = p.slice(nl + 1).replace(/\s+/g, ' ').trim();
        if (!out) continue; // маркер напечатан, а ответа нет: команда упала
        const it = list.find((x) => x.id === id); if (!it) continue;
        res.set(id, out); cache[id] = { stamp: it.stamp, out }; got.add(id);
      }
      if (r.status === 0) break;
      const m = (r.stderr || '').match(/line (\d+)/); const ln = m ? +m[1] : 0;
      const bad = list[Math.floor((ln - 2) / 2)];
      if (!bad) { for (const it of list) if (!got.has(it.id)) res.set(it.id, 'ошибка проверки: ' + (r.stderr || '').replace(/\s+/g, ' ').slice(0, 200)); break; }
      res.set(bad.id, 'не константа или не найдена: ' + (r.stderr || '').replace(/\s+/g, ' ').replace(/^.*?Error:/, '').trim().slice(0, 160));
      list = list.filter((x) => x !== bad && !got.has(x.id));
    }
  }
  // несколько запусков могут идти одновременно: перед записью перечитать кэш и записать через переименование
  let latest = {}; try { latest = JSON.parse(fs.readFileSync(cacheFile, 'utf8')); } catch (e) { /* нет кэша */ }
  writeAtomic(cacheFile, JSON.stringify(Object.assign(latest, cache)));
  return res;
}

// Locate для имён без объявления верхнего уровня (конструкторы, поля записей, имена стандартной библиотеки).
const VERNAC = new Set(('Theorem Lemma Corollary Proposition Fact Remark Definition Fixpoint CoFixpoint Inductive CoInductive Record Structure Class Instance Axiom Parameter Hypothesis Variable Example Let Ltac Notation Module Section End Proof Qed Defined Admitted Abort Require Import Export From Print Check Compute Eval Locate Search About Open Close Scope Set Unset Goal Context Arguments Opaque Transparent Hint Existing Program Local Global ' +
  'forall exists fun match with end if then else let in return as fix cofix Prop Type Set SProp at where using struct').split(' '));
function locate(names0, files) {
  const res = new Map();
  let names = [];
  for (const n of names0) { if (VERNAC.has(n)) res.set(n, 'ключевое слово Rocq'); else names.push(n); }
  if (!names.length) return res;
  fs.mkdirSync(BUILD + '/_pa', { recursive: true });
  const built = files.filter((f) => fs.existsSync(BUILD + '/' + f + 'o'));
  const base = '_pa/loc_' + sha1(names.join(',') + files.join(',')).slice(0, 10) + '_' + process.pid;
  for (let guard = 0; guard < 60 && names.length; guard++) {
    const src = ['From Stdlib Require QArith ZArith Lia Lqa List Classical Arith Qabs Bool.'];
    for (const f of built) src.push('Require ' + modOf(f) + '.');
    const head = src.length;
    for (const n of names) { src.push('Goal True. idtac "@@LOC ' + n + '". Abort.'); src.push('Locate ' + n + '.'); }
    fs.writeFileSync(BUILD + '/' + base + '.v', src.join('\n') + '\n');
    const r = cp.spawnSync(ROCQ + '/bin/coqc.exe', [...QFLAGS, base + '.v'], { cwd: BUILD, env: ENV, encoding: 'utf8', maxBuffer: 1 << 28 });
    for (const p of (r.stdout || '').split(/^@@LOC /m).slice(1)) { const nl = p.indexOf('\n'); const out = p.slice(nl + 1).replace(/\s+/g, ' ').trim(); if (out) res.set(p.slice(0, nl).trim(), out); }
    if (r.status === 0) break;
    // синтаксическая ошибка останавливает весь файл: убрать виновное имя и повторить
    const m = (r.stderr || '').match(/line (\d+)/); const bad = m ? names[Math.floor((+m[1] - head - 1) / 2)] : null;
    if (!bad) { for (const n of names) if (!res.has(n)) res.set(n, 'ошибка проверки: ' + (r.stderr || '').replace(/\s+/g, ' ').slice(0, 160)); break; }
    res.set(bad, 'не имя Rocq (синтаксическая ошибка при Locate)');
    names = names.filter((n) => n !== bad);
    for (const n of names) res.delete(n);
  }
  return res;
}

// К какому объявлению относится имя, названное в главе. entries: [{name, hint}] (hint -- базовое имя файла из
// записи Модуль.имя). Порядок: указанный модуль -> файл, названный в главе -> единственное объявление ->
// Locate в окружении файлов главы (отличает имя стандартной библиотеки, конструктор, поле записи) -> первое из многих.
const SECTION_LOCAL = new Set(['Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Let']);
function resolveNames(idx, entries, chapterPaths) {
  const res = new Map(); const ask = [];
  for (const e of entries) {
    const all = idx.byName.get(e.name) || []; const top = all.filter((c) => !SECTION_LOCAL.has(c.kind));
    const r = { name: e.name, candidates: top.length, others: [], decl: null, type: 'missing', how: '', locate: null };
    const hinted = e.hint ? top.filter((c) => path.basename(c.file) === e.hint) : [];
    const inCh = top.filter((c) => chapterPaths.has(c.file));
    if (hinted.length) { r.decl = hinted[0]; r.how = 'по указанию модуля'; }
    else if (inCh.length) { r.decl = inCh[0]; r.how = 'файл назван в главе'; }
    else if (top.length === 1) { r.decl = top[0]; r.how = 'единственное объявление'; }
    else if (!top.length && idx.byBase.has(e.name + '.v')) { r.type = 'module'; r.moduleFile = idx.byBase.get(e.name + '.v')[0]; }
    else ask.push(r);
    if (r.decl) { r.type = 'decl'; r.others = top.filter((c) => c !== r.decl).map((c) => c.file + ':' + c.line); }
    res.set(e.name, r);
  }
  const loc = locate(ask.map((r) => r.name), [...chapterPaths]);
  for (const r of ask) {
    const a = loc.get(r.name) || ''; r.locate = a; const top = (idx.byName.get(r.name) || []).filter((c) => !SECTION_LOCAL.has(c.kind));
    const viaLocate = top.find((c) => a.includes(modOf(c.file) + '.' + (c.mod ? c.mod + '.' : '') + r.name));
    if (viaLocate) { r.decl = viaLocate; r.type = 'decl'; r.how = 'по Locate в окружении файлов главы'; }
    else if (/^(ключевое слово Rocq|не имя Rocq)/.test(a)) { r.type = 'keyword'; }
    else if (a && !/^No object of basename/.test(a) && !/^ошибка проверки/.test(a)) { r.type = 'external'; r.how = 'Locate'; }
    else if (top.length) { r.decl = top[0]; r.type = 'decl'; r.how = 'файл в главе не назван; объявлений ' + top.length; }
    if (r.decl) r.others = top.filter((c) => c !== r.decl).map((c) => c.file + ':' + c.line);
  }
  return res;
}

// Ссылки главы: все фрагменты в обратных кавычках с номерами строк.
function chapterRefs(file) {
  const text = fs.readFileSync(file, 'utf8'); const lines = text.split(/\r?\n/); const refs = [];
  // Код в обратных кавычках может переходить со строки на строку (`process_continuum_⏎hypothesis`), поэтому
  // разбор идёт по абзацам; блоки ``` … ``` ссылок не содержат и пропускаются. broken: имя разорвано переводом строки.
  let inside = false; let para = []; let paraStart = 0;
  const flush = () => {
    if (!para.length) return;
    const body = para.join('\n'); const offs = [0]; for (const l of para) offs.push(offs[offs.length - 1] + l.length + 1);
    for (const m of body.matchAll(/`([^`]+)`/g)) {
      let x = m[1]; let broken = false;
      if (x.includes('\n')) {
        // разрыв внутри имени виден по знаку «_», «.» или «/» у края строки; иначе это два слова (`Print⏎Assumptions`)
        const joined = x.replace(/\s*\n\s*/g, '');
        if (/[_.\/]\s*\n|\n\s*[_.\/]/.test(x) && /^[A-Za-z0-9_.'\/]+$/.test(joined)) { x = joined; broken = true; } else x = x.replace(/\s*\n\s*/g, ' ');
      }
      x = x.trim(); let type = 'other'; let name = x; let fileHint = null;
      let k = 0; while (k + 1 < offs.length && offs[k + 1] <= m.index) k++;
      if (/^([A-Za-z0-9_\/]+\.v)$/.test(x)) type = 'file';
      else if (/^[A-Za-z_][A-Za-z0-9_']*$/.test(x)) type = 'ident';
      else if (/^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)+$/.test(x)) { type = 'qualified'; const p = x.split('.'); name = p[p.length - 1]; fileHint = p[p.length - 2] + '.v'; }
      refs.push({ line: paraStart + k + 1, raw: x, type, name, fileHint, broken });
    }
    para = [];
  };
  for (let i = 0; i < lines.length; i++) {
    if (/^\s*```/.test(lines[i])) { flush(); inside = !inside; continue; }
    if (inside) continue;
    if (!lines[i].trim()) { flush(); continue; }
    if (!para.length) paraStart = i;
    para.push(lines[i]);
  }
  flush();
  return { lines, refs };
}

module.exports = { REPO, BUILD, TOM, ROCQ, ENV, QFLAGS, sha1, walk, stripComments, buildIndex, fileNums, modOf, printAssumptions, locate, resolveNames, chapterRefs, PROOFY };
