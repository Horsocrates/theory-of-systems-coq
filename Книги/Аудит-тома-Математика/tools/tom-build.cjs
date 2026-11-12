// tom-build.cjs -- сборка формализации в отдельной папке вне OneDrive (шаг 0 аудита).
//
//   node tom-build.cjs sync                 скопировать изменившиеся .v из репозитория в папку сборки
//   node tom-build.cjs build [-j N] [цели]  собрать всё (или только цели и их зависимости); цели -- пути от корня сборки
//   node tom-build.cjs status               сколько собрано / упало / осталось
//
// Репозиторий не меняется: .v только читаются. Папка сборки: BUILD (ниже) или переменная TOS_BUILD.
// Готовые .vo переиспользуются: файл пересобирается, если его .v или .vo зависимости новее.
const fs = require('fs'); const path = require('path'); const cp = require('child_process'); const crypto = require('crypto');

const REPO = 'C:/Users/abary/OneDrive/Desktop/theory-of-systems-coq';
const BUILD = process.env.TOS_BUILD || 'C:/Users/abary/tos-audit-build';
const ROCQ = 'C:/Programs/Rocq-Platform~9.0~2025.08';
const ENV = Object.assign({}, process.env, { ROCQLIB: ROCQ.replace(/\//g, '\\') + '\\lib\\coq' });
const QFLAGS = ['-Q', 'src', 'ToS', '-Q', 'Architecture_of_Reasoning', 'ToS_Arch'];
const SKIP = new Set(['src/TestNode.v']); // не зарегистрирован в _CoqProject, не компилируется

function walk(dir, out) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const f = dir + '/' + e.name;
    if (e.isDirectory()) walk(f, out); else if (e.name.endsWith('.v')) out.push(f);
  }
  return out;
}
const sha = (f) => crypto.createHash('sha1').update(fs.readFileSync(f)).digest('hex');

function sync() {
  let copied = 0, removed = 0; const seen = new Set();
  for (const top of ['src', 'Architecture_of_Reasoning']) {
    for (const f of walk(REPO + '/' + top, [])) {
      const rel = f.slice(REPO.length + 1); seen.add(rel);
      const dst = BUILD + '/' + rel;
      if (!fs.existsSync(dst) || sha(dst) !== sha(f)) { fs.mkdirSync(path.dirname(dst), { recursive: true }); fs.copyFileSync(f, dst); const now = new Date(); fs.utimesSync(dst, now, now); copied++; } // время правки -- «сейчас»: иначе при возврате к прежнему тексту .vo от пробной правки считался бы свежим
    }
    if (fs.existsSync(BUILD + '/' + top)) for (const f of walk(BUILD + '/' + top, [])) {
      const rel = f.slice(BUILD.length + 1);
      if (!seen.has(rel)) { fs.unlinkSync(f); removed++; }
    }
  }
  const list = [...seen].filter((r) => !SKIP.has(r)).sort();
  fs.writeFileSync(BUILD + '/_CoqProject', ['-Q src ToS', '-Q Architecture_of_Reasoning ToS_Arch', ...list].join('\n') + '\n');
  const r = cp.spawnSync(ROCQ + '/bin/coqdep.exe', ['-f', '_CoqProject'], { cwd: BUILD, env: ENV, encoding: 'utf8', maxBuffer: 1 << 28 });
  if (r.status !== 0 || (r.stderr || '').includes('Error')) { console.error(r.stderr); process.exit(1); }
  fs.writeFileSync(BUILD + '/deps.txt', r.stdout);
  console.log(`sync: файлов ${list.length}, скопировано ${copied}, удалено ${removed}; deps.txt обновлён`);
}

function readDeps() {
  const deps = new Map(); // src/X.v -> [src/Y.v ...]
  for (const line of fs.readFileSync(BUILD + '/deps.txt', 'utf8').split(/\r?\n/)) {
    const i = line.indexOf(': '); if (i < 0) continue;
    const tgt = line.slice(0, i).split(' ')[0]; if (!tgt.endsWith('.vo')) continue;
    const v = tgt.replace(/\.vo$/, '.v');
    const ds = line.slice(i + 2).split(' ').filter((x) => x.endsWith('.vo') && !x.includes(':')).map((x) => x.replace(/\.vo$/, '.v'));
    deps.set(v, ds);
  }
  return deps;
}
const mtime = (f) => { try { return fs.statSync(f).mtimeMs; } catch (e) { return 0; } };

function closure(deps, targets) {
  const need = new Set(); const st = [...targets];
  while (st.length) { const x = st.pop(); if (need.has(x)) continue; if (!deps.has(x)) { console.error('нет в deps: ' + x); continue; } need.add(x); for (const d of deps.get(x)) st.push(d); }
  return need;
}

function fresh(v, deps) {
  const vo = BUILD + '/' + v + 'o'; const t = mtime(vo); if (!t) return false;
  if (mtime(BUILD + '/' + v) > t) return false;
  for (const d of deps.get(v)) if (mtime(BUILD + '/' + d + 'o') > t) return false;
  return true;
}

function build(args) {
  let J = 12; const targets = [];
  for (let i = 0; i < args.length; i++) { if (args[i] === '-j') J = +args[++i]; else targets.push(args[i].replace(/\\/g, '/')); }
  const deps = readDeps();
  const want = targets.length ? closure(deps, targets) : new Set(deps.keys());
  // приоритет: сначала замыкание целей из файла priority.txt (если есть), затем остальное
  let prio = new Set();
  if (fs.existsSync(BUILD + '/priority.txt')) prio = closure(deps, fs.readFileSync(BUILD + '/priority.txt', 'utf8').split(/\r?\n/).map((s) => s.trim()).filter(Boolean));
  const state = new Map(); // v -> done|failed|skipped|running
  const log = fs.createWriteStream(BUILD + '/build.log', { flags: 'a' });
  const times = fs.createWriteStream(BUILD + '/build-times.tsv', { flags: 'a' });
  const order = [...want].sort((a, b) => (prio.has(b) - prio.has(a)) || a.localeCompare(b));
  let running = 0, done = 0, failed = 0, skipped = 0, reused = 0; const t0 = Date.now();
  log.write(`\n=== build ${new Date().toISOString()} целей ${want.size} j=${J}\n`);
  function ready(v) { return deps.get(v).every((d) => !want.has(d) ? fs.existsSync(BUILD + '/' + d + 'o') : state.get(d) === 'done'); }
  function blocked(v) { return deps.get(v).some((d) => state.get(d) === 'failed' || state.get(d) === 'skipped'); }
  function pump() {
    let progressed = true;
    while (progressed) {
      progressed = false;
      for (const v of order) {
        if (state.has(v)) continue;
        if (blocked(v)) { state.set(v, 'skipped'); skipped++; log.write(`SKIP ${v}\n`); progressed = true; continue; }
        if (!ready(v)) continue;
        if (fresh(v, deps)) { state.set(v, 'done'); reused++; progressed = true; continue; }
        if (running >= J) continue;
        state.set(v, 'running'); running++; const ts = Date.now();
        const p = cp.spawn(ROCQ + '/bin/coqc.exe', [...QFLAGS, v], { cwd: BUILD, env: ENV });
        let err = ''; p.stderr.on('data', (d) => { err += d; }); p.stdout.on('data', () => {});
        p.on('close', (code) => {
          running--; const dt = ((Date.now() - ts) / 1000).toFixed(1);
          if (code === 0) { state.set(v, 'done'); done++; times.write(`${v}\t${dt}\n`); }
          else { state.set(v, 'failed'); failed++; log.write(`FAIL ${v} (${dt}s)\n${err.slice(0, 3000)}\n`); }
          if ((done + failed) % 50 === 0) console.log(`[${((Date.now() - t0) / 60000).toFixed(1)} мин] собрано ${done}, взято готовых ${reused}, упало ${failed}, пропущено ${skipped}, из ${want.size}`);
          pump();
        });
      }
    }
    if (running === 0 && [...want].every((v) => state.has(v) && state.get(v) !== 'running')) {
      const msg = `ИТОГ: собрано ${done}, взято готовых ${reused}, упало ${failed}, пропущено из-за зависимостей ${skipped}, всего ${want.size}; ${((Date.now() - t0) / 60000).toFixed(1)} мин`;
      console.log(msg); log.write(msg + '\n'); log.end(); times.end();
    }
  }
  pump();
}

function status() {
  const deps = readDeps(); let ok = 0; const miss = [];
  for (const v of deps.keys()) if (fs.existsSync(BUILD + '/' + v + 'o')) ok++; else miss.push(v);
  console.log(`собрано ${ok} из ${deps.size}; без .vo: ${miss.length}`);
  if (miss.length && miss.length <= 40) console.log(miss.join('\n'));
}

const cmd = process.argv[2];
if (cmd === 'sync') sync(); else if (cmd === 'build') build(process.argv.slice(3)); else if (cmd === 'status') status();
else console.log('usage: node tom-build.cjs sync | build [-j N] [цели] | status');
