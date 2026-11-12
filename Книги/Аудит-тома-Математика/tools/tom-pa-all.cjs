// tom-pa-all.cjs -- Print Assumptions для ВСЕХ объявлений формализации (реестр цены по компилятору).
//
//   node tom-pa-all.cjs [-j N]      пишет <папка сборки>/pa-all.tsv: файл, строка, вид, имя, допущения
//   node tom-pa-all.cjs summary     сводка по готовому pa-all.tsv: сколько объявлений на каких аксиомах
//
// Нужна собранная папка (tom-build.cjs). Несобранные файлы пропускаются и перечисляются в сводке.
const fs = require('fs'); const cp = require('child_process');
const L = require('./tom-lib.cjs');
const OUT = L.BUILD + '/pa-all.tsv';
const SKIP = new Set(['Ltac', 'Notation', 'Abbreviation', 'Let', 'Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Scheme', 'Coercion']);

function runFile(file, decls) {
  return new Promise((resolve) => {
    const base = '_pa/all_' + L.sha1(file).slice(0, 12); const rows = []; let list = decls.slice(); let guard = 0;
    const step = () => {
      if (!list.length || guard++ > 600) return resolve(rows);
      const src = ['Require ' + L.modOf(file) + '.'];
      for (const d of list) { src.push('Goal True. idtac "@@PA ' + d.line + ' ' + d.name + '". Abort.'); src.push('Print Assumptions ' + L.modOf(file) + '.' + (d.mod ? d.mod + '.' : '') + d.name + '.'); }
      fs.writeFileSync(L.BUILD + '/' + base + '.v', src.join('\n') + '\n');
      const p = cp.spawn(L.ROCQ + '/bin/coqc.exe', [...L.QFLAGS, base + '.v'], { cwd: L.BUILD, env: L.ENV });
      let so = '', se = ''; p.stdout.on('data', (x) => { so += x; }); p.stderr.on('data', (x) => { se += x; });
      p.on('close', (code) => {
        const got = new Set();
        for (const part of so.split(/^@@PA /m).slice(1)) {
          const nl = part.indexOf('\n'); const [ln, name] = part.slice(0, nl).trim().split(' '); const out = part.slice(nl + 1).replace(/\s+/g, ' ').trim();
          if (!out) continue; const d = list.find((x) => x.line === +ln && x.name === name); if (!d) continue;
          rows.push([file, d.line, d.kind, d.name, out]); got.add(d);
        }
        if (code === 0) return resolve(rows);
        const m = se.match(/line (\d+)/); const bad = m ? list[Math.floor((+m[1] - 2) / 2)] : null;
        if (!bad) { for (const d of list) if (!got.has(d)) rows.push([file, d.line, d.kind, d.name, 'ОШИБКА ПРОВЕРКИ: ' + se.replace(/\s+/g, ' ').slice(0, 120)]); return resolve(rows); }
        rows.push([file, bad.line, bad.kind, bad.name, 'НЕ КОНСТАНТА: ' + se.replace(/\s+/g, ' ').replace(/^.*?Error:/, '').trim().slice(0, 120)]);
        list = list.filter((x) => x !== bad && !got.has(x)); step();
      });
    };
    step();
  });
}

async function all(J) {
  const idx = L.buildIndex(); fs.mkdirSync(L.BUILD + '/_pa', { recursive: true });
  const files = Object.keys(idx.files).sort(); const notBuilt = []; const queue = [];
  for (const f of files) {
    if (!fs.existsSync(L.BUILD + '/' + f + 'o')) { notBuilt.push(f); continue; }
    const seen = new Set(); const decls = idx.files[f].decls.filter((d) => !SKIP.has(d.kind) && !seen.has(d.mod + '.' + d.name) && seen.add(d.mod + '.' + d.name));
    if (decls.length) queue.push([f, decls]);
  }
  const w = fs.createWriteStream(OUT); w.write('file\tline\tkind\tname\tassumptions\n');
  let done = 0, total = queue.length; const t0 = Date.now();
  const worker = async () => { while (queue.length) { const [f, decls] = queue.shift(); const rows = await runFile(f, decls); for (const r of rows) w.write(r.join('\t') + '\n'); if (++done % 100 === 0) console.log(`[${((Date.now() - t0) / 60000).toFixed(1)} мин] файлов ${done} из ${total}`); } };
  await Promise.all(Array.from({ length: J }, worker));
  w.end(); fs.writeFileSync(L.BUILD + '/pa-all-notbuilt.txt', notBuilt.join('\n') + '\n');
  console.log(`готово: файлов ${done}, не собрано ${notBuilt.length}; ${((Date.now() - t0) / 60000).toFixed(1)} мин -> ${OUT}`);
}

function summary() {
  const rows = fs.readFileSync(OUT, 'utf8').split('\n').slice(1).filter(Boolean).map((l) => l.split('\t'));
  const axOf = (a) => { if (a.startsWith('Closed under')) return 'без допущений'; if (/^(ОШИБКА|НЕ КОНСТАНТА)/.test(a)) return 'не проверено'; 
    // имена аксиом в выводе -- полные (Модуль.имя); связанные переменные типов (P, x) и QArith_base.* отбрасываются
    const names = [...a.matchAll(/(?:^Axioms: |\s)([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+) :/g)].map((m) => m[1]).filter((n) => !n.startsWith('QArith_base.'));
    return [...new Set(names)].sort().join(' + ') || a.slice(0, 60);
  };
  const by = new Map(); const proofy = new Map();
  for (const r of rows) { const k = axOf(r[4]); by.set(k, (by.get(k) || 0) + 1); if (L.PROOFY.has(r[2])) proofy.set(k, (proofy.get(k) || 0) + 1); }
  console.log(`объявлений проверено: ${rows.length}; из них теорем и лемм: ${[...proofy.values()].reduce((a, b) => a + b, 0)}`);
  console.log('\nтеоремы и леммы по набору допущений:');
  for (const [k, v] of [...proofy.entries()].sort((a, b) => b[1] - a[1])) console.log(`  ${String(v).padStart(6)}  ${k}`);
  const open = rows.filter((r) => !r[4].startsWith('Closed under'));
  fs.writeFileSync(L.BUILD + '/pa-not-closed.tsv', 'file\tline\tkind\tname\taxioms\n' + open.map((r) => [r[0], r[1], r[2], r[3], axOf(r[4])].join('\t')).join('\n') + '\n');
  console.log('\nне замкнутых объявлений: ' + open.length + ' -> ' + L.BUILD + '/pa-not-closed.tsv');
  console.log('\nвсе объявления (включая определения) по набору допущений:');
  for (const [k, v] of [...by.entries()].sort((a, b) => b[1] - a[1])) console.log(`  ${String(v).padStart(6)}  ${k}`);
}

const args = process.argv.slice(2);
if (args[0] === 'summary') summary(); else all(args[0] === '-j' ? +args[1] : 10);
