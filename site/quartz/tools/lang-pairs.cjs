// lang-pairs.cjs — связывает русскую сборку (public/) и английскую (public/en/) после `quartz build`.
// Для каждой страницы:
//   • кнопка языка в группе toolbar (рядом с поиском; на проде nav.js Алега переносит группу в шапку):
//     RU-страница → её перевод, а без перевода — английская главная; EN-страница → её русский оригинал;
//   • <link rel="alternate" hreflang="ru|en|x-default"> в <head>, если у страницы есть пара;
//   • EN-страница со status: draft — строка «Translation draft, <дата>» в начале статьи;
//   • ссылки EN-страниц на ещё не переведённые страницы ведут на русские (если дана таблица слагов).
// Пары задаёт поле translationOf во frontmatter EN-страниц (путь RU-файла от content/).
// Адреса пишутся в русской форме сборки (кириллица); на проде их, как и всё остальное, переводит web_translit.py.
//
//   node tools/lang-pairs.cjs --ru public --en public/en --content-en content-en
//        [--en-base /en] [--slugs <slugs_en.tsv>] [--domain localhost:8080]
const fs = require('fs');
const path = require('path');

function arg(name, dflt) {
  const i = process.argv.indexOf(`--${name}`);
  return i > 0 && process.argv[i + 1] ? process.argv[i + 1] : dflt;
}
const RU = path.resolve(arg('ru', 'public'));
const EN = path.resolve(arg('en', 'public/en'));
const CEN = path.resolve(arg('content-en', 'content-en'));
const EN_BASE = arg('en-base', '/en').replace(/\/$/, '');
const DOMAIN = arg('domain', 'localhost:8080');
const SLUGS = arg('slugs', '');

// ── Quartz slugs (порт slugifyFilePath из @quartz-community/utils) ─────────────
function slugifyPath(s) {
  return s.split('/').map(seg => seg.replace(/\s/g, '-').replace(/&/g, '-and-').replace(/%/g, '-percent')
    .replace(/\?/g, '').replace(/#/g, '').toLowerCase()).join('/').replace(/\/$/, '');
}
function slugifyFilePath(fp) {
  fp = fp.replace(/^\/+|\/+$/g, '').replace(/\.md$/, '');
  let slug = slugifyPath(fp);
  if (slug.endsWith('_index')) slug = slug.replace(/_index$/, 'index');
  const seg = slug.split('/');
  if (seg.length >= 2 && seg[seg.length - 1] === seg[seg.length - 2]) { seg[seg.length - 1] = 'index'; slug = seg.join('/'); }
  return slug;
}
const slugToUrl = slug => (slug === 'index' ? '' : slug.endsWith('/index') ? slug.slice(0, -'index'.length) : slug);
const norm = p => p.replace(/^\/+/, '').replace(/\/index$/, '').replace(/^index$/, '').replace(/\/$/, '');

// ── английские сегменты прода (порт translit/en_segment из web_translit.py) ───
const TR = { 'а': 'a', 'б': 'b', 'в': 'v', 'г': 'g', 'д': 'd', 'е': 'e', 'ё': 'yo', 'ж': 'zh', 'з': 'z', 'и': 'i', 'й': 'y',
  'к': 'k', 'л': 'l', 'м': 'm', 'н': 'n', 'о': 'o', 'п': 'p', 'р': 'r', 'с': 's', 'т': 't', 'у': 'u', 'ф': 'f', 'х': 'h',
  'ц': 'ts', 'ч': 'ch', 'ш': 'sh', 'щ': 'sch', 'ъ': '', 'ы': 'y', 'ь': '', 'э': 'e', 'ю': 'yu', 'я': 'ya',
  'і': 'i', 'ї': 'yi', 'є': 'ye', 'ґ': 'g' };
const translit = s => [...s].map(ch => { const l = ch.toLowerCase(); if (!(l in TR)) return ch; const t = TR[l]; return ch !== l ? t.charAt(0).toUpperCase() + t.slice(1) : t; }).join('');
let SLUG_MAP = null;
if (SLUGS && fs.existsSync(SLUGS)) {
  SLUG_MAP = new Map();
  for (const line of fs.readFileSync(SLUGS, 'utf8').split(/\r?\n/)) {
    if (!line.trim() || line.startsWith('#')) continue;
    const [k, v] = line.split('\t');
    if (k && v && k.trim() && v.trim()) SLUG_MAP.set(k.trim(), v.trim());
  }
}
const enSegment = seg => { const t = translit(seg); if (t === seg) return seg; return (SLUG_MAP && SLUG_MAP.get(t.toLowerCase())) || t; };
const enPath = p => p.split('/').map(enSegment).join('/');

// ── пары из frontmatter content-en ─────────────────────────────────────────────
function walk(dir, pred, skip) {
  const out = [];
  (function rec(d) {
    for (const e of fs.readdirSync(d, { withFileTypes: true })) {
      const p = path.join(d, e.name);
      if (skip && skip(p)) continue;
      if (e.isDirectory()) rec(p); else if (pred(e.name)) out.push(p);
    }
  })(dir);
  return out;
}
const ruToEn = new Map(), enToRu = new Map(), enMeta = new Map();
for (const f of walk(CEN, n => n.endsWith('.md'))) {
  const s = fs.readFileSync(f, 'utf8');
  const fm = (s.match(/^---\r?\n([\s\S]*?)\r?\n---/) || [, ''])[1];
  const get = k => { const m = fm.match(new RegExp(`^${k}:\\s*"?([^"\\r\\n]*)"?\\s*$`, 'm')); return m ? m[1].trim() : ''; };
  const enSlug = slugifyFilePath(path.relative(CEN, f).split(path.sep).join('/'));
  enMeta.set(enSlug, { status: get('status'), translated: get('translated') });
  const tOf = get('translationOf');
  if (tOf) { const ruSlug = slugifyFilePath(tOf); ruToEn.set(ruSlug, enSlug); enToRu.set(enSlug, ruSlug); }
}

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
const fmtDate = d => { const m = d.match(/^(\d{4})-(\d{2})-(\d{2})$/); return m ? `${+m[3]} ${MONTHS[+m[2] - 1]} ${m[1]}` : d; };
const esc = s => s.replace(/&/g, '&amp;').replace(/"/g, '&quot;');
const ruHref = slug => '/' + slugToUrl(slug);
const enHref = slug => EN_BASE + '/' + slugToUrl(slug);
const abs = href => `https://${DOMAIN}${href}`;

// ── вставки в HTML ─────────────────────────────────────────────────────────────
function appendToToolbar(html, inner) {
  const start = html.indexOf('<div class="flex-component"');
  if (start < 0) return html;
  const re = /<\/?div\b[^>]*>/g;
  re.lastIndex = start;
  let depth = 0, m;
  while ((m = re.exec(html))) {
    depth += m[0].startsWith('</') ? -1 : 1;
    if (depth === 0) {
      const wrap = '<div style="flex-grow: 0; flex-shrink: 1; flex-basis: auto; order: 0; align-self: center; justify-self: center;">' + inner + '</div>';
      return html.slice(0, m.index) + wrap + html.slice(m.index);
    }
  }
  return html;
}
function headLinks(ruSlug, enSlug) {
  return `<link rel="alternate" hreflang="ru" href="${esc(abs(ruHref(ruSlug)))}" data-lang-pairs/>`
    + `<link rel="alternate" hreflang="en" href="${esc(abs(enHref(enSlug)))}" data-lang-pairs/>`
    + `<link rel="alternate" hreflang="x-default" href="${esc(abs(ruHref(ruSlug)))}" data-lang-pairs/>`;
}

const stats = { ru: 0, ruPaired: 0, en: 0, enPaired: 0, drafts: 0, linksToRu: 0, linksUnresolved: new Set() };

// RU-сборка (без вложенной /en/)
const enDirAbs = EN;
for (const f of walk(RU, n => n.endsWith('.html'), p => p === enDirAbs)) {
  let html = fs.readFileSync(f, 'utf8');
  if (html.includes('data-lang-pairs')) continue;
  const m = html.match(/<body data-slug="([^"]*)"/);
  if (!m) continue;
  const ruSlug = m[1];
  const enSlug = ruToEn.get(ruSlug);
  stats.ru++;
  if (enSlug) { stats.ruPaired++; html = html.replace('</head>', headLinks(ruSlug, enSlug) + '</head>'); }
  const href = enSlug ? enHref(enSlug) : EN_BASE + '/';
  const title = enSlug ? 'English version' : 'English (home page)';
  html = appendToToolbar(html, `<a class="lang-switch" href="${esc(href)}" hreflang="en" lang="en" title="${title}" aria-label="${title}" data-router-ignore data-lang-pairs>EN</a>`);
  fs.writeFileSync(f, html, 'utf8');
}

// карта «английский путь прода → русский слаг» — для ссылок EN-страниц на непереведённое
// Неразрешённую вики-ссылку Quartz кладёт в корень по одному имени (/social-systems),
// поэтому вторая карта — по последнему сегменту, если он единственный в русском дереве.
// Значения карт — готовые русские адреса (href от корня). Страницы-синонимы (alias stubs, meta refresh)
// ведут на свою цель: «Ошибки рассуждения» → каталог ошибок.
const ruByEnPath = new Map(), ruByEnLast = new Map();
const unq = s => s.replace(/['’]/g, '');
function addTarget(enP, href) {
  const p = unq(norm(enP));
  if (!ruByEnPath.has(p)) ruByEnPath.set(p, href);
  const last = p.split('/').pop();
  if (last) ruByEnLast.set(last, ruByEnLast.has(last) && ruByEnLast.get(last) !== href ? null : href);
}
if (SLUG_MAP) {
  const files = walk(RU, n => n.endsWith('.html'), p => p === enDirAbs);
  for (const f of files) {
    const html = fs.readFileSync(f, 'utf8');
    const m = html.match(/<body data-slug="([^"]*)"/);
    if (m && !m[1].startsWith('tags')) addTarget(enPath(m[1]), ruHref(m[1]));
  }
  for (const f of files) {
    const html = fs.readFileSync(f, 'utf8');
    if (/<body data-slug=/.test(html)) continue;
    const r = html.match(/http-equiv="refresh"[^>]*?content="\d+;\s*url=([^"]*)"/);
    if (!r) continue;
    const stub = path.relative(RU, f).split(path.sep).join('/').replace(/\.html$/, '');
    const dest = path.posix.normalize(path.posix.join(path.posix.dirname('/' + stub), decodeURIComponent(r[1])));
    addTarget(enPath(stub), dest);
  }
}
const ruForTarget = t => { const n = unq(norm(t)); return ruByEnPath.get(n) || (n.includes('/') ? null : ruByEnLast.get(n)) || null; };
// Английские страницы по последнему сегменту: чистые плагины CI кладут ссылку на папку в корень
// (/logic вместо /library/branches/logic/) — такую ссылку чиним внутри английского дерева, а не уводим на русский.
const enByLast = new Map();
for (const s of enMeta.keys()) {
  const n = norm(s), last = n.split('/').pop();
  if (last) enByLast.set(last, enByLast.has(last) && enByLast.get(last) !== s ? null : s);
}
function existsInEn(rel) {
  const r = rel.replace(/\/$/, '');
  return fs.existsSync(path.join(EN, r + '.html')) || fs.existsSync(path.join(EN, r, 'index.html')) || (r === '' && fs.existsSync(path.join(EN, 'index.html')));
}

// EN-сборка
for (const f of walk(EN, n => n.endsWith('.html'))) {
  let html = fs.readFileSync(f, 'utf8');
  if (html.includes('data-lang-pairs')) continue;
  const m = html.match(/<body data-slug="([^"]*)"/);
  if (!m) continue;
  const enSlug = m[1];
  const ruSlug = enToRu.get(enSlug);
  stats.en++;
  if (ruSlug) { stats.enPaired++; html = html.replace('</head>', headLinks(ruSlug, enSlug) + '</head>'); }
  const href = ruSlug ? ruHref(ruSlug) : '/';
  const title = ruSlug ? 'Русская версия' : 'Русская версия (главная)';
  html = appendToToolbar(html, `<a class="lang-switch" href="${esc(href)}" hreflang="ru" lang="ru" title="${title}" aria-label="${title}" data-router-ignore data-lang-pairs>RU</a>`);
  const meta = enMeta.get(enSlug);
  if (meta && meta.status === 'draft') {
    const line = `<p class="translation-draft" data-lang-pairs>Translation draft, ${fmtDate(meta.translated)}</p>`;
    const before = html;
    html = html.replace(/(<article\b[^>]*>)/, `$1${line}`);
    if (html !== before) stats.drafts++; else console.log(`WARNING: no <article> for the draft line: ${enSlug}`);
  }
  // ссылки на непереведённые страницы → русские
  const pageDir = path.posix.dirname('/' + enSlug);
  // любой <a> с классом internal (порядок атрибутов любой: у карточек главной class стоит раньше href)
  html = html.replace(/<a\b([^>]*)>/g, (all, attrs) => {
    const cm = attrs.match(/\bclass="([^"]*)"/), hm = attrs.match(/\bhref="([^"]*)"/);
    if (!cm || !hm || !/\binternal\b/.test(cm[1]) || /\blang-switch\b/.test(cm[1])) return all;
    const href = hm[1];
    if (/^[a-z]+:/i.test(href) || href.startsWith('#') || href.startsWith('/')) return all;
    const [p] = href.split('#');
    let decoded;
    try { decoded = decodeURIComponent(p); } catch (e) { return all; }
    const target = path.posix.normalize(path.posix.join(pageDir, decoded)).replace(/^\/+/, '');
    if (existsInEn(target)) return all;
    const nt = norm(target);
    const enHit = !nt.includes('/') && enByLast.get(nt);
    if (enHit) {
      stats.linksFixedEn = (stats.linksFixedEn || 0) + 1;
      return `<a${attrs.replace(/\bhref="[^"]*"/, `href="${esc(enHref(enHit))}"`).replace(/\bdata-slug="[^"]*"/, `data-slug="${esc(enHit)}"`)}>`;
    }
    const ru = ruForTarget(target);
    if (!ru) { stats.linksUnresolved.add(target); return all; }
    stats.linksToRu++;
    // data-slug снимаем: он указывал бы в английское дерево (поповеры и SPA ходят по нему)
    const a2 = attrs.replace(/\bhref="[^"]*"/, `href="${esc(ru)}"`).replace(/\bclass="([^"]*)"/, 'class="$1 lang-ru"')
      .replace(/\s*\bdata-slug="[^"]*"/, '');
    return `<a${a2} lang="ru" hreflang="ru" data-router-ignore>`;
  });
  fs.writeFileSync(f, html, 'utf8');
}

console.log(`lang-pairs: RU pages ${stats.ru} (with translation ${stats.ruPaired}); EN pages ${stats.en} (paired ${stats.enPaired}); drafts marked ${stats.drafts}; EN links to RU ${stats.linksToRu}; EN root links fixed ${stats.linksFixedEn || 0}`);
if (stats.linksUnresolved.size) console.log(`WARNING: ${stats.linksUnresolved.size} EN link target(s) unresolved: ${[...stats.linksUnresolved].slice(0, 15).join(', ')}`);
const missingPairs = [...ruToEn.keys()].filter(s => !fs.existsSync(path.join(RU, slugToUrl(s) === '' ? 'index.html' : (s.endsWith('/index') ? path.join(slugToUrl(s), 'index.html') : s + '.html'))));
if (missingPairs.length) console.log(`WARNING: translationOf points to RU page(s) not in the build: ${missingPairs.join(', ')}`);
