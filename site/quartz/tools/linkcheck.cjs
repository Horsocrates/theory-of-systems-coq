// tools/linkcheck.js — проверка целостности собранного сайта (public/) и исходников (content/).
// Запускается deploy.ps1 после сборки; выход с кодом 1 при любой битой ссылке.
// Проверяет:
//   1) public/: каждый внутренний href/src разрешается в существующий файл ТОЧНО ПО РЕГИСТРУ
//      (готовность к case-sensitive nginx) — включая data-slug викиссылок;
//   2) content/: каждая [[викиссылка]] находит страницу (по имени, алиасу или полному пути),
//      якоря [[Страница#Секция]] находят заголовок в целевом файле; коллизии алиасов.
const fs = require("fs");
const path = require("path");

const ROOT = path.resolve(__dirname, "..");
const PUB = path.join(ROOT, "public");
const CONTENT = path.join(ROOT, "content");

function walk(dir, out = []) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) walk(p, out);
    else out.push(p);
  }
  return out;
}

let failures = 0;
function fail(msg) { failures++; console.log("  " + msg); }

// ---------- 1) public/: exact-case href/src + data-slug ----------
if (fs.existsSync(PUB)) {
  const pubFiles = walk(PUB).map(p => path.relative(PUB, p).split(path.sep).join("/"));
  const pubSet = new Set(pubFiles);
  const htmlFiles = pubFiles.filter(f => f.endsWith(".html"));
  const missing = new Map();
  let total = 0;
  for (const hf of htmlFiles) {
    const html = fs.readFileSync(path.join(PUB, hf), "utf8");
    const dir = path.posix.dirname(hf);
    const re = /(?:href|src)="([^"]+)"/g;
    let m;
    while ((m = re.exec(html))) {
      let url = m[1];
      if (/^(https?:|mailto:|data:|#|javascript:)/.test(url)) continue;
      url = url.split("#")[0].split("?")[0];
      if (!url) continue;
      try { url = decodeURIComponent(url); } catch {}
      let resolved = url.startsWith("/")
        ? url.slice(1)
        : path.posix.normalize(path.posix.join(dir === "." ? "" : dir, url));
      resolved = resolved.replace(/\/\.$/, "").replace(/\/$/, "");
      if (resolved.startsWith("../")) continue;
      if (resolved === "" || resolved === "." || resolved === "./") resolved = "index.html";
      total++;
      const cand = [resolved, resolved + ".html", resolved + "/index.html"];
      if (!cand.some(c => pubSet.has(c))) {
        if (!missing.has(resolved)) missing.set(resolved, hf);
      }
    }
    // data-slug мёртвых викиссылок (резолвер упал в корень)
    const reSlug = /<a[^>]*data-slug="([^"]+)"[^>]*>/g;
    while ((m = reSlug.exec(html))) {
      const slug = m[1];
      if (pubSet.has(slug + ".html") || pubSet.has(slug + "/index.html")) continue;
      if (!missing.has("data-slug:" + slug)) missing.set("data-slug:" + slug, hf);
    }
  }
  console.log(`public/: ${htmlFiles.length} html, ${total} внутренних ссылок`);
  for (const [t, src] of missing) fail(`МЁРТВАЯ ССЫЛКА: ${t}  (например из ${src})`);
} else {
  console.log("public/ отсутствует — пропускаю (сначала npx quartz build)");
}

// ---------- 2) content/: викиссылки, якоря, алиасы ----------
const mdFiles = walk(CONTENT).filter(f => f.endsWith(".md"));
const nameToFile = new Map(), aliasToFile = new Map(), fullPathToFile = new Map();
for (const f of mdFiles) {
  const rel = path.relative(CONTENT, f).split(path.sep).join("/");
  const base = path.basename(rel, ".md");
  nameToFile.set(base.toLowerCase(), rel);
  fullPathToFile.set(rel.replace(/\.md$/, "").toLowerCase(), rel);
  if (base === "index") {
    const folder = path.posix.dirname(rel).split("/").pop();
    if (folder && folder !== ".") nameToFile.set(folder.toLowerCase(), rel);
  }
  const fm = fs.readFileSync(f, "utf8").match(/^---\r?\n([\s\S]*?)\r?\n---/);
  if (fm) {
    const addAlias = (a) => {
      const k = a.toLowerCase();
      if (aliasToFile.has(k) && aliasToFile.get(k) !== rel)
        fail(`КОЛЛИЗИЯ АЛИАСОВ: "${a}" у ${rel} и ${aliasToFile.get(k)}`);
      aliasToFile.set(k, rel);
    };
    const inline = fm[1].match(/^aliases:\s*\[([^\]]*)\]/m);
    if (inline) inline[1].split(",").map(s => s.trim().replace(/^["']|["']$/g, "")).filter(Boolean)
      .forEach(addAlias);
    // блочный формат:  aliases:\n  - Имя
    const block = fm[1].match(/^aliases:\s*\r?\n((?:[ \t]+-[ \t]+.*(?:\r?\n|$))+)/m);
    if (block) [...block[1].matchAll(/-[ \t]+(.+)/g)]
      .map(x => x[1].trim().replace(/^["']|["']$/g, "")).filter(Boolean)
      .forEach(addAlias);
  }
}
let badLinks = 0, badAnchors = 0;
for (const f of mdFiles) {
  const rel = path.relative(CONTENT, f).split(path.sep).join("/");
  const body = fs.readFileSync(f, "utf8")
    .replace(/```[\s\S]*?```/g, "").replace(/`[^`\n]*`/g, "");
  const re = /\[\[([^\]|#]+)(#[^\]|]+)?(\|[^\]]*)?\]\]/g;
  let m;
  while ((m = re.exec(body))) {
    const target = m[1].trim().replace(/\\/g, "");
    const anchor = m[2] ? m[2].slice(1).trim() : null;
    const key = target.toLowerCase();
    const hit = nameToFile.get(key) || aliasToFile.get(key) || fullPathToFile.get(key);
    if (!hit) { badLinks++; fail(`БИТАЯ ВИКИССЫЛКА: [[${target}]] в ${rel}`); continue; }
    if (anchor) {
      const headings = [...fs.readFileSync(path.join(CONTENT, hit), "utf8")
        .matchAll(/^#{1,6}\s+(.*)$/gm)].map(h => h[1].trim().toLowerCase());
      if (!headings.some(h => h.includes(anchor.toLowerCase()))) {
        badAnchors++; fail(`БИТЫЙ ЯКОРЬ: [[${target}#${anchor}]] в ${rel}`);
      }
    }
  }
}
console.log(`content/: ${mdFiles.length} md; битых викиссылок: ${badLinks}, битых якорей: ${badAnchors}`);

if (failures > 0) {
  console.log(`\nLINKCHECK FAILED: ${failures} проблем(ы)`);
  process.exit(1);
}
console.log("\nLINKCHECK OK");
