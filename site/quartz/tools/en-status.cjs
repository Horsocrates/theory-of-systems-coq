// en-status.cjs -- which English pages lag behind their Russian source.
//
//   node tools/en-status.cjs
//
// Every page in content-en/ carries in its frontmatter:
//   translationOf: "<path of the Russian page inside content/>"
//   sourceBlob:    <git blob hash of that Russian file at translation time>
// The Russian file is hashed again (same algorithm as `git hash-object`);
// a different hash means the source changed after the translation was made.

const fs = require("fs")
const path = require("path")
const crypto = require("crypto")

const root = path.join(__dirname, "..")
const enRoot = path.join(root, "content-en")
const ruRoot = path.join(root, "content")

function blobHash(buf) {
  const h = crypto.createHash("sha1")
  h.update(`blob ${buf.length}\0`)
  h.update(buf)
  return h.digest("hex")
}

function walk(dir, out) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name)
    if (entry.isDirectory()) walk(full, out)
    else if (entry.name.endsWith(".md")) out.push(full)
  }
  return out
}

function field(frontmatter, name) {
  const m = frontmatter.match(new RegExp(`^${name}:\\s*(.+)$`, "m"))
  return m ? m[1].trim().replace(/^["']|["']$/g, "") : null
}

if (!fs.existsSync(enRoot)) {
  console.log("content-en/ not found: no English pages yet")
  process.exit(0)
}

const rows = []
for (const file of walk(enRoot, [])) {
  const text = fs.readFileSync(file, "utf8")
  const fm = text.startsWith("---") ? text.slice(3, text.indexOf("\n---", 3)) : ""
  const source = field(fm, "translationOf")
  const stored = field(fm, "sourceBlob")
  const status = field(fm, "status") || "-"
  const rel = path.relative(enRoot, file).split(path.sep).join("/")
  let state
  if (!source || !stored) state = "NO METADATA"
  else {
    const ruFile = path.join(ruRoot, source)
    if (!fs.existsSync(ruFile)) state = "SOURCE MISSING"
    else state = blobHash(fs.readFileSync(ruFile)) === stored ? "up to date" : "STALE"
  }
  rows.push({ rel, state, status, source: source || "-" })
}

rows.sort((a, b) => a.rel.localeCompare(b.rel))
const width = Math.max(...rows.map((r) => r.rel.length), 10)
for (const r of rows) {
  console.log(`${r.state.padEnd(14)} ${r.status.padEnd(9)} ${r.rel.padEnd(width)}  <- ${r.source}`)
}
const stale = rows.filter((r) => r.state !== "up to date").length
console.log(`\n${rows.length} English page(s); ${stale} need attention`)
process.exit(stale ? 1 : 0)
