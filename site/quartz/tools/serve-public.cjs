// serve-public.cjs — статическая раздача собранного public\ (русская сборка + английская в public\en\).
// Dev-сервер Quartz (deploy.ps1 -Serve) пересобирает только русский сайт и затирает public\en\,
// поэтому превью двух языков — так:  .\deploy.ps1 ; .\build-en.ps1 ; node tools\serve-public.cjs public 8082
// Правила адресов — как у nginx прода: $uri, $uri.html, $uri/index.html.
const http = require('http');
const fs = require('fs');
const path = require('path');
const root = path.resolve(process.argv[2] || 'public');
const port = parseInt(process.argv[3] || '8082', 10);
const types = { '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg',
  '.woff2': 'font/woff2', '.xml': 'application/xml; charset=utf-8', '.txt': 'text/plain; charset=utf-8', '.ico': 'image/x-icon' };
function pick(p) {
  for (const c of [p, p + '.html', path.join(p, 'index.html')]) {
    try { if (fs.statSync(c).isFile()) return c; } catch (e) { /* next */ }
  }
  return null;
}
http.createServer((req, res) => {
  let u;
  try { u = decodeURIComponent(req.url.split('?')[0].split('#')[0]); } catch (e) { res.writeHead(400); return res.end(); }
  const p = path.normalize(path.join(root, u));
  if (!p.startsWith(root)) { res.writeHead(403); return res.end(); }
  const f = pick(p);
  if (!f) {
    const nf = pick(path.join(root, u.startsWith('/en/') ? 'en/404' : '404'));
    res.writeHead(404, { 'Content-Type': types['.html'] });
    return nf ? fs.createReadStream(nf).pipe(res) : res.end('not found');
  }
  res.writeHead(200, { 'Content-Type': types[path.extname(f)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
  fs.createReadStream(f).pipe(res);
}).listen(port, '127.0.0.1', () => console.log(`serving ${root} on http://localhost:${port}`));
