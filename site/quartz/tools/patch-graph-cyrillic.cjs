// Патч плагина graph: getFullSlugFromUrl читал window.location.pathname БЕЗ decodeURIComponent.
// На кириллических слагах браузер отдаёт percent-encoded путь, а ключи contentIndex — в кириллице,
// поэтому текущая страница не находилась в данных: локальный граф вырождался в ОДИН узел,
// подписанный сырым «%D0%B1%D0%B8...», без связей. Патч декодирует путь.
// Идемпотентен. Прогонять после `npx quartz plugin install/update` — обновление стирает патчи dist.
const fs = require("fs");
const path = require("path");

const root = path.resolve(__dirname, "..");
const files = [
  ".quartz/plugins/graph/dist/index.js",
  ".quartz/plugins/graph/dist/components/index.js",
];

const from = 'function we(){let u=window.location.pathname;return u.endsWith("/")';
const to =
  'function we(){let u=window.location.pathname;try{u=decodeURIComponent(u)}catch(e){}return u.endsWith("/")';

let changed = 0;
let failed = 0;

for (const rel of files) {
  const f = path.join(root, rel);
  if (!fs.existsSync(f)) {
    console.log("ОТСУТСТВУЕТ :: " + rel);
    failed++;
    continue;
  }
  const s = fs.readFileSync(f, "utf8");
  if (s.includes(to)) {
    console.log("уже пропатчен :: " + rel);
    continue;
  }
  const n = s.split(from).length - 1;
  if (n !== 1) {
    console.log("ПРОПУСК (совпадений: " + n + ", ожидалось 1) :: " + rel);
    failed++;
    continue;
  }
  fs.writeFileSync(f, s.split(from).join(to), "utf8");
  console.log("пропатчен :: " + rel);
  changed++;
}

console.log("итог: изменено " + changed + ", проблем " + failed);
process.exit(failed > 0 ? 1 : 0);
