// Шаг 4 Части V, место 13 (слово автора 12.11: «Да — вносим 12 мест и строку 13»): новая строка в таблице цены
// страницы «Формализация» — после строки о теореме Гейне — Бореля. Вносится точной вставкой ОТДЕЛЬНО в страницу
// сайта и в её копию в репозитории (копии различаются одним чужим словом в строке 245, файл целиком не копируется).
// Запуск: node apply-step-04-formalizaciya.cjs [--dry]
const fs = require('fs');
const dry = process.argv.includes('--dry');
const FILES = [
  'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/Формализация.md',
  'C:/Users/abary/OneDrive/Desktop/theory-of-systems-coq/site/quartz/content/Библиотека/Формализация.md',
];
const ANCHOR = '| Гейне — Борель при числе Лебега | `Heine_Borel` (HeineBorel_ERR.v) | нет |';
const ROW = '| Полнота пространства классов: сближающаяся последовательность точек имеет предел-точку | `regular_class_complete`; `class_complete_L4` (RealPointComplete.v) | нет — для регулярных представителей; извлечение свидетеля — для произвольных |';
for (const p of FILES) {
  const raw = fs.readFileSync(p, 'utf8');
  const eol = raw.includes('\r\n') ? '\r\n' : '\n';
  const lines = raw.split(eol);
  const hits = lines.map((l, i) => (l === ANCHOR ? i : -1)).filter((i) => i >= 0);
  if (hits.length !== 1) throw new Error(p + ': строка-якорь найдена ' + hits.length + ' раз(а)');
  if (lines.includes(ROW)) throw new Error(p + ': строка уже внесена');
  lines.splice(hits[0] + 1, 0, ROW);
  if (!dry) fs.writeFileSync(p, lines.join(eol));
  console.log((dry ? 'проверка: ' : 'внесено: ') + p + ' — после строки ' + (hits[0] + 1));
}
