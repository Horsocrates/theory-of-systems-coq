// Шаг 8 Части X, места 11 и 12: страница «Формализация», таблица «Цена результатов».
//   (а) строка о лемме Диксона: цена «исключённое третье» -> «нет» (доказана конструктивно 13.11);
//   (б) новая строка после строки о теореме Шрёдера — Бернштейна: та же теорема из исключённого третьего и
//       единственного свидетеля, взятых посылками.
// Вносится точной правкой ОТДЕЛЬНО в страницу сайта и в её копию в репозитории (копии различаются одним
// посторонним словом, файл целиком не копируется).
// Запуск: node apply-step-08-formalizaciya.cjs [--dry]
const fs = require('fs');
const dry = process.argv.includes('--dry');
const FILES = [
  'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/Формализация.md',
  'C:/Users/abary/OneDrive/Desktop/theory-of-systems-coq/site/quartz/content/Библиотека/Формализация.md',
];
const DICK_OLD = '| Лемма Диксона для пар | `dickson_pair` (HigmanLemma.v) | исключённое третье (стандартная библиотека) |';
const DICK_NEW = '| Лемма Диксона для пар | `dickson_pair` (HigmanLemma.v) | нет |';
const SB_PREFIX = '| Теорема Шрёдера — Бернштейна (Кантора — Бернштейна); антисимметрия мощностей | `Schroeder_Bernstein` (SchroederBernstein_ERR.v);';
const SB_ROW = '| Та же теорема из исключённого третьего и извлечения единственного свидетеля, взятых посылками | `Schroeder_Bernstein_definite` (SchroederBernstein_ERR.v); `cardinal_antisym_definite` (CardinalityWithoutChoice.v) | нет: оба принципа взяты посылками |';
for (const p of FILES) {
  const raw = fs.readFileSync(p, 'utf8');
  const eol = raw.includes('\r\n') ? '\r\n' : '\n';
  const lines = raw.split(eol);
  const d = lines.map((l, i) => (l === DICK_OLD ? i : -1)).filter((i) => i >= 0);
  if (d.length === 1) lines[d[0]] = DICK_NEW;
  else if (!lines.includes(DICK_NEW)) throw new Error(p + ': строка о лемме Диксона найдена ' + d.length + ' раз(а)');
  if (!lines.includes(SB_ROW)) {
    const s = lines.map((l, i) => (l.startsWith(SB_PREFIX) ? i : -1)).filter((i) => i >= 0);
    if (s.length !== 1) throw new Error(p + ': строка о Шрёдере — Бернштейне найдена ' + s.length + ' раз(а)');
    lines.splice(s[0] + 1, 0, SB_ROW);
  }
  if (!dry) fs.writeFileSync(p, lines.join(eol));
  console.log((dry ? 'проверка: ' : 'внесено: ') + p);
}
