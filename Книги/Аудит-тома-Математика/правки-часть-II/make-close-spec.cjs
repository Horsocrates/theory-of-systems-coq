// Собирает описание правок закрывающего шага Части II (глава II.5: слова «четыре пути — один ряд» и поправка
// формулировки в сноске 2): 3 правки. «Было» берётся с живой страницы.
// Запуск: node make-close-spec.cjs  -> закрытие-глава-II5.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL = 'Направления/Математика/Том Математика/02 Натуральные числа/05 Структурный путь число как позиция в системе.md';
const page = fs.readFileSync(LIVE + REL, 'utf8').replace(/\r/g, '').split('\n');
function old(first, last, max) {
  const hits = page.filter((l) => l.startsWith(first)).length;
  const i = page.findIndex((l) => l.startsWith(first));
  if (i < 0 || hits !== 1) throw new Error('начало не найдено однозначно (' + hits + '): ' + first);
  let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
  if (j >= page.length || j - i > (max || 20)) throw new Error('конец не найден: ' + last);
  return page.slice(i, j + 1);
}
function inline(prefix, a, b) {
  const o = old(prefix, prefix);
  if (o[0].split(a).length !== 2) throw new Error('фрагмент в строке не найден однозначно: ' + a.slice(0, 60));
  return { old: o, neu: [o[0].replace(a, () => b)] };
}
const BS = String.fromCharCode(92);
const GE = '$n ' + BS + 'ge 1$';
const edits = [];

// 1. «В чём четыре пути совпали»: формальная сторона совпадения
edits.push({ old: old('разные деривации привели к *тождественному* ряду: к одному и тому', 'же $1, 2, 3, …$.'),
  neu: ['разные деривации привели к *тождественному* ряду: к одному и тому',
        'же $1, 2, 3, …$. Формальную сторону этого совпадения несёт файл',
        '`FourPathsOneSeries.v`: начала четырёх путей суть $1$, шаги — `S`',
        '(`four_bases_are_one`, `four_steps_are_S`); на каждом из четырёх путей',
        'достижимы в точности числа ' + GE + ' (`four_ranges_coincide`); и пути',
        'связаны напрямую — счёт списка совершённых различений равен глубине',
        'его уровня, длине его двоичной записи и номеру его позиции',
        '(`four_paths_one_series`), а ещё один акт различения сдвигает все',
        'четыре разом (`one_more_act_moves_all_four`).'] });
// 2. синтез: что проверено машинно, а что остаётся доводом
edits.push({ old: old('довод деривации, а не единая машинно проверенная цепочка теорем:', 'структурной неизбежности $ℕ$.'),
  neu: ['довод деривации, а не единая машинно проверенная цепочка теорем:',
        'формальные якоря отдельных шагов разобраны в соответствующих главах и',
        'их сопроводительных замечаниях, а здесь сведён воедино *довод* о',
        'структурной неизбежности $ℕ$. Машинно проверено другое и меньшее — что',
        'четыре записи пути сходятся в одном ряде (теорема',
        '`four_paths_one_series`, файл `FourPathsOneSeries.v`). Независимости',
        'четырёх дериваций и неизбежности ряда она не доказывает: все четыре',
        'меры принимают значения в готовом типе `nat`.'] });
// 3. сноска 2: точная формулировка примера
edits.push(inline('[^2]: Эта синхронизация внесена (файл `StructuralPath.v`):',
  'занята одна пятая позиция, её номер $6$',
  'занята одна позиция с техническим индексом $5$, её номер $6$'));

const out = ['@@FILE ' + REL];
for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'закрытие-глава-II5.txt'), out.join('\n') + '\n');
console.log('закрытие-глава-II5.txt: правок ' + edits.length);
