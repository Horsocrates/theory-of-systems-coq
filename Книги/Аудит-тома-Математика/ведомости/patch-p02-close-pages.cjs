// Часть II, закрывающий шаг, страницы (2026-11-14, слово автора «Делай»): 3 правки главы II.5 внесены —
// формальная сторона «четырёх путей», что проверено машинно, поправка формулировки в сноске 2.
// Формализация — новый src/foundation/FourPathsOneSeries.v.
// Запуск: node patch-p02-close-pages.cjs  (затем relocate + merge по part02-ch05). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'внесено 14.11 (Часть II, закрывающий шаг, слово автора)';
const F = 'src/foundation/';
const FP = F + 'FourPathsOneSeries.v';
const SP = F + 'StructuralPath.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const GE = '$n ' + BS + 'ge 1$';
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

const p = path.join(__dirname, 'part02-ch05.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
const add = (rec) => {
  if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
};

const C1 = 'Формальную сторону этого совпадения несёт файл `FourPathsOneSeries.v`: начала четырёх путей суть $1$, шаги — `S` (`four_bases_are_one`, `four_steps_are_S`);';
add({ theorem: 'four_bases_are_one', file: FP, claim: C1,
  note: DONE + '. four_bases_are_one : forall D, length [D] = 1 ' + AND + ' level_depth L1 = 1 ' + AND + ' bit_length one_bit = 1 ' + AND + ' pos_number 0 = 1. ' + CL + '.' });
add({ theorem: 'four_steps_are_S', file: FP, claim: C1,
  note: 'four_steps_are_S — четыре леммы шага (add_distinction_increments, level_depth_LS, add_bit_increments_length, pos_number_step) в одном утверждении. ' + CL + '.' });
add({ theorem: 'four_ranges_coincide', file: FP,
  claim: 'на каждом из четырёх путей достижимы в точности числа ' + GE + ' (`four_ranges_coincide`);',
  note: 'four_ranges_coincide : для всякого n каждое из четырёх условий (счёт от единицы; глубина уровня; длина непустой записи; номер позиции) равносильно 1 <= n. ' + CL + '.' });
add({ theorem: 'four_paths_one_series', file: FP,
  claim: 'и пути связаны напрямую — счёт списка совершённых различений равен глубине его уровня, длине его двоичной записи и номеру его позиции (`four_paths_one_series`)',
  note: 'four_paths_one_series : presented Ds -> binary_record Ds bs -> level_depth (level_of_count Ds) = length Ds ' + AND + ' bit_length bs = length Ds ' + AND + ' pos_number (position_of_level (level_of_count Ds)) = length Ds. ' + CL + '.' });
add({ theorem: 'one_more_act_moves_all_four', file: FP,
  claim: 'а ещё один акт различения сдвигает все четыре разом (`one_more_act_moves_all_four`).',
  note: 'one_more_act_moves_all_four : счёт +1, уровень — LS, запись — add_bit s bs (s — сторона, положенная актом), позиция — S. ' + CL + '.' });
add({ theorem: 'four_paths_one_series', file: FP,
  claim: 'Машинно проверено другое и меньшее — что четыре записи пути сходятся в одном ряде (теорема `four_paths_one_series`, файл `FourPathsOneSeries.v`).',
  note: 'Верно; статус назван на странице точно.' });
add({ theorem: 'four_paths_one_series', file: FP,
  claim: 'Независимости четырёх дериваций и неизбежности ряда она не доказывает: все четыре меры принимают значения в готовом типе `nat`.',
  note: 'Верно: length, level_depth, bit_length, pos_number принимают значения в nat стандартной библиотеки; шапка файла говорит то же («NOT claimed»).' });
// сноска 2: формулировка примера приведена к исходнику
for (const r of j.records) {
  if (r.theorem === 'sparse_first_is_5' && !/с техническим индексом/.test(r.claim || '')) {
    r.claim = 'без нормализации номер может быть иным (пример `sparse_first_is_5`: занята одна позиция с техническим индексом $5$, её номер $6$).';
    r.note = 'поправлено 14.11 (моя неточность шага 6: было «одна пятая позиция»). sparse_first_is_5 : first_occupied_position sparse_ss 5 ' + AND + ' pos_number 5 = 6 (' + SP + '). ' + CL + '.';
    n++;
  }
}
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part02-ch05.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
