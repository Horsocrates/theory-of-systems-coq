// Собирает описание правок шага 10 Части I (глава I.7 «Онтологическое ядро: сквозные мотивы», пять мест): 6 правок.
// «Было» берётся с живой страницы по началу первой и последней строки.
// Запуск: node make-step-10-spec.cjs  -> шаг-10-глава-I7.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL = 'Направления/Математика/Том Математика/01 Перво-различие и законы логики/07 Онтологическое ядро сквозные мотивы.md';
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
const edits = [];

// 1. место 1 (стр. 338–342): russell_paradox_blocked — об одном уровне
edits.push({ old: old('запрещено иерархией уровней: формально это разобрано в файле', 'отношения `level_lt`. Списочное и иерархическое объяснения —'),
  neu: ['запрещено иерархией уровней: формально это разобрано в файле',
        '`TheoryOfSystems_Core_ERR.v`, где теорема',
        '`russell_paradox_blocked` устанавливает для уровня `L2` невозможность',
        'критерия-свидетеля на собственном уровне через иррефлексивность',
        'отношения `level_lt`; для всякого уровня то же утверждает',
        '`criterion_label_never_own_level` (`TransfiniteInductionLevel.v`).',
        'Списочное и иерархическое объяснения —'] });
// 2. место 2 (стр. 384–388): теория множеств и списки
edits.push({ old: old('более первичным уровнем списков, а не фундамент под ним. В репозитории', 'а не как основание.'),
  neu: ['более первичным уровнем списков, а не фундамент под ним. В репозитории',
        'ToS это отражено частично. Сама схема записана теоремами: множество',
        'получается из списка двумя ступенями — мультимножество забывает порядок',
        'и только его, множество забывает ещё и кратность',
        '(`first_step_forgets_exactly_order`, `support_from_mult`,',
        '`second_step_well_defined`, файл `ListModes.v`). Слой же',
        'теоретико-множественных конструкций[^2] на эту схему пока не опирается:',
        'множества в нём заданы предикатами и типами, а списки служат рабочим',
        'материалом — позициями игр, словами, наборами поддеревьев.'] });
// 3. место 5 (стр. 681): имя файла
edits.push(inline('| операциональная делимость | `Level`, `System` $L$, `Criterion` в `Core_ERR.v`', 'в `Core_ERR.v`', 'в `TheoryOfSystems_Core_ERR.v`'));
// 4. место 4 (стр. 686–687): что проверено о записи Distinction
edits.push({ old: old('прямой формальный след: запись `Distinction` с её полями машинно', 'проверена. Операциональная делимость формализована как иерархия'),
  neu: ['прямой формальный след: запись `Distinction` с её полями задана в Rocq,',
        'и о ней доказано, что каждая сторона всякого различения есть в точности',
        'отрицание другой и что стороны различны (`sides_codetermined`,',
        '`sides_distinct`, без аксиом); канонический экземпляр `distinction_of`',
        'построен ценой аксиомы `classic`. Операциональная делимость формализована как иерархия'] });
// 5. место 3 (сноска 1): ConnectionClosesGap.v
edits.push(inline('[^1]: В репозитории эта линия имеет несколько формальных следов.',
  '`ConnectionClosesGap.v` собирает Barandes-style correspondence между distinction graph, doubly stochastic / unistochastic transitions и path-dependence.',
  '`ConnectionClosesGap.v` проверяет на примерах три звена Barandes-style correspondence и сводит проверки в одну теорему; само соответствие между distinction graph, doubly stochastic / unistochastic transitions и path-dependence приведено в нём таблицей в комментарии. Для графа из двух узлов цепочка проведена теоремами целиком (`GraphTransitionN2.v`): матрица графа, её преобразование Кэли, ортогональность, унистохастическая и потому дважды стохастическая матрица переходов — при любом весе связи (`cayley_2_is_cayley_transform`, `graph_transition_unistochastic`); и неделимость — переход за два шага не равен произведению переходов за один (`two_step_transition_indivisible`).'));
// 6. место 2 (сноска 2)
edits.push(inline('[^2]: Соответствующие построения — в каталоге `src/settheory/` репозитория',
  'репозитория `theory-of-systems-coq`.',
  'репозитория `theory-of-systems-coq`. Схема «список → мультимножество → множество» — в файле `src/settheory/ListModes.v`.'));

const out = ['@@FILE ' + REL];
for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'шаг-10-глава-I7.txt'), out.join('\n') + '\n');
console.log('описание собрано: правок ' + edits.length);
