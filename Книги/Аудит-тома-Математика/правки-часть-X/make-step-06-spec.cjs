// Собирает описание правок шага 6 Части X (глава X.5, строки 5–12 таблицы): семь мест в главе X.5
// и четыре места в главах I.6, IV.1, X.6 (параметр eval_program стал переменной раздела).
// Страница «Формализация» правится отдельным скриптом apply-step-06-formalizaciya.cjs (две её копии
// различаются одним посторонним словом, поэтому apply-edits для неё не годится).
// Запуск: node make-step-06-spec.cjs  -> шаг-06-глава-X5.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
function pageOf(rel) {
  const page = fs.readFileSync(LIVE + rel, 'utf8').replace(/\r/g, '').split('\n');
  function old(first, last) {
    const hits = page.filter((l) => l.startsWith(first)).length;
    const i = page.findIndex((l) => l.startsWith(first));
    if (i < 0 || hits !== 1) throw new Error('начало не найдено однозначно (' + hits + '): ' + first);
    let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
    if (j >= page.length || j - i > 20) throw new Error('конец не найден: ' + last);
    return page.slice(i, j + 1);
  }
  function inline(prefix, a, b) {
    const o = old(prefix, prefix);
    if (o[0].split(a).length !== 2) throw new Error('фрагмент в строке не найден однозначно: ' + a);
    return { old: o, neu: [o[0].replace(a, () => b)] };
  }
  return { old, inline };
}
const M = 'Направления/Математика/Том Математика/';
const X5 = M + '10 Теория множеств без аксиомы выбора/05 Ординалы как процессы; башня сильных аксиом (ATR_0, ^1_1) и её снятие.md';
const X6 = M + '10 Теория множеств без аксиомы выбора/06 Синтез Части X что доказуемо без выбора, и карта границ.md';
const I6 = M + '01 Перво-различие и законы логики/06 Аксиоматический минимум и механизм статуса.md';
const IV1 = M + '04 Процессные действительные числа/01 P4 бесконечность как процесс.md';
const blocks = [];
function file(rel, edits) { blocks.push('@@FILE ' + rel); for (const e of edits) blocks.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); return edits.length; }
let total = 0;

{ // ---------------- глава X.5
  const a = pageOf(X5);
  const e = [
    // 1. строка 6 таблицы: квантор по кодам — выбор области
    { old: a.old('завершённой несчётной тотальности *всех* функций) к P4-развитию не привлекается — это', 'ровно тот завершённый объект, который P4 не актуализирует.'),
      neu: ['завершённой несчётной тотальности *всех* функций) к P4-развитию не привлекается — это',
            'ровно тот завершённый объект, который P4 не актуализирует. Что это выбор области, а не',
            'равносильная замена, доказано: никакая таблица кодов не содержит всех функций —',
            'диагональная функция в неё не входит, — и квантор по кодам строго слабее квантора по',
            'функциям (`no_table_covers_all_functions`, `codes_reading_is_weaker`).'] },
    // 2. строки 6 и 12: «Что даёт»
    { old: a.old('переинтерпретированы (`P4_eliminates_ATR0`, `P4_eliminates_Pi11`,', '`P4_eliminates_Infinity`, `P4ProhibitsImpredicative`;'),
      neu: ['переинтерпретированы (`P4_eliminates_ATR0`, `P4_eliminates_Pi11`,',
            '`P4_eliminates_Infinity`, `russell_requires_completed_totality`; всё — 0 аксиом).'] },
    // 3. строка 10: сноска 1
    a.inline('[^1]: `Ordinal.v`: `Ord` (с `OZero`/`OSucc`/`OLim`)',
      'Арифметика ($+,\\cdot,{}^\\wedge$) — структурной рекурсией, но часть её лемм опирается на функциональную экстенсиональность.',
      'Арифметика ($+,\\cdot,{}^\\wedge$) — структурной рекурсией; два тождества, проходящие через предел (`ord_add_zero_l`, `ord_mul_one_r`), записаны с точностью до постадийного равенства `ord_eq`, и функциональная экстенсиональность не привлекается: все 24 леммы файла закрыты.'),
  ];
  // 4–7. сноски 3, 4, 5, 6
  e.push({ old: a.old('[^3]: `P4_Eliminates_ATR.v`: `CB_transfinite`', '[^3]: `P4_Eliminates_ATR.v`: `CB_transfinite`'),
    neu: ['[^3]: `P4_Eliminates_ATR.v`: `iterate_pred` — итерация произвольного оператора на подмножествах $ℕ$ вдоль нотации как `Fixpoint` на `Ord`; `P4_eliminates_ATR0` фиксирует zero/successor-уравнения рекурсии (limit-стадия задана самим `Fixpoint`). Пример `CB_transfinite` взят для модельного оператора `CB_step` (точка остаётся, если у неё есть сосед на расстоянии 1) — дискретного подобия производной Кантора–Бендиксона; его итерация стоит на месте уже после первого шага (`CB_transfinite_succ_stage`, `CB_transfinite_omega`). Настоящая производная итерируется вдоль нотаций в `CantorBendixsonFull.v`: `CB_ord`, на конечных нотациях совпадающая с `CB_iter`, на $\\omega$ — с `CB_omega` (`CB_ord_nat`, `CB_ord_omega`). 22 Qed, 0 аксиом (сверено `Print Assumptions`: Closed).'] });
  e.push({ old: a.old('[^4]: `P4_Eliminates_Pi11.v`: `Program := nat`', '[^4]: `P4_Eliminates_Pi11.v`: `Program := nat`'),
    neu: ['[^4]: `P4_Eliminates_Pi11.v`: `Program := nat`; `P4_forall_functions` — квантор по кодам; таблица кодов `eval_program` — переменная раздела без каких-либо свойств, так что все утверждения верны для любой таблицы. Итог — `P4_eliminates_Pi11`: квантор по кодам есть квантор по функциям, *заданным кодами*. Совпадение с квантором по всем функциям имеет место ровно при условии «всякая функция имеет код» (`pi11_hierarchy_collapse`), а оно не выполняется ни для какой таблицы (`no_table_covers_all_functions`). По `Print Assumptions` — 0 аксиом; одна лемма файла, `pi11_negation`, стоит на `classic`.'] });
  e.push({ old: a.old('[^5]: `P4_Eliminates_Infinity.v`: `converges`', '[^5]: `P4_Eliminates_Infinity.v`: `converges`'),
    neu: ['[^5]: `P4_Eliminates_Infinity.v`: итог — `P4_eliminates_Infinity`: правило индукции; никакая конечная стадия не исчерпывает натуральных чисел (`no_finite_stage_exhausts_nat`); за всяким числом есть большее. `converges` — сходимость последовательности натуральных чисел: это стабилизация, и предел единствен (`converges_iff_stabilizes`, `converges_unique`). 13 Qed, 0 аксиом. Ср. 10.4: потенциальная бесконечность с P4 совместима, завершённая — нет.'] });
  e.push({ old: a.old('[^6]: `P4ProhibitsImpredicative.v`: P1${}+{}$P4 исключают', '[^6]: `P4ProhibitsImpredicative.v`: P1${}+{}$P4 исключают'),
    neu: ['[^6]: `P4ProhibitsImpredicative.v`: собиратель расселова условия по области сам в эту область не входит (`russell_collector_escapes`); по каждой конечной стадии он существует и лежит вне стадии (`staged_russell_collector_exists`); область, у которой он есть, не завершена (`russell_needs_incomplete_range`). Что P4 исключает завершённую область — `completed_inf_contradicts_P4`, при условии `bridge` (Глава 10.4). 11 Qed, 0 аксиом.'] });
  total += file(X5, e);
}
{ // ---------------- глава X.6: строка таблицы о Π^1_1
  const a = pageOf(X6);
  total += file(X6, [
    a.inline('| вычислительный примитив | $\\Pi^1_1$-переинтерпретация',
      '| вычислительный примитив | $\\Pi^1_1$-переинтерпретация — 0 логич. аксиом, но при `eval_program` (`Parameter`) |',
      '| 0 аксиом, для любой таблицы кодов | $\\Pi^1_1$-переинтерпретация: `eval_program` — переменная раздела без свойств, не параметр |'),
  ]);
}
{ // ---------------- глава I.6: сноска 8
  const a = pageOf(I6);
  total += file(I6, [
    a.inline('[^8]: Файл `src/foundation/P4_Eliminates_Pi11.v`.',
      'а `eval_program` объявлен как `Parameter`; теорема `P4_eliminates_Pi11` устанавливает эквивалентность $P4$-определённой квантификации `P4_forall_functions` с квантификацией по `nat`.',
      'а таблица кодов `eval_program` — переменная раздела без каких-либо свойств; теорема `P4_eliminates_Pi11` устанавливает, что $P4$-определённая квантификация `P4_forall_functions` есть квантификация по функциям, заданным кодами.'),
  ]);
}
{ // ---------------- глава IV.1: два места о eval_program
  const a = pageOf(IV1);
  total += file(IV1, [
    { old: a.old('через параметр `eval_program` («запустить код $c$ на входе', '$n$»). При таком чтении квантор «по всем функциям» сводится к'),
      neu: ['через таблицу кодов `eval_program` («значение функции с кодом $c$ на входе',
            '$n$»). При таком чтении квантор «по всем функциям» сводится к'] },
    { old: a.old('функций с классом программ. И `eval_program` здесь — не', 'ненужности обходятся вовсе без подобных объявлений.'),
      neu: ['функций с классом программ. И `eval_program` здесь — не',
            'доказанное утверждение и не определённая функция, а',
            '*переменная раздела*: произвольная таблица, сопоставляющая коду',
            'функцию, без каких-либо свойств. Все утверждения файла верны для любой',
            'такой таблицы и допущений не имеют. Доказано и то, что ни одна таблица',
            'не содержит всех функций: диагональная функция в неё не входит',
            '(`no_table_covers_all_functions`).'] },
  ]);
}
fs.writeFileSync(path.join(__dirname, 'шаг-06-глава-X5.txt'), blocks.join('\n') + '\n');
console.log('описание собрано: правок ' + total);
