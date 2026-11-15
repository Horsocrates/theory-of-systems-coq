// Собирает описание правок шага 2 Части VI («мера интервала как процесс; различимость»;
// места 1.1, 1.2, 1.5, 2.3, 2.4, 3.5): 9 правок — глава VI.1 (6), глава VI.2 (2), глава VI.3 (1).
// Формализация — src/process/ProcessMeasureIntervals.v. «Было» берётся с живых страниц.
// Запуск: node make-step-02-spec.cjs  -> шаг-02-главы-VI1-VI2-VI3.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/06 Меры и интегрирование/';
const REL1 = DIR + '01 Мера как процесс приписывания.md';
const REL2 = DIR + '02 Мера Лебега на процессном континууме.md';
const REL3 = DIR + '03 Измеримые функции и интеграл Лебега.md';
const BS = String.fromCharCode(92);
const SIGMA = '$' + BS + 'sigma$';

function loader(rel) {
  const page = fs.readFileSync(LIVE + rel, 'utf8').replace(/\r/g, '').split('\n');
  const old = (first, last, max) => {
    const hits = page.filter((l) => l.startsWith(first)).length;
    const i = page.findIndex((l) => l.startsWith(first));
    if (i < 0 || hits !== 1) throw new Error(rel + ': начало не найдено однозначно (' + hits + '): ' + first);
    let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
    if (j >= page.length || j - i > (max || 20)) throw new Error(rel + ': конец не найден: ' + last);
    return page.slice(i, j + 1);
  };
  const inline = (prefix, a, b) => {
    const o = old(prefix, prefix);
    if (o[0].split(a).length !== 2) throw new Error(rel + ': фрагмент в строке не найден однозначно: ' + a.slice(0, 60));
    return { old: o, neu: o[0].replace(a, () => b).split('\n') };
  };
  const whole = (prefix, neu) => ({ old: old(prefix, prefix), neu: [neu] });
  return { old, inline, whole };
}

const e1 = []; const e2 = []; const e3 = [];
{
  const { old, inline, whole } = loader(REL1);
  // 1. место 1.1: «мера как sup-процесс»
  e1.push({ old: old(SIGMA + '-аддитивности (мера как sup-процесс, сходимость частичных сумм): доказаны',
                     'именно эти процессные утверждения, при явно названной цене (L3). *Третий* —'),
    neu: [SIGMA + '-аддитивности (мера интервала как предел процесса приближений, сходимость',
          'частичных сумм): доказаны именно эти процессные утверждения — первое без аксиом,',
          'второе при явно названной цене (L3). *Третий* —'] });
  // 2. § «Измеримое есть различимое», формальный статус: общий предикат записан
  e1.push({ old: old('уже полностью построенная в этом файле теория.[^5]', 'уже полностью построенная в этом файле теория.[^5]'),
    neu: ['уже полностью построенная в этом файле теория.[^5] Сам предикат записан',
          'отдельно (`distinguishable`, файл `ProcessMeasureIntervals.v`): множество',
          'совпадает с конечным набором отрезков с точностью до покрытия сколь угодно',
          'малой суммарной длины; доказано, что различимы отрезок, рациональные точки',
          'отрезка и канторово множество.'] });
  // 3. § «Мера Лебега против объёма Жордана»: неизмеримость по Жордану — теорема
  e1.push(inline('оценки не сходятся — объём Жордана не определён.',
    'оценки не сходятся — объём Жордана не определён.',
    'оценки не сходятся — объём Жордана не определён (`segment_rationals_not_finitely_distinguishable`, файл `ProcessMeasureIntervals.v`).'));
  // 4. место 1.5: сноска 1, число
  e1.push(inline('[^1]: Опорные файлы — `LebesgueMeasure.v`',
    '20 доказанных утверждений', '22 доказанных утверждения'));
  // 5. сноска 7: цепочка примыкающих интервалов
  e1.push(inline('[^7]: Доказанная лемма `measure_additive` даёт случай двух примыкающих интервалов:',
    'Все — 0 аксиом.',
    'Все — 0 аксиом. Для цепочки из $n$ примыкающих интервалов аддитивность доказана отдельно — `measure_finite_additive_chain` (файл `ProcessMeasureIntervals.v`).'));
  // 6. место 1.2: сноска 8
  e1.push(whole('[^8]: В `ProcessMeasureTheory.v`: `measure_process` (процесс индикатора),',
    '[^8]: В `ProcessMeasureTheory.v`: `measure_process` (процесс индикатора), `q_measure_additive`, `q_measure_monotone`, а также внешние оценки и предикаты множества меры нуль. В файле `ProcessMeasureIntervals.v`: процесс меры интервала сходится к $d-c$, отступая от него на каждой стадии не более чем на один шаг сетки (`measure_process_rate`, `measure_process_converges`); различимость множества — `distinguishable` (множество совпадает с конечным набором отрезков с точностью до покрытия сколь угодно малой суммарной длины), её конечный уровень — `finitely_distinguishable` (множество зажато между внутренним и внешним конечными наборами отрезков).'));
}
{
  const { inline, whole } = loader(REL2);
  // 7. место 2.3: сноска 1 — растяжение и сдвиг в общем виде
  e2.push(inline('[^1]: `measure_translation`:',
    'Все — в `LebesgueMeasure.v`, 0 аксиом.',
    'Все — в `LebesgueMeasure.v`, 0 аксиом. Растяжение и сдвиг произвольного интервала — `measure_scaling_nonneg`: $' + BS + 'mu([ka,kb])=k' + BS + ',' + BS + 'mu([a,b])$ при $k' + BS + 'ge 0$, и `measure_shift_general`: $' + BS + 'mu([a+t,b+t])=' + BS + 'mu([a,b])$ (файл `ProcessMeasureIntervals.v`, 0 аксиом).'));
  // 8. место 2.4: сноска 2 — аддитивность цепочки и процесса
  e2.push(whole('[^2]: `measure_additive` в `LebesgueMeasure.v` (случай двух примыкающих интервалов);',
    '[^2]: `measure_additive` в `LebesgueMeasure.v` (случай двух примыкающих интервалов); цепочка из $n$ примыкающих интервалов — `measure_finite_additive_chain`. Процессный аналог — `measure_process_additive_equiv`: сумма процессов мер $[c,d]$ и $[d,e]$ называет ту же точку, что процесс меры $[c,e]$; на каждой стадии они расходятся не более чем на один шаг сетки — общая точка $d$ сосчитана дважды (`measure_process_additive_upto_point`). Обе теоремы — в файле `ProcessMeasureIntervals.v`, 0 аксиом.'));
}
{
  const { whole } = loader(REL3);
  // 9. место 3.5: сноска 6
  e3.push(whole('[^6]: Процессный предикат различимости функции на стадии $n$ — `measurable_at`',
    '[^6]: Для множеств различимость записана предикатом `distinguishable` (файл `ProcessMeasureIntervals.v`): множество совпадает с конечным набором отрезков — то есть его индикатор со ступенчатой функцией — с точностью до покрытия сколь угодно малой суммарной длины. Для функций ту же роль несёт интегрируемость (§ «Интегрируемая функция как предел ступенчатых»); отдельный тип «прообраз-измеримой функции» в текущем корпусе не строится и подаётся как классическое сравнение.'));
}

const out = []; let n = 0;
for (const [rel, edits] of [[REL1, e1], [REL2, e2], [REL3, e3]]) {
  out.push('@@FILE ' + rel);
  for (const e of edits) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-02-главы-VI1-VI2-VI3.txt'), out.join('\n') + '\n');
console.log('шаг-02-главы-VI1-VI2-VI3.txt: правок ' + n);
