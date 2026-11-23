// Собирает описание правок шага 2 Части IX («Перенос на всём процессе»; место 4.1): глава IX.4 и одно место
// главы IX.1.
// Формализация — src/process/ProcessTransportProcess.v, src/process/ProcessBurgersStep.v.
// «Было» берётся с живой страницы. Запуск: node make-step-02-spec.cjs [--no-burgers] [--keep-shape]
//   --no-burgers   вопрос 1, вариант 2: шаг нелинейной схемы на странице IX.4 не упоминается
//                  (стр. 34–35 и новая сноска 10 не вносятся)
//   --keep-shape   вопрос 2, вариант 2: IX.1, стр. 171–173 («без изменения формы… лишь сдвигается») не трогается
// Итог: шаг-02-главы-IX4-и-IX1.txt. L() превращает «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/09 Уравнения в частных производных/';
const REL1 = DIR + '01 Решение как процесс на пространственно-временной сетке.md';
const REL4 = DIR + '04 Перенос и нелинейность.md';
const BS = String.fromCharCode(92);
const L = (s) => s.split('¤').join(BS);   // «¤» — обратная косая черта
const NO_BURGERS = process.argv.includes('--no-burgers');
const KEEP_SHAPE = process.argv.includes('--keep-shape');

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
  const whole = (prefix, neu) => ({ old: old(prefix, prefix), neu: Array.isArray(neu) ? neu : [neu] });
  return { old, inline, whole };
}
const append = (a, tail) => [a, a + tail];   // пара (фрагмент, фрагмент с добавлением) для inline

const FN10 = L('[^10]: По эту сторону границы доказаны свойства одного шага консервативной схемы против потока для уравнения Бюргерса (`burgers_step`, `ProcessBurgersStep.v`): он есть шаг переноса с местным числом Куранта, зависящим от решения (`burgers_step_local_courant`); сохраняет массу (`burgers_mass`); удерживает неотрицательный профиль в его боксе, пока $¤lambda¤cdot¤max u¤le1$, где $¤lambda=¤Delta t/¤Delta x$ (`burgers_step_box`). На одном примере наклон спадающего участка растёт с $1/4$ до $5/16$ (`burgers_steepens_concrete`); линейный шаг разностей соседних узлов не увеличивает (`transport_no_steepening`). Ударные волны, слабые решения и поведение на многих шагах не формализованы. 0 аксиом.');

// ---------------------------------------------------------------- глава IX.4
const e4 = [];
{
  const { old, inline } = loader(REL4);

  // 1. вопрос 1 (стр. 34–35): что глава не делает
  if (!NO_BURGERS) e4.push({ old: old('Чего глава *не* делает: она не формализует *нелинейный* перенос', 'Бюргерса), ударные волны и слабые (энтропийные) решения.'),
    neu: ['Чего глава *не* делает: она не формализует ударные волны и слабые (энтропийные) решения',
          '*нелинейного* переноса (уравнения Бюргерса); о нелинейной схеме доказаны лишь свойства',
          'одного шага. Разрывное решение есть'] });

  // 2. вопрос 1 (стр. 146): сноска о шаге нелинейной схемы
  if (!NO_BURGERS) e4.push(inline('перенос, ударные волны и энтропийные решения — граница формализации',
    'граница формализации этой части.', 'граница формализации этой части.[^10]'));

  // 3. сноска 1: новый опорный файл
  e4.push(inline('[^1]:', ...append('0 аксиом (`Print Assumptions`: «closed under the global context»).',
    ' Законы на всём процессе — `ProcessTransportProcess.v` (масса, неотрицательность и бокс на любом числе шагов, точность условия Куранта, сдвиг на $n$ узлов, баланс суммы квадратов; 40 утверждений, 0 аксиом).')));

  // 4. сноска 2: условие точное
  e4.push(inline('[^2]:', ...append('циклический предшественник `ppred`.',
    L(' Что условие точное — `transport_nonneg_iff_cfl` (`ProcessTransportProcess.v`): при $N¤ge2$ неотрицательность для всякого неотрицательного профиля равносильна $0¤le¤nu¤le1$; вне условия значения знакопеременного профиля на сетке с чётным числом узлов превосходят любую границу (`transport_unstable_outside_cfl`). 0 аксиом.'))));

  // 5. сноска 3: крайние случаи и численная диффузия
  e4.push(inline('[^3]:', ...append('предельно допустимое по CFL движение за шаг.',
    L(' При $¤nu=0$ профиль стоит (`transport_step_zero`). За $n$ шагов при $¤nu=1$ профиль сдвигается на $n$ узлов (`transport_iter_shift`), а на периодической сетке за $N$ шагов возвращается на место (`transport_full_cycle`). Численная диффузия записана точным балансом: за шаг сумма квадратов убывает на $¤nu(1-¤nu)$, умноженное на сумму квадратов разностей соседних значений (`transport_step_energy`); при $¤nu=1$ она сохраняется. Все — `ProcessTransportProcess.v`, 0 аксиом.'))));

  // 6. место 4.1 (сноска 4): масса на всём процессе
  e4.push(inline('[^4]:', ...append(L('и не зависит от $¤nu$. 0 аксиом.'),
    ' На всём процессе — `transport_iter_mass` (`ProcessTransportProcess.v`): сумма сохраняется при любом числе шагов.')));

  // 7. место 4.1 (сноска 5): неотрицательность на всём процессе
  e4.push(inline('[^5]:', ...append('из неотрицательности следует неотрицательность.',
    ' На всём процессе — `transport_iter_nonneg`; то же для профиля, заданного только на узлах сетки, — `transport_iter_nonneg_grid` (`ProcessTransportProcess.v`).')));

  // 8. сноска 6: бокс на узлах сетки; сравнение и устойчивость
  e4.push(inline('[^6]:', ...append('как и в тепле.',
    ' На узлах сетки — `transport_iter_box_grid`. Следствия на всём процессе: принцип сравнения (`transport_iter_mono`) и устойчивость по начальным данным (`transport_iter_stable`); сумма модулей за шаг не растёт (`transport_step_l1`). Все — `ProcessTransportProcess.v`.')));

  // 9. сноска 7: все узлы после полушага
  e4.push(inline('[^7]:', ...append('Точная рациональная арифметика.',
    ' Все четыре узла после полушага — $(5/2, 4, 3/2, 0)$ (`p_prof_half_step`, `ProcessTransportProcess.v`).')));

  // 10. сноска 8: все узлы после полного шага
  e4.push(inline('[^8]:', ...append('`transport_step 1 4 p_prof 1 == 5`.',
    ' Все четыре узла — $(0, 5, 3, 0)$ (`p_prof_full_step`); четыре полных шага возвращают профиль на место (`p_prof_full_cycle`).')));

  // 11. вопрос 1: новая сноска 10
  if (!NO_BURGERS) { const o = old('[^9]:', '[^9]:'); e4.push({ old: o, neu: [o[0], FN10] }); }
}

// ---------------------------------------------------------------- глава IX.1
const e1 = [];
{
  const { old } = loader(REL1);
  // 12. вопрос 2 (стр. 171–173): перенос в триптихе
  if (!KEEP_SHAPE) e1.push({ old: old('Пространственный оператор — первая производная; процесс *движет* профиль без', 'лишь сдвигается.'),
    neu: ['Пространственный оператор — первая производная; процесс *движет* профиль — при числе',
          L('Куранта $¤nu=1$ без изменения формы, при меньшем слегка размывая его. Роль оператора —'),
          '*сохранение*: полная масса не меняется.'] });
}

const out = []; let n = 0;
out.push('@@FILE ' + REL4); for (const e of e4) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
if (e1.length) { out.push('@@FILE ' + REL1); for (const e of e1) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; } }
fs.writeFileSync(path.join(__dirname, 'шаг-02-главы-IX4-и-IX1.txt'), out.join('\n') + '\n');
console.log('шаг-02-главы-IX4-и-IX1.txt: правок ' + n + ' (IX.4 — ' + e4.length + ', IX.1 — ' + e1.length + ')' + (NO_BURGERS ? ' [без шага Бюргерса]' : '') + (KEEP_SHAPE ? ' [стр. 171–173 главы IX.1 оставлены]' : ''));
