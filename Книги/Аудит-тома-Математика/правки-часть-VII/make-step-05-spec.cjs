// Собирает описание правок шага 5 Части VII («Сходимость ряда Фурье по стандартной системе»; место 4.2):
// 7 правок главы VII.4. Формализация — src/process/ProcessFourierConvergenceStd.v.
// «Было» берётся с живой страницы. Запуск: node make-step-05-spec.cjs -> шаг-05-глава-VII4.txt
// Внимание: строки с настоящим знаком параграфа через L() не пропускать (в этом файле знак параграфа — PAR).
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/07 Гармонический анализ/';
const REL4 = DIR + '04 Сходимость рядов Фурье в L2.md';
const BS = String.fromCharCode(92);
const PAR = String.fromCharCode(167);
const L = (s) => s.split('§').join(BS);   // «§» в строках, идущих через L(), — обратная косая черта

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
  const after = (prefix, add) => { const o = old(prefix, prefix); return { old: o, neu: [o[0], add] }; };
  return { old, inline, whole, after };
}

const e4 = [];
{
  const { old, inline, whole, after } = loader(REL4);
  // 1. уровни строгости: второй
  e4.push({ old: old(L('*Второй* — процессное чтение: ряд Фурье как процесс $K§mapsto P_K$ с убывающей'), 'ошибкой, L<sup>2</sup>-полнота по построению (Рисс–Фишер Части VI).'),
    neu: [L('*Второй* — процессное чтение: ряд Фурье как процесс $K§mapsto P_K$ с убывающей'),
          'ошибкой; для стандартной системы доказано и большее — остаток стремится к нулю при всех',
          L('усечениях $N$ сразу тогда и только тогда, когда процесс энергии $§sum_{i<n}f_i^2$ есть'),
          'процесс Коши, и тогда частичные суммы L<sup>2</sup>-Коши, а предел, построенный по',
          'Риссу–Фишеру Части VI, есть сама $f$.'] });
  // 2. бюджет энергии: что доказано для стандартной системы
  e4.push(whole('одного Бесселя.',
    L('одного Бесселя. Для стандартной системы оно доказано в процессной форме: остаток $§norm{f-P_K}^2$ меньше любого $§varepsilon$ при всех усечениях $N$ сразу, начиная с некоторого $K$, тогда и только тогда, когда процесс энергии $n§mapsto§sum_{i<n}f_i^2$ есть процесс Коши.[^9]')));
  // 3. Рисс — Фишер: фиксированное усечение; недостающие звенья для стандартной системы
  e4.push({ old: old('построен, его предел читается как L<sup>2</sup>-процесс (пространство', 'именно $f$.'),
    neu: ['построен, его предел читается как L<sup>2</sup>-процесс (пространство',
          'L<sup>2</sup>-процессов Коши-полно по построению — при каждом фиксированном усечении $N$).[^2] Но сама',
          'Коши-сходимость ряда Фурье к $f$ из одного Бесселя *не* следует: она требует полноты',
          'системы и сходимости процесса энергии. Рисс–Фишер гарантирует *носитель* предела, а не то, что предел есть',
          'именно $f$. Для стандартной системы оба недостающих звена доказаны: при процессе энергии',
          'Коши частичные суммы образуют L<sup>2</sup>-Коши-процесс со стадией, не зависящей от $N$,',
          'и координаты построенного предела совпадают с координатами $f$.'] });
  // 4. граница: завершённый ряд
  e4.push(whole('пределе, а это уже предельное утверждение, а не конечное тождество.',
    'пределе, а это уже предельное утверждение, а не конечное тождество. Для стандартной системы оно доказано в процессной форме (' + PAR + ' «Энергетический бюджет, не гарантия предела»); для произвольной — остаётся границей.'));
  // 5. сноска 1: новый файл
  e4.push(inline('[^1]: Опорный файл — `ProcessOrthonormalFourier.v`',
    'Процессное чтение предела — `ProcessL2RieszFischer.v`.',
    'Процессное чтение предела — `ProcessL2RieszFischer.v` и `ProcessFourierConvergenceStd.v` (26 утверждений, 0 аксиом).'));
  // 6. сноска 2: Рисс — Фишер
  e4.push(whole('[^2]: Процессное прочтение Рисса–Фишера',
    '[^2]: Процессное прочтение Рисса–Фишера — `l2_riesz_fischer` в `ProcessL2RieszFischer.v` (Часть VI), при фиксированном усечении $N$: предел строится покоординатно как процесс (`l2_limit`), и заключение теоремы есть её посылка, развёрнутая по этому определению (`rf_conclusion_is_hypothesis`), — «полно по построению» в точном смысле; содержательная трёхчастная форма — `riesz_fischer_process_form` (`ProcessL2Orthonormal.v`). Это *мост* к носителю предела, см. ' + PAR + ' «Граница: завершённый ряд, поточечная сходимость, Гиббс». Для частичных сумм стандартной системы посылка моста доказана — `std_partial_sums_L2CauchySq`, а предел опознан — `std_limit_is_f` (`ProcessFourierConvergenceStd.v`).'));
  // 7. новая сноска 9
  e4.push(after('[^8]: Шапки:',
    L('[^9]: `ProcessFourierConvergenceStd.v` (26 утверждений, 0 аксиом). Для стандартной системы ошибка на $N$ координатах есть кусок энергии: $§norm{f-P_K}^2=§sum_{K§le i<N}f_i^2$ при $K§le N$ (`std_error_is_tail`) и нуль при $N§le K$ (`std_error_zero_beyond`). Отсюда `std_fourier_l2_convergence_iff`: процесс энергии есть процесс Коши $§Leftrightarrow$ для всякого $§varepsilon>0$ есть $M$, после которого ошибка меньше $§varepsilon$ при всех $K§ge M$ и всех $N$. Тогда частичные суммы L<sup>2</sup>-Коши со стадией, не зависящей от $N$ (`std_partial_sums_cauchy`), посылка Рисса–Фишера выполнена (`std_partial_sums_L2CauchySq`, `std_fourier_riesz_fischer`), а координаты предела суть координаты $f$ (`std_limit_is_f`). Условие выполнимо: конечный носитель (`finite_support_energy_cauchy`) и $f_i=2^{-i}$ (`geometric_energy_cauchy`, `geometric_fourier_converges`). Что процесс энергии всякой $f$ с ограниченной энергией есть процесс Коши, не утверждается.')));
}

const out = ['@@FILE ' + REL4]; let n = 0;
for (const e of e4) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-05-глава-VII4.txt'), out.join('\n') + '\n');
console.log('шаг-05-глава-VII4.txt: правок ' + n);
