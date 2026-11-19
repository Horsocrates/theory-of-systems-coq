// Собирает описание правок шага 6 Части VII («Сжатие и восстановление для Уолша»; места 5.1, 5.2, 5.3, 5.5)
// в двух вариантах — по развилке о счёте операций быстрого преобразования:
//   шаг-06-глава-VII5-вариант-1.txt — 8 правок: пять общих и три о счёте операций (со сноской 4);
//   шаг-06-глава-VII5-вариант-2.txt — 5 правок: только общие, слова страницы о стоимости не меняются.
// Формализация — src/process/ProcessWalshReconstruction.v и src/process/ProcessFastWalshCost.v.
// «Было» берётся с живой страницы. Запуск: node make-step-06-spec.cjs
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/07 Гармонический анализ/';
const REL5 = DIR + '05 Сжатие, быстрое преобразование, свёртка.md';
const BS = String.fromCharCode(92);
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
  return { old, inline, whole };
}

const { old, inline, whole } = loader(REL5);
const COST = ', `ProcessFastWalshCost.v` (10)';

// ---------------------------------------------------------------- общие правки (оба варианта)
const base = (withCost) => {
  const e = [];
  // 1. оговорка о шкале: где стоит масштаб N
  e.push({ old: old(L('для сырого спектра Уолша $(Hf)_i$ та же формула читается с масштабом $N$, ибо $§sum_i'), L('(Hf)_i^2 = N§norm{f}^2$ (Планшерель, Глава 7.2).')),
    neu: [L('для сырого спектра Уолша $(Hf)_i$ та же формула читается с масштабом $N$, ибо $§sum_i'),
          L('(Hf)_i^2 = N§norm{f}^2$ (Планшерель, Глава 7.2). Точнее: если $f_K$ — сигнал, восстановленный'),
          L('по первым $K$ сырым коэффициентам (обратным шагом $H/N$ от спектра, в котором коэффициенты'),
          L('с номерами $i§ge K$ заменены нулями), то $N§norm{f-f_K}^2=§sum_{K§le i<N}(Hf)_i^2$.'),
          'Нормированная шкала у Уолша рациональна при чётном $k$, и тогда формула верна в ней дословно.'] });
  // 2. сноска 1: число и новые файлы
  e.push(inline('[^1]: Опорные файлы (каталог `src/process/`): `ProcessFourierCompression.v`',
    '`ProcessWalshCompaction.v` (1), `ProcessFastWalsh.v` (2), `ProcessWalshConvolutionGeneral.v` (7); все',
    '`ProcessWalshCompaction.v` (2), `ProcessFastWalsh.v` (2), `ProcessWalshConvolutionGeneral.v` (7), `ProcessWalshReconstruction.v` (16)' + (withCost ? COST : '') + '; все'));
  // 3. сноска 2: ошибка восстановления
  e.push(whole('[^2]: В `ProcessFourierCompression.v`:',
    L('[^2]: В `ProcessFourierCompression.v`: `captured`$(c,K)=§sum_{i<K}c_i^2$; `truncation_error_eq` даёт баланс `captured`$(c,N)=$`captured`$(c,K)+$хвост для любой последовательности $c$; `captured_mono` — монотонность по $K$. Что хвост есть ошибка восстановления, доказано в `ProcessWalshReconstruction.v`: `walsh_rec` — сигнал $f_K$, восстановленный по первым $K$ сырым коэффициентам (он же частичная сумма разложения по функциям Уолша, `walsh_rec_partial_sum`); `walsh_compression_error` — $N§norm{f-f_K}^2=§sum_{K§le i<N}(Hf)_i^2$; `walsh_tail_eq` — эта сумма равна $N§norm{f}^2-$`captured`$(Hf,K)$ (равенство, по Планшерелю; `walsh_captured_le_energy` — оценка захваченной энергии сверху); `walsh_compression_error_mono` — ошибка не возрастает по $K$. В нормированной шкале: для полной ортонормированной системы — `fourier_error_is_tail_b` (Глава 7.4); для Уолша при рациональном $s$ с $s^2=N$ — `walsh_normalized_error_is_tail`, при $N=4^j$ — `walsh_4j_error_is_tail`. 0 аксиом.')));
  // 4. сноска 3: восстановление без потерь
  e.push(whole('[^3]: `walsh_compaction` в `ProcessWalshCompaction.v`:',
    L('[^3]: `walsh_bandlimited_lossless` в `ProcessWalshReconstruction.v`: если $(Hf)_i=0$ при $K§le i<N$, то $f_K(m)=f(m)$ при всех $m<N$; обратное — `walsh_lossless_iff`: восстановление точно тогда и только тогда, когда отброшенные коэффициенты равны нулю. Равенство энергий — `walsh_compaction` в `ProcessWalshCompaction.v`: при $c_i=0$ для $K§le i<N$ выполнено `captured`$(c,N)=$`captured`$(c,K)$ — хвост нулевой. 0 аксиом. Точное рациональное сжатие полосно-ограниченного сигнала.')));
  // 5. сноска 5: обратный шаг свёртки
  e.push(inline('[^5]: `walsh_convolution` в `ProcessWalshConvolutionGeneral.v`:',
    'доказанную блочной рекурсией Сильвестра). 0 аксиом.',
    L('доказанную блочной рекурсией Сильвестра). Обратный шаг — `walsh_convolution_inverse` в `ProcessWalshReconstruction.v`: $N§,(f§ast g)=H§bigl((Hf)§cdot(Hg)§bigr)$; то же через быструю бабочку — `convolution_via_fwht`. 0 аксиом.')));
  return e;
};

// ---------------------------------------------------------------- правки о счёте операций (только вариант 1)
const cost = () => {
  const e = [];
  // 6. чего глава не утверждает
  e.push({ old: old('Чего глава *не* утверждает. Сложность', 'и матричного преобразований, а не оценка стоимости.'),
    neu: [L('Чего глава *не* утверждает. Сложность $O(N§log N)$ сама по себе — операционное'),
          'свойство (счёт шагов), а не равенственное тождество; доказано *равенство* быстрого',
          'и матричного преобразований, а счёт шагов — для одной записи алгоритма: бабочка на',
          L('списке делает ровно $k§cdot2^k$ сложений и вычитаний. Оценка стоимости как класса —'),
          'асимптотика, оптимальность, сравнение с матричным счётом — остаётся вне доказанного. *Оптимальное* $K$-членное'] });
  // 7. итог раздела о быстром преобразовании
  e.push({ old: old('шагов), читается поверх доказанного равенства, но не входит в равенственное ядро.*', 'шагов), читается поверх доказанного равенства, но не входит в равенственное ядро.*'),
    neu: ['шагов), читается поверх доказанного равенства, но не входит в равенственное ядро; для',
          L('бабочки на списке сам счёт доказан: ровно $k§cdot2^k$ сложений и вычитаний.*')] });
  // 8. сноска 4: счёт шагов
  e.push(inline('[^4]: `fwht_correct` в `ProcessFastWalsh.v`:',
    '«Быстрый $=$ матричный» — алгоритм как процесс, равный преобразованию.',
    L('«Быстрый $=$ матричный» — алгоритм как процесс, равный преобразованию. Счёт шагов — в `ProcessFastWalshCost.v` (10 утверждений, 0 аксиом): `fwht_c` — бабочка на списке из $2^k$ рациональных чисел, возвращающая результат вместе с числом выполненных сложений и вычитаний; это число равно $k§cdot2^k$ (`fwht_c_ops`), значения совпадают с `fwht` (`fwht_c_correct`) и с матричным преобразованием (`fwht_c_cost_and_value`); пример $N=8$, 24 операции — `fwht_c_8`. Операции со списками и стоимость рациональной арифметики не считаются; оптимальность и сравнение с матричным счётом не утверждаются.')));
  return e;
};

const write = (name, edits) => {
  const out = ['@@FILE ' + REL5];
  for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
  fs.writeFileSync(path.join(__dirname, name), out.join('\n') + '\n');
  console.log(name + ': правок ' + edits.length);
};
write('шаг-06-глава-VII5-вариант-1.txt', [...base(true), ...cost()]);
write('шаг-06-глава-VII5-вариант-2.txt', base(false));
