// Собирает описание правок шага 4 Части VI («теоремы сходимости»; места 4.1–4.4, 1.3):
// 7 правок — глава VI.4 (5), глава VI.1 (2).
// Формализация — src/process/ProcessConvergenceTheorems.v. «Было» берётся с живых страниц.
// Запуск: node make-step-04-spec.cjs  -> шаг-04-главы-VI4-VI1.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/06 Меры и интегрирование/';
const REL4 = DIR + '04 Теоремы сходимости монотонная и мажорированная.md';
const REL1 = DIR + '01 Мера как процесс приписывания.md';
const BS = String.fromCharCode(92);
const DOM_OLD = '$' + BS + 'forall k x,' + BS + ' |f_k(x)|' + BS + 'le g(x)$';
const DOM_NEW = '$' + BS + 'forall k,' + BS + ' ' + BS + 'forall x' + BS + 'in[a,b]:' + BS + ' |f_k(x)|' + BS + 'le g(x)$';

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

const e4 = []; const e1 = [];
{
  const { old, inline, whole } = loader(REL4);
  // 1. место 4.3: где проходит граница — новый абзац после «…честно вынесенный наружу.»
  const last = 'конструктивно, и остаётся ровно один инфинитарный шаг, честно вынесенный наружу.';
  e4.push({ old: old(last, last), neu: [last, '',
    'Где именно проходит эта граница, проверено с двух сторон. На фиксированной сетке узлов',
    'границы нет: там стремление невязки к нулю равносильно поточечной сходимости в узлах и',
    'доказывается без мажоранты.[^8] Граница появляется при переходе к процессу интегралов —',
    'к пределу по сетке: там посылка о невязках уже не следует из поточечной сходимости и',
    'мажоранты. Пример: индикаторы первых $k$ точек нумерации рациональных чисел растут к',
    'единице в каждой рациональной точке и ограничены мажорантой $g' + BS + 'equiv 1$; интеграл',
    'каждого равен нулю, а интеграл предела — единице.[^9] И там же посылка снимается, если',
    'недостающее предъявлено как данные, подобно мажоранте: сходимость равномерна вне',
    'множества, на котором интеграл мажоранты сколь угодно мал, — тогда невязки стремятся к',
    'нулю, и сходимость интегралов доказана без аксиом.[^10]'] });
  // 2. места 4.1, 4.2: § «Лемма Фату на процессном уровне»
  e4.push({ old: old('Лемму Фату — что интеграл нижнего предела не превосходит нижнего предела',
                     'стадии $n$ величины определены и удовлетворяют нужным неравенствам.'),
    neu: ['Лемму Фату — что интеграл нижнего предела не превосходит нижнего предела',
          'интегралов — ToS удерживает на процессном уровне: на каждой стадии интеграл нижней',
          'огибающей конечного набора функций не превосходит нижней огибающей их интегралов; для',
          'неотрицательных функций нижняя огибающая последовательности интегралов неотрицательна,',
          'а при доминировании ограничена интегралом мажоранты.[^7] Это конечно-процессное ядро',
          'Фату: на каждой стадии $n$ величины определены и удовлетворяют нужным неравенствам.'] });
  // 3. место 4.4: сноска 3 — формула dominated
  e4.push(inline('[^3]: Предикат `dominated` в `ProcessFatou.v`:',
    DOM_OLD + ', где $g$ — параметр.', DOM_NEW + ', где $g$ и отрезок $[a,b]$ — параметры.'));
  // 4. место 4.3: сноска 6 — уровень сетки и уровень процесса интегралов
  e4.push(inline('[^6]: `process_dct` в `ProcessDCT.v` (0 аксиом):',
    'Пакет `process_dct_dominated` объединяет конверт и сжатие.',
    'Пакет `process_dct_dominated` объединяет конверт и сжатие. Это утверждения о сумме на фиксированной сетке узлов; для процесса интегралов (предел по сетке) те же три звена — `lebesgue_engine`, `lebesgue_envelope`, `process_dct_lebesgue` (файл `ProcessConvergenceTheorems.v`, 0 аксиом).'));
  // 5. места 4.1, 4.2: сноска 7 и новые сноски 8–10
  e4.push(whole('[^7]: `process_fatou_nonneg` и `process_fatou_bounded` в `ProcessFatou.v` (0 аксиом);', [
    '[^7]: Неравенство — `process_fatou_inf` (по хвосту последовательности — `process_fatou_tail`, на сетке узлов — `grid_fatou`); оценки через мажоранту-функцию — `process_fatou_bounded_g` (нижняя огибающая интегралов не больше интеграла $g$) и `dominated_integral_bound_g` (разность интегралов не больше интеграла $2g$). Все — в `ProcessConvergenceTheorems.v`, 0 аксиом. В `ProcessFatou.v` (0 аксиом): `process_fatou_nonneg`, а также `process_fatou_bounded` и `dominated_integral_bound` — оценки с постоянной $M$ на месте мажоранты-функции.',
    '[^8]: `grid_residual_from_pointwise`, `grid_pointwise_from_residual`, `grid_dct_pointwise` в `ProcessConvergenceTheorems.v` (0 аксиом).',
    '[^9]: `pointwise_dominated_not_enough` и `dct_fails_on_rational_grid` в `ProcessConvergenceTheorems.v` (0 аксиом). Точки, в которых заданы функции, — рациональные; последовательность к тому же возрастает, так что пример касается и монотонной сходимости в полном виде.',
    '[^10]: `almost_uniform_residual` и `dominated_almost_uniform_convergence` в `ProcessConvergenceTheorems.v` (0 аксиом); равномерная сходимость — частный случай (`uniform_convergence_integral`, `uniform_is_almost_uniform`). Классически переход от поточечной сходимости к равномерной вне множества малой меры даёт теорема Егорова — над завершённой мерой.']));
}
{
  const { inline, whole } = loader(REL1);
  // 6. место 4.4 (перекрытие): сноска 12 главы VI.1 — та же формула
  e1.push(inline('[^12]: В коде доминирование — предикат `dominated`,',
    DOM_OLD + '.', DOM_NEW + '.'));
  // 7. место 1.3: сноска 13
  e1.push(whole('[^13]: Редукция мажорированной сходимости — `process_dct` (`ProcessDCT.v`), 0 аксиом:',
    '[^13]: Редукция мажорированной сходимости — `process_dct` (`ProcessDCT.v`) на фиксированной сетке узлов и `process_dct_lebesgue` (`ProcessConvergenceTheorems.v`) для процесса интегралов, 0 аксиом: движок и «конверт»-мажоранта доказаны конструктивно, а сходимость невязок к нулю вынесена в явную гипотезу-вход. На фиксированной сетке эта гипотеза равносильна поточечной сходимости в узлах; для процесса интегралов она из поточечной сходимости и мажоранты не следует (`pointwise_dominated_not_enough`) и снимается, когда сходимость равномерна вне множества с малым интегралом мажоранты, — там мажоранта и несёт оценку (`dominated_almost_uniform_convergence`).'));
}

const out = []; let n = 0;
for (const [rel, edits] of [[REL4, e4], [REL1, e1]]) {
  out.push('@@FILE ' + rel);
  for (const e of edits) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-04-главы-VI4-VI1.txt'), out.join('\n') + '\n');
console.log('шаг-04-главы-VI4-VI1.txt: правок ' + n);
