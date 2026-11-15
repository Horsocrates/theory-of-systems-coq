// Собирает описание правок шага 3 Части VI («ступенчатый интеграл и L¹»;
// места 3.1–3.4, 3.6, 5.3, 5.5): 7 правок — глава VI.3 (6), глава VI.5 (1).
// Формализация — src/process/ProcessL1Integrable.v. «Было» берётся с живых страниц.
// Запуск: node make-step-03-spec.cjs  -> шаг-03-главы-VI3-VI5.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/06 Меры и интегрирование/';
const REL3 = DIR + '03 Измеримые функции и интеграл Лебега.md';
const REL5 = DIR + '05 L^1 и L^2 пространства как процессы, полнота как конструируемость.md';
const BS = String.fromCharCode(92);
const NORM = '$' + BS + '|f_n-g_n' + BS + '|_1<' + BS + 'varepsilon$';

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

const e3 = []; const e5 = [];
{
  const { old, inline, whole } = loader(REL3);
  // 1. место 3.2: «совпадение Лебега с Риманом на ступенчатом уровне»
  e3.push({ old: old('ступенчатом уровне доказано точно (вложение `step_to_l1`); для более широкого',
                     'ступенчатом уровне доказано точно (вложение `step_to_l1`); для более широкого'),
    neu: ['ступенчатом уровне доказано точно: процесс Римана ступенчатой функции сходится к её',
          'ступенчатому интегралу (`step_riemann_equiv`), а значит, называет ту же точку, что и',
          'L¹-интеграл её вложения (`lebesgue_step_agrees`); для более широкого'] });
  // 2. место 3.6: сноска 1, число
  e3.push(inline('[^1]: Тип ступенчатой функции и `step_integral`',
    '20 доказанных утверждений', '17 доказанных утверждений'));
  // 3. место 3.1: сноска 2 — однородность и монотонность для списков ступеней
  e3.push(whole('[^2]: `integral_app` (аддитивность по конкатенации), `integral_scale` (однородность),',
    '[^2]: `integral_app` (аддитивность по конкатенации) в `StepIntegral.v`; там же для одной ступени — `integral_scale`, `integral_monotone_step`, `step_integral_nonneg`. Для списков ступеней (файл `ProcessL1Integrable.v`, каталог `src/process/`): однородность — `step_fun_integral_scale`; монотонность — `step_integral_monotone`: если значение одной ступенчатой функции в каждой точке не больше значения другой, то и интеграл не больше, какими бы разбиениями они ни были записаны (доказано сравнением сумм на одной достаточно мелкой сетке). Следствие — интеграл зависит только от функции, а не от списка ступеней, которым она записана (`step_integral_depends_on_function`).'));
  // 4. место 3.3: сноска 4 — тип интегрируемых функций
  e3.push(whole('[^4]: Тип `L1Process` и норма `step_fun_norm` в `L1Space.v`',
    '[^4]: Тип `L1On` (файл `ProcessL1Integrable.v`, каталог `src/process/`, 0 аксиом): последовательность ступенчатых функций на отрезке, у которой разность двух далёких стадий — как функция точки — записывается списком ступеней сколь угодно малой нормы (`l1_close`; норма — `step_fun_norm` из `StepIntegral.v`). Такая близость не зависит от того, какими разбиениями записаны стадии. Прежний тип `L1Process` (`L1Space.v`, каталог `src/analysis/`, 16 доказанных утверждений, 0 `Admitted`, 0 аксиом) вычитает ступени по месту в списке; сказанное в этом разделе верно для него, когда все стадии записаны на общем разбиении (`l1_integral_cauchy_aligned`), а без этого условия — нет (`l1_process_integral_unbounded`).'));
  // 5. место 3.3: сноска 5 — интеграл как процесс Коши
  e3.push(whole('[^5]: `l1_integral_approx` — интеграл L¹-функции как приближающий процесс;',
    '[^5]: `on_integral` — интеграл интегрируемой функции как процесс интегралов её стадий; `l1_on_integral_is_Cauchy` — этот процесс есть процесс Коши; `l1_on_equiv_integral` — у эквивалентных функций он называет одну точку. `step_to_l1_on` — вложение ступенчатой функции; `series_l1` — ряд ступеней с суммируемыми нормами есть интегрируемая функция; пример — `staircase`: бесконечно много ступеней, сгущающихся к нулю; она не эквивалентна ни одной из своих стадий (`staircase_beyond_every_stage`). Все — в файле `ProcessL1Integrable.v`, 0 аксиом.'));
  // 6. место 3.4: сноска 7 — отношение эквивалентности
  e3.push(whole('[^7]: `l1_equiv` в `L1Space.v`:',
    '[^7]: `l1_on_equiv` в `ProcessL1Integrable.v`: $' + BS + 'forall' + BS + 'varepsilon>0' + BS + ' ' + BS + 'exists N' + BS + ' ' + BS + 'forall n' + BS + 'ge N:' + BS + ' ' + BS + '|f_n-g_n' + BS + '|_1<' + BS + 'varepsilon$. Доказано, что это отношение эквивалентности (`l1_on_equiv_equivalence`) и что оно сохраняет интеграл (`l1_on_equiv_integral`). Пример: функция, равная единице в одной точке и нулю в остальных, эквивалентна нулевой (`point_differs_but_equivalent`), а постоянная единица — нет (`one_not_equiv_zero`). Это L¹-смысл равенства почти всюду; полностью поточечное «различаются лишь на множестве меры нуль» — содержательное чтение поверх этого ядра.'));
}
{
  const { whole } = loader(REL5);
  // 7. места 5.3, 5.5: сноска 2
  e5.push(whole('[^2]: Файл `L1Space.v` (каталог `analysis/`, 25 Qed по шапке):',
    '[^2]: Файл `ProcessL1Integrable.v` (каталог `src/process/`, 83 доказанных утверждения, 0 аксиом): `L1On` (представители), `l1_close` (близость по интегральной норме), `on_integral`, `l1_on_equiv` ($' + BS + '|f-g' + BS + '|_1' + BS + 'to0$; что это отношение эквивалентности — `l1_on_equiv_equivalence`), `step_to_l1_on`. Прежний файл `L1Space.v` (каталог `src/analysis/`, 16 доказанных утверждений): тип `L1Process` — для стадий на общем разбиении. Разбор — Глава 6.3.'));
}

const out = []; let n = 0;
for (const [rel, edits] of [[REL3, e3], [REL5, e5]]) {
  out.push('@@FILE ' + rel);
  for (const e of edits) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-03-главы-VI3-VI5.txt'), out.join('\n') + '\n');
console.log('шаг-03-главы-VI3-VI5.txt: правок ' + n);
