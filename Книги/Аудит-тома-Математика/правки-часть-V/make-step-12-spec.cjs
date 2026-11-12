// Собирает описание правок шага 12 Части V (глава V.5, строки 2–11 таблицы): двенадцать мест.
// «Было» берётся со страницы дословно, «стало» — тексты, показанные автору 12.11.
// Запуск: node make-step-12-spec.cjs  -> шаг-12-глава-V5.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL = 'Направления/Математика/Том Математика/05 Топология и анализ процессов/05 Интеграл.md';
const page = fs.readFileSync(LIVE + REL, 'utf8').replace(/\r/g, '').split('\n');
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
const edits = [
  // 1. строка 2: три определения riemann_sum
  { old: old('(предохранитель C4). В репозитории есть *три разных*', 'остальным двум обратимся отдельно в § 5.7, всякий раз называя файл.'),
    neu: ['(предохранитель C4). В репозитории есть *три разных*',
          'определения с именем `riemann_sum`: это, основное, из',
          '`RiemannIntegration.v` (левая сумма по `walk_point`);',
          'демонстрационное в `ProcessAnalysis.v`; и ещё одно в',
          '`ProcessMCT.v` (сумма по произвольной последовательности узлов с',
          'общим весом). Кроме них есть сумма с близким именем',
          '`riemann_sum_01` на отрезке $[0,1]$ в `ProcessIntegration.v`.',
          'Определения различны; ниже под `riemann_sum` мы всегда понимаем',
          'первое, а к суммам из `ProcessAnalysis.v` и `ProcessIntegration.v`',
          'обратимся отдельно в § 5.7, всякий раз называя файл.'] },
  // 2. строка 7: отрезок у integral_constant
  { old: old('на отрезке есть $c$ (`integral_constant`); интеграл индикатора', 'на отрезке есть $c$ (`integral_constant`); интеграл индикатора'),
    neu: ['на отрезке $[0,1]$ есть $c$ (`integral_constant`); интеграл индикатора'] },
  // 3. строка 6: условие на шаг и леммы уровня процесса
  { old: old('`riemann_sum_abs_bound`: если $|f|\\le M$ в узлах, то', 'Подставив, получаем для конечной суммы процесса $\\texttt{RS}_n$:'),
    neu: ['`riemann_sum_abs_bound`: если $|f|\\le M$ в узлах и шаг',
          'неотрицателен, то $|\\texttt{riemann\\_sum} f a \\texttt{step} n|\\le M\\cdot',
          'n\\cdot\\texttt{step}$. Лемма `riemann_sum_global_bound`: при',
          '$\\mathrm{lo}\\le f\\le \\mathrm{hi}$ в узлах и неотрицательном шаге сумма',
          'из $n$ слагаемых зажата',
          'между $\\mathrm{lo}\\cdot n\\cdot\\texttt{step}$ и $\\mathrm{hi}\\cdot',
          'n\\cdot\\texttt{step}$. Это оценки произвольной конечной суммы с $n$',
          'подынтервалами. В интегральном процессе на уровне $n$ число',
          'подынтервалов равно $S n$ (то есть $n+1$), и нормировка такова:',
          '$(S n)\\cdot\\texttt{integral\\_step} a b n = b-a$ (`grid_width_eq`).',
          'Подставив, получаем для конечной суммы процесса $\\texttt{RS}_n$',
          '(леммы `integral_process_abs_bound` и',
          '`integral_process_global_bound`):'] },
  // 4. строка 6: «точны и безусловны»
  { old: old('Предохранитель C1: оценки на конечной сумме точны и безусловны;', 'Предохранитель C1: оценки на конечной сумме точны и безусловны;'),
    neu: ['Предохранитель C1: оценки на конечной сумме точны и не требуют',
          'сходимости процесса (нужен только неотрицательный шаг; в процессе он',
          'положителен при $a<b$);'] },
  // 5. строка 5: что именно лейбницево-точно
  { old: old('сетки — и это совпадение *лейбницево-точное*, потому что узлы', '$a+ks$ (та же honest-деталь, что разбиралась в главе о производной).'),
    neu: ['сетки — без погрешности и без условий на $f$. *Лейбницево-точно*',
          'здесь совпадение узлов: конец одного шага и начало следующего — один',
          'и тот же терм, потому что узлы заданы рекурсивной `walk_point` из',
          '§ 5.4, а не формулой $a+ks$ (та же honest-деталь, что разбиралась в',
          'главе о производной). Поэтому соседние слагаемые сокращаются, и от',
          '$f$ не требуется уважать `Qeq`. Само равенство суммы и приращения в',
          'лемме — равенство рациональных чисел `==`.'] },
  // 6. строки 8 и 9: правило произведения и единственность первообразной
  { old: old('поверх grid-FTC. Файл `IntegralApplications.v` содержит правило', 'означает почти-постоянство, § 5.4). Все эти теоремы сверены и'),
    neu: ['поверх grid-FTC. Файл `IntegralApplications.v` содержит правило',
          'произведения для равномерной дифференцируемости (`udiff_product`:',
          'приращение произведения раскладывается на три слагаемых — тождество',
          '`product_decomp`, — и $\\varepsilon$ дробится на три части, как в',
          'правиле произведения производной § 5.4), его интегральную форму',
          '(`ftc_product`), интегрирование по частям',
          '(`integration_by_parts` и его частный случай',
          '`ibp_self`) и единственность первообразной',
          '(`antiderivative_unique_exact`: две функции с одной производной',
          'имеют равные приращения на отрезке; её сеточная предшественница',
          '`antiderivative_unique` даёт близость приращений на уровне сетки —',
          'параллель тому, что нулевая производная означает постоянство,',
          '§ 5.4). Все эти теоремы сверены и'] },
  // 7. строка 4: на каждом уровне — теперь теорема
  { old: old('Интеграл $\\int_0^1 1$ равен $1$ на каждом уровне. Итоговая', 'Интеграл $\\int_0^1 1$ равен $1$ на каждом уровне. Итоговая'),
    neu: ['Интеграл $\\int_0^1 1$ равен $1$ на каждом уровне',
          '(`integral_one_all_levels`). Итоговая'] },
  // 8. строка 3: имена определений ProcessAnalysis.v
  { old: old('Здесь предохранитель C4 особенно важен. Файл `ProcessAnalysis.v`', '`RiemannIntegration.v`, хотя имена совпадают. Это'),
    neu: ['Здесь предохранитель C4 особенно важен. Файл `ProcessAnalysis.v`',
          'содержит *свои* определения: `process_derivative`,',
          '`riemann_sum` и `process_integral`. Имя `riemann_sum`',
          'совпадает с основным из `RiemannIntegration.v`, а определение',
          'другое; `process_derivative` и `process_integral` носят имена,',
          'похожие на основные `deriv_process` (`ProcessDerivative.v`) и',
          '`integral_process` (`ProcessIntegral.v`), и записаны иначе. Для',
          'производной две записи согласованы леммой: их значения совпадают на',
          'каждом уровне (`process_derivative_agrees`). Это'] },
  // 9. строка 10: полные имена
  inline('- оценки сумм (`abs_bound`, `global_bound`);', '(`abs_bound`, `global_bound`)', '(`riemann_sum_abs_bound`, `riemann_sum_global_bound`)'),
  // 10. строка 11: счёт StepIntegral.v
  { old: old('короток и заявляет « 20 Qed, 0 Admitted, 0 axioms ». И ещё один', 'короток и заявляет « 20 Qed, 0 Admitted, 0 axioms ». И ещё один'),
    neu: ['короток и заявляет « 17 Qed, 0 Admitted, 0 axioms ». И ещё один'] },
];
const out = ['@@FILE ' + REL];
for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'шаг-12-глава-V5.txt'), out.join('\n') + '\n');
console.log('описание собрано: правок ' + edits.length);
