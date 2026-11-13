// Собирает описание правок шага 5 Части X (глава X.5, строки 1–4 таблицы): шесть мест.
// Запуск: node make-step-05-spec.cjs [A|B]  -> шаг-05-глава-X5.txt (формат tools/apply-edits.cjs)
//   A — заготовки transfinite_rec и omega_tower_induction сняты из TransfiniteInduction.v;
//   B — оставлены, сноска называет их заготовками.
const fs = require('fs');
const path = require('path');
const variant = (process.argv[2] || 'A').toUpperCase();
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL = 'Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/05 Ординалы как процессы; башня сильных аксиом (ATR_0, ^1_1) и её снятие.md';
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
const FN2 = '[^2]: `OrdinalOrders.v`: порядок построения `ord_below` и его фундированность `wf_ord_below`; индукция `structural_transfinite_ind`; рекурсия `ord_rec` с уравнением `ord_rec_eq`; индукция по ступеням башни `tower_induction` и ниже $\\varepsilon_0$ — `induction_below_epsilon_0`; порядок Брауэра `olt` — `wf_olt`, `olt_trans`, `olt_omega_epsilon_0`. **0 аксиом** (сверено `Print Assumptions`). Прежнее отношение `ord_lt` (`Ordinal.v`) тоже фундировано (`wf_ord_lt`, `transfinite_ind` в `TransfiniteInduction.v`), но ниже любой нотации по нему лежат только конечные нотации (`ord_lt_left_numeral`): $\\omega$ по нему не ниже $\\omega+1$ и не ниже $\\varepsilon_0$.'
  + (variant === 'B' ? ' Теоремы `transfinite_rec` и `omega_tower_induction` того же файла — заготовки: в первой нет уравнения рекурсии, вторая есть индукция по $ℕ$.' : '')
  + ' Дополнительно индукция по *уровневой* иерархии — `level_strong_induction` в `TransfiniteInductionLevel.v` (эта работа).';
const edits = [
  // 1. строка 4 таблицы: что актуально на стадии
  { old: old('предел процесса возведения в степень.[^1] На каждой стадии $n$ актуально лишь конечное', 'позиция в фундированном процессе.'),
    neu: ['предел процесса возведения в степень.[^1] На каждой стадии $n$ предъявлена одна нотация:',
          'для $\\omega$ — конечная, $\\mathrm{OSucc}^n(\\mathrm{OZero})$; для $\\varepsilon_0$ — ступень башни,',
          'сама заданная как предел процесса. Сам ординал — не завершённый трансфинитный объект, а',
          'позиция в фундированном процессе.'] },
  // 2. строки 1–3 таблицы: порядок, индукция, рекурсия
  { old: old('Это даёт трансфинитную индукцию и рекурсию *по нотациям* — без аксиом. Отношение', 'вполне-порядку.'),
    neu: ['Это даёт трансфинитную индукцию и рекурсию *по нотациям* — без аксиом. Порядок здесь —',
          'порядок построения: ниже нотации лежат её стадии — предшественник успешника и всякая стадия',
          'предела (`ord_below`). Он фундирован, и по нему идут индукция, в предельном шаге опирающаяся',
          'на все стадии, рекурсия с доказанным уравнением и индукция вплоть до $\\omega$, по ступеням',
          'башни и ниже $\\varepsilon_0$.[^2] Фундирован и порядок сравнения, в котором предел есть',
          'верхняя грань стадий (порядок Брауэра, `olt`): в нём $\\omega<\\omega+1$ и',
          '$\\omega<\\varepsilon_0$. Подчеркнём область: это индукция/рекурсия',
          'по *конструктивным ординальным нотациям* `Ord`, а не по произвольному завершённому',
          'вполне-порядку.'] },
  // 3. строка 4: строка таблицы «Elements»
  inline('| *Elements* (L1${}+{}$P4) | конечная нотация/код/стадия на каждом шаге;',
    'конечная нотация/код/стадия на каждом шаге;',
    'одна нотация, один код, одна стадия на каждом шаге;'),
  // 4. строка 1: «Что даёт»
  { old: old('**Что даёт.** Трансфинитная индукция/рекурсия по нотациям — `wf_ord_lt`,', '`transfinite_ind` (0 аксиом). ATR$_0$/$\\Pi^1_1$/Бесконечность/импредикативность —'),
    neu: ['**Что даёт.** Трансфинитная индукция/рекурсия по нотациям — `wf_ord_below`,',
          '`structural_transfinite_ind`, `ord_rec_eq` (0 аксиом). ATR$_0$/$\\Pi^1_1$/Бесконечность/импредикативность —'] },
  // 5. строка 1: итог
  inline('(`wf_ord_lt`, `transfinite_ind`). Башня сильных аксиом над выбором получила',
    '(`wf_ord_lt`, `transfinite_ind`).',
    '(`wf_ord_below`, `structural_transfinite_ind`).'),
];
// 6. сноска 2
{
  const o2 = old('[^2]: `TransfiniteInduction.v`: `wf_ord_lt`', '[^2]: `TransfiniteInduction.v`: `wf_ord_lt`');
  edits.push({ old: o2, neu: [FN2] });
}
const out = ['@@FILE ' + REL];
for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'шаг-05-глава-X5.txt'), out.join('\n') + '\n');
console.log('описание собрано (вариант ' + variant + '): правок ' + edits.length);
