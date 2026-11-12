// Собирает описание правок шага 6 Части V («темпы сходимости»): одно место главы V.2 и два места главы V.3.
// «Было» берётся со страницы дословно (по первой и последней строке места), «стало» — тексты, показанные автору 12.11
// (слово автора: «А — снимаем, вносим три места»).
// Запуск: node make-step-06-spec.cjs  -> шаг-06-темпы-сходимости.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/05 Топология и анализ процессов/';
function reader(rel) {
  const page = fs.readFileSync(LIVE + rel, 'utf8').replace(/\r/g, '').split('\n');
  return function old(first, last) {
    const hits = page.filter((l) => l.startsWith(first)).length;
    const i = page.findIndex((l) => l.startsWith(first));
    if (i < 0 || hits !== 1) throw new Error('начало не найдено однозначно (' + hits + '): ' + first);
    let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
    if (j >= page.length || j - i > 20) throw new Error('конец не найден: ' + last);
    return page.slice(i, j + 1);
  };
}
const pages = [
  { rel: DIR + '02 Топология и компактность.md', edits: (o) => [
    { old: o('картину E/R/R, а `bw_convergence_rate` фиксирует скорость —', '$1/2$: интервал на каждом шаге уполовинивается.'),
      neu: ['картину E/R/R, а `bw_convergence_rate` фиксирует скорость —',
            '$1/2$: интервал на каждом шаге уполовинивается (лемма',
            '`bw_rate_is_width_ratio`).'] },
  ] },
  { rel: DIR + '03 Непрерывность.md', edits: (o) => [
    { old: o('`process_IVT`, а `ivt_convergence_rate` фиксирует', '(175 строк).'),
      neu: ['`process_IVT`, а `ivt_convergence_rate` фиксирует',
            'темп — $1/2$: ширина интервала бисекции на каждом шаге',
            'уполовинивается (лемма `ivt_rate_is_width_ratio`). Всё это —',
            'содержание файла `ProcessIVT.v` (190 строк).'] },
    { old: o('Третий файл — `ProcessEVT.v` (158 строк) — играет ту же', 'свойство; `evt_convergence_rate` фиксирует темп — $1/2$.'),
      neu: ['Третий файл — `ProcessEVT.v` (190 строк) — играет ту же',
            'роль, что `ProcessIVT.v` для теоремы о промежуточном значении:',
            'тонкая обёртка, переносящая результат на язык процессов',
            '`ProcessCore`. В нём мосты Cauchy-совместимости',
            '(`evt_cauchy_compat`), `sup_process_cauchy` и `process_EVT` — она',
            'несёт всё содержание `EVT_complete`: процесс значений Коши, процесс',
            'точек отрезка, в которых эти значения достигаются, и мажорирующее',
            'свойство. Темп называет теорема `evt_lipschitz_rate`: для функции с',
            'константой Липшица $K$ значение на $n$-й сетке отстоит от любого',
            'значения функции на отрезке не больше чем на $K(b-a)/(n+1)$.',
            'Постоянного отношения между стадиями у сетки нет — на каждой стадии',
            'прибавляется одна ячейка; $1/2$ появляется лишь при удвоении числа',
            'ячеек (`evt_step_halves_on_doubling`).'] },
  ] },
];
const out = []; let n = 0;
for (const pg of pages) {
  out.push('@@FILE ' + pg.rel);
  for (const e of pg.edits(reader(pg.rel))) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-06-темпы-сходимости.txt'), out.join('\n') + '\n');
console.log('описание собрано: правок ' + n);
