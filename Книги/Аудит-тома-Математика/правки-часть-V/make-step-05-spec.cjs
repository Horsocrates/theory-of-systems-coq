// Собирает описание правок шага 5 Части V (теоремы-вывески): по одному месту в главах V.2, V.3, V.5, V.6.
// «Было» берётся со страницы дословно (по первой и последней строке места), «стало» — тексты, показанные автору 12.11.
// Запуск: node make-step-05-spec.cjs  -> шаг-05-теоремы-вывески.txt (формат tools/apply-edits.cjs)
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
    { old: o('Аксиомного основания процессная обёртка не меняет: она ничего не', 'BolzanoWeierstrass)»*.'),
      neu: ['Саму теорему на язык процессов переносит `process_BW`: существует',
            'процесс Коши в $[a,b]$, к каждой далёкой стадии которого сколь угодно',
            'близко подходят члены последовательности со сколь угодно большими',
            'номерами. А `bw_is_process_construction` называет роль каждой стадии:',
            'в интервале между концами лежат члены последовательности со сколь',
            'угодно большими номерами. Аксиомного основания процессная обёртка не',
            'меняет: она стоит на тех же $L3$ и $L4$. Заголовок',
            '`ProcessBW.v` это и фиксирует: *«classic (inherited from',
            'BolzanoWeierstrass)»*.'] },
  ] },
  { rel: DIR + '03 Непрерывность.md', edits: (o) => [
    { old: o('Третий файл — `ProcessEVT.v` (133 строки) — играет ту же', '`evt_convergence_rate` фиксирует темп — $1/2$.'),
      neu: ['Третий файл — `ProcessEVT.v` (158 строк) — играет ту же',
            'роль, что `ProcessIVT.v` для теоремы о промежуточном значении:',
            'тонкая обёртка, переносящая результат на язык процессов',
            '`ProcessCore`. В нём мосты Cauchy-совместимости',
            '(`evt_cauchy_compat`), `sup_process_cauchy` и `process_EVT` — она',
            'несёт всё содержание `EVT_complete`: процесс значений Коши, процесс',
            'точек отрезка, в которых эти значения достигаются, и мажорирующее',
            'свойство; `evt_convergence_rate` фиксирует темп — $1/2$.'] },
  ] },
  { rel: DIR + '05 Интеграл.md', edits: (o) => [
    { old: o('теоремы (§ 5.5). Теорема', 'выдавать одно за другое не следует.'),
      neu: ['теоремы (§ 5.5). Теорема',
            '`integral_is_process_construction` предъявляет процесс сумм как',
            'конструкцию — стадия есть сумма по $n+1$ ячейке, шаг положителен,',
            'ячейки покрывают отрезок в точности, шаг стремится к нулю, — но это',
            '*не* теорема интегрируемости, и выдавать одно за другое не следует.'] },
  ] },
  { rel: DIR + '06 Основная теорема анализа.md', edits: (o) => [
    { old: o('приращением функции; `ftc_error` — её модуль. Теорема', 'как конструкцию (E/R/R-форма).'),
      neu: ['приращением функции; `ftc_error` — её модуль. Теорема',
            '`ftc_is_process_construction` предъявляет этот процесс ошибки',
            'как конструкцию (E/R/R-форма) и собирает доказанное о нём: процесс',
            'сумм есть процесс Коши, а процесс ошибки называет нуль — при условиях',
            'теоремы сходимости, о которой ниже.'] },
  ] },
];
const out = []; let n = 0;
for (const pg of pages) {
  out.push('@@FILE ' + pg.rel);
  for (const e of pg.edits(reader(pg.rel))) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-05-теоремы-вывески.txt'), out.join('\n') + '\n');
console.log('описание собрано: правок ' + n);
